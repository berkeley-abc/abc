# SPDX-License-Identifier: BSD-3-Clause
# Copyright (c) 2019-2026, The OpenROAD Authors
# Adapted from OpenROAD test/flow.tcl for matched combinational evaluation.
source $::env(SCM_CONFIG)
set_thread_count $threads
sta::set_thread_count 1
suppress_message STA 1212
source $or_test/$vars_file
if {$library eq "asap7"} {
    set std_cell_lef asap7/asap7sc7p5t_28_R_1x_220121a.lef
}
foreach lib $liberties { read_liberty $lib }

proc matches {name patterns} {
    foreach pattern $patterns { if {[string match $pattern $name]} { return 1 } }
    return 0
}
proc ports {file} {
    set out [open $file w]
    set entries {}
    foreach port [[ord::get_db_block] getBTerms] {
        if {[$port getSigType] in {POWER GROUND}} {continue}
        lappend entries "[$port getName]\t[$port getIoType]"
    }
    puts $out [join [lsort $entries] \n]
    close $out
}
if {$mode eq "export"} {
    # Reloading refreshes supply-port types before logical Verilog export.
    read_db routed.odb
    ports ports_routed.tsv
    write_verilog -remove_cells $physical_only logic.v
    puts SCM_EXPORT_DONE
    exit
}

read_lef $or_test/$tech_lef
read_lef $or_test/$std_cell_lef
read_verilog $netlist
link_design [string map [list / "\\/"] $top]
# Materialize Verilog literals as library tie cells before placement and PDN.
proc scm_map_constants {} {
    global tielo_port tiehi_port
    set block [ord::get_db_block]
    set count 0
    foreach net [$block getNets] {
        set type [$net getSigType]
        if {$type ni {POWER GROUND}} {continue}
        set value [expr {$type eq "POWER"}]
        set port [expr {$value ? $tiehi_port : $tielo_port}]
        set lib_pins [get_lib_pins */$port]
        if {[llength $lib_pins] != 1} {error "Expected one tie output: $port"}
        set lib_pin [lindex $lib_pins 0]
        if {[$lib_pin function] ne "$value"} {error "Wrong constant function on $port"}
        foreach pin [$net getITerms] {
            if {[$pin getSigType] ne "SIGNAL" || [$pin getIoType] ne "INPUT"} {
                error "Refusing to convert a driven or supply-connected net: [$net getName]"
            }
        }
        foreach pin [$net getBTerms] {
            if {[$pin getIoType] ne "OUTPUT"} {
                error "Refusing to convert an external supply: [$net getName]"
            }
        }
        set master_name [join [lrange [split $port /] 0 end-1] /]
        set pin_name [lindex [split $port /] end]
        set master [[ord::get_db] findMaster $master_name]
        if {$master eq "NULL"} {error "Missing tie master: $master_name"}
        set name "__scmap_constant_[$net getId]"
        if {[$block findInst $name] ne "NULL"} {error "Tie instance already exists: $name"}
        set inst [odb::dbInst_create $block $master $name]
        set pin [$inst findITerm $pin_name]
        if {$pin eq "NULL"} {error "Missing tie output: $port"}
        $net setSigType SIGNAL
        foreach term [$net getBTerms] {$term setSigType SIGNAL}
        $pin connect $net
        incr count
    }
    puts "SCM_CONSTANT_TIES count=$count"
}
scm_map_constants

ports ports_initial.tsv
set period [sta::time_sta_ui [expr {$period_ps*1e-12}]]
create_clock -name VCLK -period $period
set_input_delay 0 -clock VCLK [all_inputs]
set_output_delay 0 -clock VCLK [all_outputs]
set_driving_cell -lib_cell $driver [all_inputs]
set drive_pin [get_lib_pins */$driver/A]
if {[llength $drive_pin] != 1} {error "Expected one driver input pin"}
set output_load [expr {4.0*[get_property $drive_pin capacitance]}]
set load_ff [expr {1e15*[sta::capacitance_ui_sta $output_load]}]
if {$load_ff < 0.1 || $load_ff > 1000} {error "Unexpected output-load units: $load_ff fF"}
set_load $output_load [all_outputs]
set_dont_use $dont_use
puts "SCM_BOUNDARY period_ps=$period_ps driver=$driver load_ff=$load_ff"
report_units

proc snapshot {stage} {
    global period area_exclude buffer_patterns
    set slack [sta::worst_slack -max]
    if {abs($slack) > 1e12} {error "No finite constrained paths"}
    set block [ord::get_db_block]
    set dbu [$block getDbUnitsPerMicron]
    set area 0.0
    set excluded 0.0
    set buffers 0
    set buffer_area 0.0
    set out [open cells_$stage.tsv w]
    puts $out "instance\tmaster\tarea\texcluded\tbuffer"
    foreach inst [$block getInsts] {
        set master [$inst getMaster]
        set name [$master getName]
        set value [expr {double([$master getWidth])*[$master getHeight]/($dbu*$dbu)}]
        set skip [matches $name $area_exclude]
        set buffer [matches $name $buffer_patterns]
        if {$skip} {
            set excluded [expr {$excluded+$value}]
        } else {
            set area [expr {$area+$value}]
            if {$buffer} {incr buffers; set buffer_area [expr {$buffer_area+$value}]}
        }
        puts $out "[$inst getName]\t$name\t$value\t$skip\t$buffer"
    }
    close $out
    set delay_ps [expr {1e12*[sta::time_ui_sta [expr {$period-$slack}]]}]
    set slack_ps [expr {1e12*[sta::time_ui_sta $slack]}]
    puts "SCM_PHYSICAL stage=$stage area=$area delay_ps=$delay_ps slack_ps=$slack_ps excluded_area=$excluded buffers=$buffers buffer_area=$buffer_area"
    report_worst_slack -max -digits 6
    report_tns -digits 6
    report_check_types -max_slew -max_capacitance -max_fanout -violators -digits 6
}

snapshot synthesis
initialize_floorplan -site $site -die_area $die -core_area $core
source $or_test/$tracks_file
remove_buffers
eval tapcell $tapcell_args
source $or_test/$pdn_cfg
pdngen
foreach adjustment $global_routing_layer_adjustments {
    lassign $adjustment layers factor
    set_global_routing_layer_adjustment $layers $factor
}
set_routing_layers -signal $global_routing_layers -clock $global_routing_clock_layers
if {$mode eq "calibration"} {
    global_placement -density 0.30 -pad_left $global_place_pad -pad_right $global_place_pad -skip_io
    place_pins -hor_layers $io_placer_hor_layer -ver_layers $io_placer_ver_layer
    write_pin_placement $pins
} else {
    source $pins
}
global_placement -routability_driven -density 0.30 -pad_left $global_place_pad -pad_right $global_place_pad
source $or_test/$layer_rc_file
set_wire_rc -signal -layer $wire_rc_layer
set_wire_rc -clock -layer $wire_rc_layer_clk
estimate_parasitics -placement
repair_design -slew_margin 0 -cap_margin 0
repair_tie_fanout -separation $tie_separation $tielo_port
repair_tie_fanout -separation $tie_separation $tiehi_port
set_placement_padding -global -left $detail_place_pad -right $detail_place_pad
detailed_placement
estimate_parasitics -placement
snapshot placed
repair_timing -setup
detailed_placement
estimate_parasitics -placement
snapshot repaired
pin_access
global_route -guide_file route.guide -congestion_iterations 100
estimate_parasitics -global_routing
snapshot global_route
global_route -start_incremental
repair_timing -setup
detailed_placement
global_route -end_incremental
estimate_parasitics -global_routing
snapshot global_repaired
global_route -start_incremental
repair_timing -recover_power 100
detailed_placement
global_route -end_incremental
estimate_parasitics -global_routing
snapshot recovered
global_route -start_incremental
repair_design -slew_margin 20 -cap_margin 20
detailed_placement
global_route -end_incremental
estimate_parasitics -global_routing
snapshot electrical_repaired
repair_antennas -iterations 5
check_antennas
detailed_route -output_drc route_drc.rpt -output_maze maze.log -or_seed $seed -verbose 0
set iterations 0
while {[check_antennas] && $iterations < 5} {
    repair_antennas
    detailed_route -output_drc route_drc.rpt -output_maze maze.log -or_seed $seed -verbose 0
    incr iterations
}
# Diagnostic fallback, reached only after the original five repairs fail.
if {[check_antennas]} {
    check_antennas -verbose -report_file antenna_before_retry.rpt
    write_db antenna_before_retry.odb
    foreach margin {20 50} {
        for {set attempt 0} {$attempt < 3 && [check_antennas]} {incr attempt} {
            puts "SCM_ANTENNA_RETRY margin=$margin attempt=$attempt"
            repair_antennas -ratio_margin $margin -iterations 5
            detailed_route -output_drc route_drc.rpt -output_maze maze.log -or_seed $seed -verbose 0
        }
        if {![check_antennas]} {break}
    }
    check_antennas -verbose -report_file antenna_after_retry.rpt
    write_db antenna_after_retry.odb
}

set drvs [detailed_route_num_drvs]
set antennas [ant::antenna_violation_count]
set routed [design_is_routed]
puts "SCM_ROUTE routed=$routed drvs=$drvs antennas=$antennas"
if {!$routed || $drvs != 0 || $antennas != 0} {error "Physical validity check failed"}
snapshot before_fill
filler_placement $filler_cells
check_placement -verbose
define_process_corner -ext_model_index 0 X
extract_parasitics -ext_model_file $or_test/$rcx_rules_file
write_spef routed.spef
read_spef routed.spef
snapshot extracted
report_checks -path_delay max -format full_clock_expanded -fields {input_pin slew capacitance} -digits 6
report_floating_nets -verbose
write_db routed.odb
write_sdc -digits 12 routed.sdc
puts SCM_PHYSICAL_DONE
