# Recompute timing from saved artifacts, without optimizing the design.
source $::env(SCM_CONFIG)
set_thread_count 1
sta::set_thread_count 1
suppress_message STA 1212
foreach lib $liberties { read_liberty $lib }
read_db routed.odb
if {$::env(SCM_REPLAY_MODE) eq "recorded"} {
    set exact_period [sta::time_sta_ui [expr {$period_ps*1e-12}]]
    create_clock -name VCLK -period $exact_period
    set_input_delay 0 -clock VCLK [all_inputs]
    set_output_delay 0 -clock VCLK [all_outputs]
    set_driving_cell -lib_cell $driver [all_inputs]
    set output_load [expr {4.0*[get_property [get_lib_pins */$driver/A] capacitance]}]
    set_load $output_load [all_outputs]
    write_sdc -digits 12 routed_exact.sdc
} elseif {$::env(SCM_REPLAY_MODE) eq "precise"} {
    read_sdc routed_exact.sdc
} else {
    read_sdc routed.sdc
}
read_spef routed.spef
report_parasitic_annotation -report_unannotated
foreach pin [get_pins -hierarchical *] {
    if {[get_property $pin direction] ne "output" || [$pin net] ne "NULL"} {continue}
    set port [$pin liberty_port]
    set dbpin [sta::sta_to_db_pin $pin]
    if {$port ne "NULL" && [$port function] ne "NULL" && $dbpin ne "NULL" && [$dbpin getNet] eq "NULL"} {
        if {[$port function] in {0 1}} {
            puts "SCM_DISCONNECTED_CONSTANT [get_property $pin full_name]"
        } else {
            puts "SCM_DISCONNECTED_OUTPUT [get_property $pin full_name]"
        }
    }
}
set clock [get_clocks VCLK]
if {[llength $clock] != 1} {error "Expected the frozen virtual clock"}
set period [get_property $clock period]
set delay_ps [expr {1e12*[sta::time_ui_sta [expr {$period-[sta::worst_slack -max]}]]}]
set actual_period [expr {1e12*[sta::time_ui_sta $period]}]
puts "SCM_REPLAY period_ps=$actual_period delay_ps=$delay_ps"
foreach type {slew capacitance fanout} {
    if {[catch {sta::max_${type}_check_slack_limit} value]} {
        puts "SCM_ELECTRICAL type=$type normalized_slack=unavailable"
        puts "SCM_ELECTRICAL_NOTE $value"
    } else {
        puts "SCM_ELECTRICAL type=$type normalized_slack=$value"
    }
}
report_check_types -max_slew -max_capacitance -max_fanout -violators -digits 6
puts SCM_REPLAY_DONE
