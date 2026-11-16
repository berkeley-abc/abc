source $::env(SCRIPTS_DIR)/load.tcl
erase_non_stage_variables place
load_design 3_1_place_gp_skip_io.odb 2_floorplan.sdc
source $::env(DESIGN_HOME)/asap7/$::env(DESIGN_NAME)/pins.tcl
if {![all_pins_placed]} {error "Shared I/O layout incomplete"}
orfs_write_db $::env(RESULTS_DIR)/3_2_place_iop.odb
write_pin_placement $::env(RESULTS_DIR)/3_2_place_iop.tcl
