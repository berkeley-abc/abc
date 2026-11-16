# Mapping-only ORFS handoff. See LICENSE.orfs for the upstream script license.
proc get_module_names { file_path } {
  set module_list [list]
  if { [catch { set fid [open $file_path r] } err] } {
    error "Failed to open file $file_path: $err"
  }
  set regex {^[ \t]*module[ \t]+([A-Za-z_$][A-Za-z0-9_$]*)}
  while { [gets $fid line] >= 0 } {
    if { [regexp -nocase $regex $line match_all module_name] } {
      lappend module_list $module_name
    }
  }
  close $fid
  return $module_list
}

proc get_dfflegalize_args { file_path } {
  set legalize_args [list]
  set module_names [get_module_names $file_path]
  foreach module_name $module_names {
    lappend legalize_args -cell $module_name x
  }
  return $legalize_args
}

source $::env(SCRIPTS_DIR)/synth_preamble.tcl
read_checkpoint $::env(RESULTS_DIR)/1_1_yosys_canonicalize.rtlil

hierarchy -check -top $::env(DESIGN_NAME)

if { $::env(SYNTH_GUT) } {
  delete $::env(DESIGN_NAME)/c:*
}

set lib_args [list]
foreach lib $::env(LIB_FILES) {
  lappend lib_args -liberty $lib
}

set lib_dont_use_args [list]
if { [env_var_exists_and_non_empty DONT_USE_CELLS] } {
  foreach cell $::env(DONT_USE_CELLS) {
    lappend lib_dont_use_args -dont_use $cell
  }
}

yosys proc

flatten

memory

techmap

if { [env_var_exists_and_non_empty DFF_LIB_FILE] } {
  dfflibmap -liberty $::env(DFF_LIB_FILE) {*}$lib_dont_use_args
} elseif { [env_var_exists_and_non_empty DFF_MAP_FILE] } {
  set legalize_args [get_dfflegalize_args $::env(DFF_MAP_FILE)]
  dfflegalize {*}$legalize_args
  techmap -map $::env(DFF_MAP_FILE)
} else {
  dfflibmap {*}$lib_args {*}$lib_dont_use_args
}

opt_clean

setundef -zero

if {
  ![env_var_exists_and_non_empty SYNTH_WRAPPED_OPERATORS] &&
  ![env_var_exists_and_non_empty SWAP_ARITH_OPERATORS]
} {
  log_cmd abc {*}$abc_args
} else {
  scratchpad -set abc9.script $::env(SCRIPTS_DIR)/abc_speed_gia_only.script
  set abc_args [lrange $abc_args 2 end]
  log_cmd abc_new {*}$abc_args
  delete {t:$specify*}
}

splitnets

opt_clean -purge

hilomap -singleton \
  -hicell {*}$::env(TIEHI_CELL_AND_PORT) \
  -locell {*}$::env(TIELO_CELL_AND_PORT)

insbuf -buf {*}$::env(MIN_BUF_CELL_AND_PORTS)

tee -o $::env(REPORTS_DIR)/synth_check.txt check

tee -o $::env(REPORTS_DIR)/synth_stat.txt stat {*}$lib_args

if {
  ![env_var_exists_and_non_empty SYNTH_WRAPPED_OPERATORS] &&
  ![env_var_exists_and_non_empty SWAP_ARITH_OPERATORS]
} {
  check -assert -mapped
} else {
  check -assert
}

write_verilog -nohex -nodec $::env(RESULTS_DIR)/1_2_yosys.v

log_cmd exec cp $::env(SDC_FILE) $::env(RESULTS_DIR)/1_synth.sdc
