read_db $::env(ODB_PATH)
set block [ord::get_db_block]
set units [$block getDbUnitsPerMicron]
set sum 0.0
set count 0
foreach net [$block getNets] {
  set kind [$net getSigType]
  if {$kind eq "POWER" || $kind eq "GROUND"} {continue}
  set rect [$net getTermBBox]
  set dx [expr {[$rect xMax] - [$rect xMin]}]
  set dy [expr {[$rect yMax] - [$rect yMin]}]
  if {$dx < 0 || $dy < 0} {continue}
  set sum [expr {$sum + ($dx + $dy) / double($units)}]
  incr count
}
puts "AUDIT_STAGE $::env(STAGE) HPWL_UM $sum NETS $count DBU_PER_UM $units"

set b [ord::get_db_block]
set d [$b getDieArea]
set c [$b getCoreArea]
puts "PAPER_BOX [$d xMin] [$d yMin] [$d xMax] [$d yMax] [$c xMin] [$c yMin] [$c xMax] [$c yMax]"
set records {}
foreach port [$b getBTerms] {
  if {[$port getSigType] in {POWER GROUND}} {continue}
  foreach pin [$port getBPins] {
    foreach box [$pin getBoxes] {
      lappend records [list [$port getName] [[$box getTechLayer] getName] [$box xMin] [$box yMin] [$box xMax] [$box yMax]]
    }
  }
}
foreach row [lsort $records] {puts "PAPER_PIN $row"}
