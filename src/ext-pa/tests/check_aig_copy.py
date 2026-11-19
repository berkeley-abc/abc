"""Run after updating ABC: python3 src/ext-pa/tests/check_aig_copy.py."""
from pathlib import Path
import re
root = Path(__file__).resolve().parents[3]
original = (root / "src/base/abc/abcAig.c").read_text()
copy = (root / "src/ext-pa/paAig.cpp").read_text()
manager = r"struct Abc_Aig_t_\s*\{.*?\n\};"
assert re.search(manager, original, re.S).group() == re.search(manager, copy, re.S).group(), "AIG manager layout changed"
names = ["HashKey2", "AigAndCreateFrom", "AigAndDelete", "AigRemoveFromLevelStructure", "AigRemoveFromLevelStructureR", "AigReplace_int", "AigUpdateLevel_int"]
def function(source, name):
    match = re.search(r"^[\w *]+\b" + name + r"\([^;{}]*\)\s*\{", source, re.M)
    assert match, name
    end, depth = match.end(), 1
    while depth:
        depth += (source[end] == "{") - (source[end] == "}")
        end += 1
    return re.sub(r"^static ", "", source[match.start():end])
for name in names:
    expected = function(original, "Abc_" + name)
    for other in names:
        expected = re.sub(r"\bAbc_" + other + r"\b", "Pa_" + other, expected)
    normalize = lambda text: "\n".join(line.rstrip() for line in text.splitlines())
    assert normalize(expected) == normalize(function(copy, "Pa_" + name)), "Copied helper changed: " + name
print("PA manager layout and seven copied helpers match upstream (ignoring trailing whitespace).")
