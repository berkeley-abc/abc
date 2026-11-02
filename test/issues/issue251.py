#!/usr/bin/env python3
"""Check exported CEX states after restoring don't-care initialization."""
import os
from pathlib import Path
import subprocess
import tempfile

abc = str(Path(os.environ.get("ABC", "./abc")).resolve())
with tempfile.TemporaryDirectory() as tmp:
    work = Path(tmp)
    for initial in ((None,) * 4, (None, 1, None, 0), (0, None, 1, None),
                    (1, 0, 0, 1), (0, 1, 1, 0)):
        # Four swapping registers and q0 XOR q2, with a dummy PI for BMC.
        lines = ["aig 9 1 4 1 4"]
        for i, (fanin, init) in enumerate(zip((6, 4, 10, 8), initial)):
            lines.append(f"{fanin} {2 * (i + 2) if init is None else init}")
        lines.append("18")
        data = ("\n".join(lines) + "\n").encode() + bytes((3, 4, 6, 4, 1, 2, 2, 15))
        (work / "test.aig").write_bytes(data)
        command = ("read test.aig; logic; undc; strash; zero; bmc; cexsave; "
                   "read test.aig; cexload; undc -c; testcex -a; "
                   "write_cex -a aiger.cex; write_cex plain.cex; write_cex -n named.cex")
        result = subprocess.run([abc, "-s", "-c", command], cwd=work,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                text=True, timeout=30)
        assert result.returncode == 0, (initial, result.returncode, result.stdout)
        assert "The cex is correct" in result.stdout, result.stdout
        aiger = (work / "aiger.cex").read_text().splitlines()
        state = aiger[0]
        assert len(state) == 4 and set(state) <= {"0", "1"}, state
        for bit, init in zip(state, initial):
            assert init is None or bit == str(init), (initial, state)
        # The frame-zero witness must violate the XOR property.
        assert state[0] != state[2], (initial, state)
        plain = (work / "plain.cex").read_text().split("#", 1)[0].strip()
        assert plain == state + aiger[1], repr(plain)
        named = [line.rsplit("=", 1)[1] for line in
                 (work / "named.cex").read_text().splitlines() if "@0=" in line]
        assert "".join(named) == plain, named
print("PASS: Issue #251 (plain, AIGER, and named CEX; mixed initialization)")
