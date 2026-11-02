#!/usr/bin/env python3
"""Nonzero initialization does not turn ordinary outputs into properties."""
import bz2, gzip, os, subprocess, tempfile
from pathlib import Path
abc = str(Path(os.environ.get("ABC", "./abc")).resolve())
with tempfile.TemporaryDirectory() as tmp:
    p = Path(tmp)
    for init in [0, 1, 2]:
        for constrained in [False, True]:
            header = "aig 1 0 1 0 0 1 1" if constrained else "aig 1 0 1 1 0"
            latch = "3" if init == 0 else f"3 {init}"
            (p/"input.aig").write_text(header + "\n" + latch + "\n2\n" + ("1\n" if constrained else "") + "c\nfixture\n")
            for ext, decode in [("aig", lambda x:x), ("aig.gz", gzip.decompress), ("aig.bz2", bz2.decompress)]:
                r = subprocess.run([abc, "-s", "-c", f"read_aiger input.aig; write_aiger -s output.{ext}"], cwd=p, capture_output=True, text=True)
                assert r.returncode == 0, r.stdout + r.stderr
                lines = decode((p/f"output.{ext}").read_bytes()).splitlines()
                assert lines, (init, constrained, ext, r.stdout, r.stderr)
                assert lines[0].decode() == header, lines[:4]
                assert lines[1].decode() == latch, lines[:4]
                assert lines[2] == b"2", lines[:4]
                if constrained: assert lines[3] == b"1", lines[:4]
print("PASS: Issue #47 (18 metadata and initialization checks)")
