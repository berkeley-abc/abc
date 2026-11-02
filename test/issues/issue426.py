#!/usr/bin/env python3
"""Exercise bidec's node-budget fallback and successful decomposition."""
import os
from pathlib import Path
import random
import resource
import subprocess
import tempfile

abc = str(Path(os.environ.get("ABC", "./abc")).resolve())
resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
with tempfile.TemporaryDirectory() as tmp:
    work = Path(tmp)
    for size in (4, 14):
        rng = random.Random(426)
        truth = rng.getrandbits(1 << size)
        names = [f"x{i}" for i in range(size)]
        (work / "input.bench").write_text(
            "".join(f"INPUT({name})\n" for name in names)
            + "OUTPUT(y)\n"
            + f"y = LUT 0x{truth:0{(1 << size) // 4}x} ({', '.join(names)})\n"
        )
        script = (
            "read_bench input.bench; strash; write_aiger reference.aig; "
            "read_bench input.bench; aig; bidec; strash; &get; &cec reference.aig"
        )
        result = subprocess.run([abc, "-s", "-c", script], cwd=work,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                text=True, timeout=60)
        if result.returncode or "Networks are equivalent" not in result.stdout:
            raise SystemExit(f"K={size}:\n{result.stdout}")
print("PASS: Issue #426")
