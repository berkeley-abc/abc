#!/usr/bin/env python3
"""Check exact synthesis, cached mapping, polarity, and truth-table sizes."""
import os
from pathlib import Path
import subprocess
import tempfile

abc = str(Path(os.environ.get("ABC", "./abc")).resolve())


def blif(path, size, truths, times):
    names = [f"x{i}" for i in range(size)]
    lines = [".model truth", ".inputs " + " ".join(names),
             ".outputs " + " ".join(f"y{i}" for i in range(len(truths)))]
    lines += [f".input_arrival {name} {t} {t}" for name, t in zip(names, times)]
    for index, truth in enumerate(truths):
        if truth in (0, (1 << (1 << size)) - 1):
            lines.append(f".names y{index}")
            if truth:
                lines.append("1")
            continue
        lines.append(".names " + " ".join(names) + f" y{index}")
        for mint in range(1 << size):
            if truth >> mint & 1:
                lines.append("".join(str(mint >> i & 1) for i in range(size)) + " 1")
    path.write_text("\n".join(lines + [".end", ""]))


with tempfile.TemporaryDirectory() as tmp:
    work = Path(tmp)
    cases = []
    # All 256 three-input functions, with uniform and nonuniform arrival times.
    for times in ((0, 0, 0), (0, 1, 2)):
        cases.append((3, list(range(256)), times))
    for size in range(4, 9):
        mask = (1 << (1 << size)) - 1
        parity = sum((bin(i).count("1") % 2) << i for i in range(1 << size))
        cases.append((size, [1, mask ^ 1, parity, mask ^ parity], range(size)))
    for index, (size, truths, times) in enumerate(cases):
        blif(work / f"case{index}.blif", size, truths, times)

    for aig in (False, True):
        commands = ["bms_start" + (" -a" if aig else "")]
        checks = 0
        for index, (size, _, _) in enumerate(cases):
            read = f"read_blif -n case{index}.blif"
            commands += [read, "strash", "write_aiger reference.aig"]
            # Reuse the same BMS cache; also test reconstruction from choices.
            for choices in (False, True):
                commands += [read, "strash"]
                if choices:
                    commands += ["dch"]
                commands += [f"if -u -K {max(4, size)}", "strash", "&get",
                             "&cec reference.aig"]
                checks += 1
        commands += ["bms_stop"]
        (work / "mapping.abc").write_text("\n".join(commands) + "\n")
        result = subprocess.run([abc, "-s", "-f", "mapping.abc"], cwd=work,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                text=True, timeout=180)
        if (result.returncode or "NOT EQUIVALENT" in result.stdout or
                result.stdout.count("Networks are equivalent") != checks):
            raise SystemExit(result.stdout)

    # Standalone extraction has a separate SOP decoder and a four-word stride
    # between output specifications, even for truth tables smaller than 8 inputs.
    for truths in ([2], [4], [0x96, 0xE8], [0x69, 0x17]):
        size = 2 if len(truths) == 1 else 3
        blif(work / "exact.blif", size, truths, range(size))
        for aig in (False, True):
            command = "read_blif exact.blif; strash; write_aiger reference.aig; "
            command += "exact -D 6 " + ("-a " if aig else "")
            command += " ".join(f"{truth:0{(1 << size) // 4}x}" for truth in truths)
            command += "; " + ("" if aig else "strash; &get; ") + "&cec reference.aig"
            result = subprocess.run([abc, "-s", "-c", command], cwd=work,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                    text=True, timeout=60)
            if result.returncode or "Networks are equivalent" not in result.stdout:
                raise SystemExit(result.stdout)
print("PASS: Issue #408 (36 equivalence checks)")
