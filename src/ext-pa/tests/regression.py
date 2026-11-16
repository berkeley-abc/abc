"""Sequential PA correctness checks; no external benchmarks are required.

python3 src/ext-pa/tests/regression.py --abc build-cmake/abc [--lib path.lib]
Add --audit for an executable compiled with ABC_PA_ENABLE_AUDIT. Timings from this test
are not performance measurements. Each optimized network is checked by CEC.
"""
import argparse
import json
import math
import os
from pathlib import Path
import random
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]


def network(path, seed):
    """Shared, reconvergent logic with a high-fanout driver and complemented edges."""
    rng = random.Random(seed)
    pins = [f"x{i}" for i in range(12)]
    nodes = pins[:]
    text = [".model pa_test", ".inputs " + " ".join(pins)]
    outputs = []
    for i in range(100):
        a, b = rng.sample(nodes, 2)
        if i > 3 and i % 3 == 0:
            a = "n0"
            if b == a:
                b = pins[0]
        out = f"n{i}"
        pattern = rng.choice(["11", "10", "01", "00"])
        text.extend([f".names {a} {b} {out}", f"{pattern} 1"])
        nodes.append(out)
        if i >= 75:
            outputs.append(out)
    text.insert(2, ".outputs " + " ".join(outputs))
    path.write_text("\n".join(text + [".end", ""]))


def run(binary, command, directory, label, env, expected=None):
    script = directory / (label + ".abc")
    script.write_text(f'source -s "{ROOT / "abc.rc"}"; {command}\n')
    result = subprocess.run([str(binary), "-s", "-f", str(script)], cwd=directory,
                            env=env, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=180)
    text = result.stdout
    (directory / (label + ".log")).write_text(text)
    if expected is not None:
        assert result.returncode >= 0, (label, result.returncode, text[-2000:])
        assert expected in text, (label, text[-2000:])
        return text
    assert result.returncode == 0, (label, result.returncode, text[-2000:])
    assert not re.search(r"(?i)(placement error|audit failed|maximum mismatch|"
                         r"has failed|original network (?:is )?restored|"
                         r"unknown command|AddressSanitizer:|Assertion failed)", text), (label, text[-2000:])
    for count in re.findall(r"roots checked, (\d+) used stale", text):
        assert int(count) == 0, label
    for count in re.findall(r"truth audit: (\d+) mismatches", text):
        assert int(count) == 0, label
    if env.get("ABC_PA_CANDIDATE_AUDIT") is not None:
        expected_audits = len(re.findall(r"(?:^|;)\s*pa_rs\b", command))
        actual_audits = len(re.findall(r"PA resub truth audit: 0 mismatches\.", text))
        assert actual_audits == expected_audits, (label, "missing resub truth audit", text[-2000:])
    for nodes, assigned, total in re.findall(r"pa_stats: nodes = (\d+)\s+coordinates = (\d+)/(\d+)", text):
        assert nodes == assigned == total, label
    for hpwl, overflow in re.findall(r"pa_stats: HPWL \S+ -> (\S+)\s+overflow \S+ -> (\S+)", text):
        assert all(math.isfinite(float(value)) for value in (hpwl, overflow)), label
    return text


def aig_network(path):
    """Read binary AIGER structure, excluding symbols and ABC's name/date comment."""
    data = path.read_bytes()
    end = data.index(b"\n") + 1
    header = data[:end].split()
    assert len(header) == 6 and header[0] == b"aig", path
    _, _, _, latches, outputs, ands = header
    for _ in range(int(latches) + int(outputs)):
        end = data.index(b"\n", end) + 1
    for _ in range(2 * int(ands)):
        while data[end] & 128:
            end += 1
        end += 1
    return data[:end]


def edge_cases(binary, directory, env, library):
    passed = []
    fixtures = {
        "constant": ".model constant\n.inputs a b\n.outputs z\n.names a b x\n11 1\n"
                    ".names a b y\n10 1\n.names x y z\n11 1\n.end\n",
        "wire": ".model wire\n.inputs a b\n.outputs z\n.names a b x\n11 1\n"
                ".names a b y\n10 1\n.names x y z\n1- 1\n-1 1\n.end\n",
        "buffer": ".model buffer\n.inputs a\n.outputs z\n.names a z\n1 1\n.end\n",
    }
    empty_sources = {}
    for name, blif in fixtures.items():
        source = directory / (name + ".blif")
        source.write_text(blif)
        original = directory / (name + ".aig")
        run(binary, f'read_blif "{source}"; strash; write_aiger "{original}"',
            directory, name + "_prepare", env)
        empty_sources[name] = original
        variants = {} if name == "buffer" else {
            "refactor": "pa_place; pa_rf",
            "resub": "pa_place; pa_rs -N 2",
            "bounded": "pa_place; pa_rf -t -S 2 -E 0",
            "strict": "pa_place; pa_rs -t -S 2 -N 2",
        }
        if library:
            variants["mapped"] = f'read_lib "{library}"; &get; &nf; &put; pa_place; pa_strash'
        for mode, flow in variants.items():
            label = f"empty_{name}_{mode}"
            target = directory / (label + ".aig")
            text = run(binary, f'read "{original}"; strash; {flow}; pa_stats; '
                       'pa_rw -t -S 2 -E 0; pa_rf -t -S 2 -E 0; pa_rs -t -S 2 -N 2; '
                       f'pa_stats; write_aiger "{target}"; cec "{original}" "{target}"',
                       directory, label, env)
            assert text.count("pa_stats: nodes = 0  coordinates = 0/0") == 2, (label, text)
            assert "Networks are equivalent" in text, (label, text[-2000:])
            passed.append(label)

    original = directory / "input7.aig"
    variants = ["", "-a", "-t -S 2 -E 0", "-t -S 2 -a", "-T"]
    for i, flags in enumerate(variants):
        label = f"refactor_min_saved_{i}"
        target = directory / (label + ".aig")
        run(binary, f'read "{original}"; strash; pa_place; pa_rf -M 1000000 {flags}; '
            f'pa_stats; write_aiger "{target}"', directory, label, env)
        assert aig_network(original) == aig_network(target), label
        passed.append(label)
    original = empty_sources["constant"]
    for minimum, flags, expected_nodes in [(4, "", 3), (3, "", 0), (4, "-a", 3), (4, "-z", 0)]:
        label = f"constant_min_saved_{minimum}{flags.replace('-', '_')}"
        target = directory / (label + ".aig")
        text = run(binary, f'read "{original}"; strash; pa_place; pa_rf -M {minimum} {flags}; '
                   f'pa_stats; write_aiger "{target}"; cec "{original}" "{target}"',
                   directory, label, env)
        assert f"pa_stats: nodes = {expected_nodes} " in text, (label, text)
        assert "Networks are equivalent" in text, label
        passed.append(label)
    original = directory / "input7.aig"
    outputs = []
    for i, flags in enumerate(["", "-M 0", "-z"]):
        label = f"refactor_zero_default_{i}"
        target = directory / (label + ".aig")
        text = run(binary, f'read "{original}"; strash; pa_place; pa_rf {flags}; '
                   f'pa_stats; write_aiger "{target}"; cec "{original}" "{target}"',
                   directory, label, env)
        assert "Networks are equivalent" in text, label
        outputs.append(aig_network(target))
        passed.append(label)
    assert outputs[0] == outputs[1] == outputs[2], "refactor zero-gain default changed"

    # A mapped netlist can contain real nodes while every library area is zero.
    genlib = directory / "zero_area.genlib"
    genlib.write_text("GATE ZERO 0 Y=CONST0;\nGATE ONE 0 Y=CONST1;\n"
                     "GATE BUF 0 Y=A; PIN * NONINV 1 999 1 0 1 0\n"
                     "GATE INV 0 Y=!A; PIN * INV 1 999 1 0 1 0\n"
                     "GATE NAND2 0 Y=!(A*B); PIN * INV 1 999 1 0 1 0\n"
                     "GATE NOR2 0 Y=!(A+B); PIN * INV 1 999 1 0 1 0\n"
                     "GATE AND2 0 Y=A*B; PIN * NONINV 1 999 1 0 1 0\n")
    mapped = directory / "zero_area.blif"
    mapped.write_text(".model zero_area\n.inputs a b\n.outputs z\n"
                      ".gate NAND2 A=a B=b Y=x\n.gate INV A=x Y=z\n.end\n")
    original = directory / "zero_area_original.aig"
    target = directory / "zero_area.aig"
    run(binary, f'read_genlib "{genlib}"; read_blif "{mapped}"; strash; write_aiger "{original}"',
        directory, "zero_area_prepare", env)
    text = run(binary, f'read_genlib "{genlib}"; read_blif "{mapped}"; pa_place; pa_stats; '
               f'pa_strash; pa_rf; pa_stats; write_aiger "{target}"; cec "{original}" "{target}"',
               directory, "zero_area", env)
    assert "cell area = 0.000" in text and "canvas = 1.000 x 1.000" in text, text
    assert "Networks are equivalent" in text, text
    passed.append("zero_area")
    return passed


def timing_seed_cases(binary, directory, env, audit):
    """Exercise the shared timing evaluator through RW, RF and RS separately.

    Each exact-mode fixture exposes a pre-fix score or boundary-arrival error.
    RF's boundary error can be masked by the final score, so both are checked.
    Full-cone modes and a mixed sequence also check command-state transitions.
    """
    local_env = dict(env)
    if audit:
        local_env["ABC_PA_TIMING_SEED_AUDIT"] = "1"
    cases = []
    for operator, seed in [("rw", 26), ("rf", 23), ("rs", 12)]:
        extra = "-N 2 " if operator == "rs" else ""
        for mode, flags in [("exact", "-t -S 2"), ("full", "-T")]:
            cases.append((f"{operator}_{mode}", seed, f"pa_{operator} {extra}{flags};"))
    cases.append(("mixed", 12, "pa_rs -N 2 -t -S 2; pa_rw -t -S 2; pa_rf -t -S 2;"))
    passed = []
    for name, seed, flow in cases:
        label = "timing_seed_" + name
        source = directory / (label + ".blif")
        original = directory / (label + "_input.aig")
        target = directory / (label + "_output.aig")
        network(source, seed)
        text = run(binary, f'read_blif "{source}"; strash; write_aiger "{original}"; '
                   f'pa_place; {flow} {flow} write_aiger "{target}"; '
                   f'cec "{original}" "{target}"', directory, label, local_env)
        assert "Networks are equivalent" in text, (label, text[-2000:])
        if audit:
            checks = re.findall(r"PA timing seed audit: (\d+) candidates checked", text)
            assert checks and sum(map(int, checks)) > 0, (label, "timing seed audit not exercised")
        passed.append(label)
    return passed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--abc", type=Path, required=True)
    parser.add_argument("--lib", type=Path)
    parser.add_argument("--audit", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    binary = args.abc.resolve()
    directory = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix="abc-pa-test-"))
    directory.mkdir(parents=True, exist_ok=True)
    env = {k: v for k, v in os.environ.items() if not k.startswith("ABC_PA_")}
    if args.audit:
        for key in ["CANDIDATE", "SCREEN", "FACTOR_CACHE", "PLACEMENT", "TIMING", "REQUIRED", "REVERSE"]:
            env["ABC_PA_" + key + "_AUDIT"] = "1"
    subprocess.run(["python3", str(ROOT / "src/ext-pa/tests/check_aig_copy.py")], check=True)
    passed = []
    for seed in [7, 23, 41]:
        source = directory / f"input{seed}.blif"
        original = directory / f"input{seed}.aig"
        network(source, seed)
        run(binary, f'read_blif "{source}"; strash; write_aiger "{original}"', directory, f"prepare{seed}", env)
        variants = {
            "hpwl": "pa_rw; pa_rf; pa_rs -N 2",
            "bounded": "pa_rw -t -S 2 -E 0; pa_rf -t -S 2 -E 0; pa_rs -N 2 -t -S 2",
            "lazy": "pa_rw -t -S 2 -E 1; pa_rf -t -S 2 -E 1; pa_rs -N 2 -t -S 2",
            "strict": "pa_rw -t -S 2; pa_rf -t -S 2; pa_rs -N 2 -t -S 2",
            "no_levels": "pa_rw -t -S 2 -l; pa_rf -t -S 2 -l; pa_rs -t -S 2 -l -N 2",
        }
        if seed == 7:
            variants["full_cone"] = "pa_rw -T; pa_rf -T; pa_rs -N 2 -T"
            variants["balanced"] = "pa_rf -t -S 2 -a; pa_rw -S 1; pa_rs -N 2 -S 1"
        for mode, flow in variants.items():
            label = f"seed{seed}_{mode}"
            target = directory / (label + ".aig")
            text = run(binary, f'read "{original}"; strash; pa_place; {flow}; {flow}; '
                       f'pa_stats; write_aiger "{target}"; cec "{original}" "{target}"', directory, label, env)
            assert target.exists() and "Networks are equivalent" in text, (label, text[-2000:])
            passed.append(label)
        if args.lib:
            for effort in [0, 2]:
                label = f"seed{seed}_unmap{effort}"
                target = directory / (label + ".aig")
                flow = f'&get; &nf; &put; pa_place; pa_strash; pa_rs -N 2 -t -S 2 -c; pa_rw -t -S 2 -E {effort} -c; pa_rf -t -S 2 -E {effort} -c'
                text = run(binary, f'read "{original}"; strash; read_lib "{args.lib.resolve()}"; '
                           f'{flow}; {flow}; pa_stats; write_aiger "{target}"; cec "{original}" "{target}"', directory, label, env)
                assert target.exists() and "Networks are equivalent" in text, (label, text[-2000:])
                passed.append(label)
    source = directory / "input7.aig"
    invalid = [
        ("pa_rw -t -E 3", "usage: pa_rw"), ("pa_rf -t -E -1", "usage: pa_rf"),
        ("pa_rw -E 1", "-E requires -t"), ("pa_rf -T -E 1", "-E requires -t"),
        ("pa_rw -t -E nan", "usage: pa_rw"), ("pa_rf -t -E", "usage: pa_rf"),
        ("pa_rs -N nan", "usage: pa_rs"), ("pa_rf -N 99999999999999999999999", "usage: pa_rf"),
        ("pa_rw -S 2", "-S 2 requires -t"), ("pa_rw -t -W nan", "usage: pa_rw"),
        ("pa_place -B 3", "outside its supported range"), ("pa_place -u nan", "invalid value"),
        ("pa_place -I 2147483647 -E 1", "outside its supported range"),
        ("pa_rw -c", "requires a placed mapped netlist"),
        ("pa_rf -c", "requires a placed mapped netlist"),
        ("pa_rs -c", "requires a placed mapped netlist"),
        ("pa_rw", "run pa_place"), ("pa_rf", "run pa_place"), ("pa_rs", "run pa_place"),
        ("pa_place; read_truth 8; strash; pa_stats", "has no placement"),
    ]
    for i, (command, expected) in enumerate(invalid):
        run(binary, f'read "{source}"; strash; {command}', directory, f"invalid{i}", env, expected)
    if args.audit:
        assert any("PA structural-screen audit:" in p.read_text() for p in directory.glob("seed*.log")), "--audit requires an audit-enabled executable"
    passed.extend(timing_seed_cases(binary, directory, env, args.audit))
    edges = edge_cases(binary, directory, env, args.lib.resolve() if args.lib else None)
    summary = dict(equivalent_cases=passed, edge_cases=edges, invalid_inputs_checked=len(invalid), audit=args.audit)
    (directory / "summary.json").write_text(json.dumps(summary, indent=2))
    print(f"PASS: {len(passed)} CEC cases, {len(edges)} edge cases, {len(invalid)} input/state checks. Logs: {directory}")


if __name__ == "__main__":
    main()
