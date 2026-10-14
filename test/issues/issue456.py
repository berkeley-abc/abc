#!/usr/bin/env python3
"""Manual &blut regression using &cec.

Run from the repository root with Python 3. No third-party modules are needed.
--output retains each small Verilog witness and its before/after AIG and log.
"""
import argparse
import json
import pathlib
import random
import subprocess
import tempfile


def module(inputs, outputs, assignments):
    wires = [name for name, _ in assignments if name not in outputs]
    return ("module top(" + ", ".join(inputs + outputs) + ");\n"
            + "input " + ", ".join(inputs) + ";\n"
            + "output " + ", ".join(outputs) + ";\n"
            + ("wire " + ", ".join(wires) + ";\n" if wires else "")
            + "".join("assign %s = %s;\n" % pair for pair in assignments)
            + "endmodule\n")


def cases(stress):
    inputs = list("abcdstuv")
    outputs = ["a0", "a1", "b0", "b1"]
    # Each pair has the same mux shape. The groups depend on each other,
    # although no individual tree depends on itself or its group mate.
    cross = [("ax", "s ? a : b"), ("ay", "s ? a : d"),
             ("bx", "u ? b : c"), ("by", "u ? a : c"),
             ("a0", "t ? ax : c"), ("b1", "v ? by : d"),
             ("ga", "b1 & c"), ("gb", "a0 & d"),
             ("a1", "t ? ay : ga"), ("b0", "v ? bx : gb")]
    yield "two_groups", module(inputs, outputs, cross)
    yield "reversed_outputs", module(inputs, outputs[::-1], cross)
    yield "inverted_controls", module(inputs, outputs,
          [(n, e.replace("s ?", "~s ?").replace("t ?", "~t ?")) for n, e in cross])
    three = cross[:4] + [("cx", "w ? c : d"), ("cy", "w ? b : d"),
            ("a0", "t ? ax : c"), ("b1", "v ? by : d"),
            ("c1", "x ? cy : a"), ("gb", "c1 & d"),
            ("b0", "v ? bx : gb"), ("gc", "a0 & b"),
            ("c0", "x ? cx : gc"), ("ga", "b1 & c"),
            ("a1", "t ? ay : ga")]
    yield "three_groups", module(inputs + list("wx"), outputs + ["c0", "c1"], three)
    control = [("bx", "u ? b : c"), ("by", "u ? a : c"),
               ("b0", "v ? bx : d"), ("sel", "b0 & s"),
               ("ax", "sel ? a : b"), ("ay", "sel ? a : d"),
               ("a0", "t ? ax : c"), ("a1", "t ? ay : b"),
               ("gb", "a0 & d"), ("b1", "v ? by : gb")]
    yield "control_dependency", module(inputs, outputs, control)
    yield "downstream_logic", module(inputs, outputs + ["y", "z"], cross +
          [("y", "(a0 ^ b0) | a1"), ("z", "(b1 ^ a1) & b0")])
    extended = cross + [("az", "s ? b : d"), ("bz", "u ? a : d"),
                        ("ha", "b0 & b"), ("hb", "a1 & a"),
                        ("a2", "t ? az : ha"), ("b2", "v ? bz : hb")]
    yield "larger_groups", module(inputs, outputs + ["a2", "b2"], extended)
    for count in (3, 4):
        assignments, ports, results = [], list("abcd"), []
        for i in range(count):
            ports += ["s%d" % i, "t%d" % i]
            results += ["base%d" % i, "dep%d" % i]
            assignments += [("x%d" % i, "s%d ? a : b" % i),
                            ("y%d" % i, "s%d ? a : d" % i),
                            ("base%d" % i, "t%d ? x%d : c" % (i, i))]
        for i in range(count):
            assignments += [("g%d" % i, "base%d & d" % ((i + 1) % count)),
                            ("dep%d" % i, "t%d ? y%d : g%d" % (i, i, i))]
        yield "ring_%d" % count, module(ports, results, assignments)
    # Controls: these must retain correct logic without a cross-group cycle.
    independent = [(n, "c" if n == "ga" else "d" if n == "gb" else e)
                   for n, e in cross]
    yield "independent_groups", module(inputs, outputs, independent)
    acyclic = [(n, "c" if n == "ga" else e) for n, e in cross]
    yield "acyclic_groups", module(inputs, outputs, acyclic)
    same = [(n, "a0 & c" if n == "ga" else "d" if n == "gb" else e)
            for n, e in cross]
    yield "same_group_dependency", module(inputs, outputs, same)
    for phase in range(16):
        assignments = [(n, ("~(" + e + ")") if
                        n in ("ga", "gb", "ax", "bx") and
                        phase & (1 << ("ga", "gb", "ax", "bx").index(n)) else e)
                       for n, e in cross]
        yield "phase_%02d" % phase, module(inputs, outputs, assignments)
    # Deterministic mux-rich DAGs with repeated select pairs and reconvergence.
    rng = random.Random(456)
    for seed in range(stress):
        pool, assignments = list("abcd"), []
        for i in range(24):
            s, t = rng.choice([("s", "t"), ("u", "v")])
            a, b, c = rng.sample(pool, 3)
            leaf = ("~" if rng.randrange(2) else "") + c
            assignments += [("m%d" % i, "%s ? %s : %s" % (s, a, b)),
                            ("r%d" % i, "%s ? m%d : %s" % (t, i, leaf)),
                            ("g%d" % i, "r%d %s %s" % (i, rng.choice(["&", "^"]), a))]
            pool.append("g%d" % i)
        yield "random_%03d" % seed, module(inputs, ["r%d" % i for i in range(24)], assignments)


def run(args, output):
    results = []
    flags = ["", "-K 2", "-K 4", "-a", "-m", "-r"]
    for name, source in cases(args.stress):
        for variant, options in enumerate(flags):
            case = output / (name + "-%d" % variant)
            case.mkdir(parents=True, exist_ok=True)
            (case / "input.v").write_text(source)
            command = ("read_verilog input.v; strash; &get; &write before.aig; "
                       "&blut -v %s; &write after.aig; &cec before.aig") % options
            completed = subprocess.run([str(args.abc), "-s", "-c", command], cwd=case,
                                       capture_output=True, text=True, timeout=60)
            log = completed.stdout + completed.stderr
            (case / "abc.log").write_text(log)
            record = {"case": name, "flags": options, "returncode": completed.returncode,
                      "cec": "Networks are equivalent" in log}
            results.append(record)
    (output / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    failures = [r for r in results if r["returncode"] != 0 or not r["cec"]]
    for r in failures[:20]:
        print("FAIL:", r)
    print("Issue #456: %d/%d passed; results: %s" %
          (len(results) - len(failures), len(results), output), flush=True)
    return bool(failures)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--abc", type=pathlib.Path, default=pathlib.Path("./abc"))
    parser.add_argument("--output", type=pathlib.Path)
    parser.add_argument("--stress", type=int, default=20)
    args = parser.parse_args()
    args.abc = args.abc.resolve()
    if args.output:
        raise SystemExit(run(args, args.output.resolve()))
    with tempfile.TemporaryDirectory(prefix="abc-issue456-") as directory:
        raise SystemExit(run(args, pathlib.Path(directory)))
