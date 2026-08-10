#!/usr/bin/env python3
"""Reconstruct ABC runeco patch outputs with ForMACE MinUNSAT interpolation."""

from __future__ import annotations

import argparse
import csv
import json
import re
import subprocess
import time
from dataclasses import asdict, dataclass
from pathlib import Path


ABC_ROOT = Path(__file__).resolve().parents[3]
PLAYGROUND = ABC_ROOT.parents[1]
DEFAULT_ABC = ABC_ROOT / "abc"
DEFAULT_BASELINE = PLAYGROUND / "try" / "results" / "0808_ECO"
DEFAULT_BENCHMARK = PLAYGROUND / "minimum-interpolation" / "ICCAD2021_ECO_benchmark"
DEFAULT_RESULTS = Path(__file__).resolve().parent / "results"


@dataclass
class OutputResult:
    index: int
    output: str
    candidates: int
    original_support: int
    selected_support: int
    seconds: float
    status: str


@dataclass
class CaseResult:
    case: str
    status: str
    outputs: int
    patch_inputs: int
    original_support_sum: int
    selected_support_sum: int
    original_support_union: int
    selected_support_union: int
    baseline_aig_ands: int
    minunsat_aig_ands: int
    interpolation_seconds: float
    verify_seconds: float
    equivalent_to_r2: bool
    equivalent_to_baseline: bool
    note: str


class ExperimentError(RuntimeError):
    pass


def run_logged(command: list[str], cwd: Path, log: Path, timeout: int) -> tuple[int, float, str]:
    started = time.monotonic()
    try:
        completed = subprocess.run(
            command,
            cwd=cwd,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            check=False,
        )
        output = completed.stdout
        returncode = completed.returncode
    except subprocess.TimeoutExpired as exc:
        partial = exc.stdout or ""
        if isinstance(partial, bytes):
            partial = partial.decode(errors="replace")
        output = partial + f"\nTIMEOUT after {timeout} seconds\n"
        returncode = 124
    seconds = time.monotonic() - started
    log.write_text("$ " + " ".join(command) + "\n\n" + output, encoding="utf-8")
    return returncode, seconds, output


def parse_module_interface(verilog: str, module: str = "patch") -> tuple[list[str], list[str]]:
    match = re.search(rf"\bmodule\s+{re.escape(module)}\s*\(.*?\);(.*?)\bendmodule\b", verilog, re.DOTALL)
    if not match:
        raise ExperimentError(f"cannot find module {module}")
    body = match.group(1)

    def names(keyword: str) -> list[str]:
        found: list[str] = []
        for declaration in re.findall(rf"\b{keyword}\b(.*?);", body, re.DOTALL):
            declaration = re.sub(r"\[\s*\d+\s*:\s*\d+\s*\]", "", declaration)
            declaration = re.sub(r"\b(?:wire|reg|logic|signed)\b", "", declaration)
            for part in declaration.split(","):
                name_match = re.search(r"[A-Za-z_][A-Za-z0-9_$]*(?:\[\s*\d+\s*\])?", part)
                if name_match:
                    found.append(re.sub(r"\s+", "", name_match.group(0)))
        return found

    return names("output"), names("input")


def parse_blif_inputs(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8", errors="replace")
    logical = re.sub(r"\\\n", " ", text)
    match = re.search(r"^\.inputs(?:\s+(.*))?$", logical, re.MULTILINE)
    return match.group(1).split() if match and match.group(1) else []


def parse_blif_support(path: Path, candidates: list[str]) -> list[str]:
    text = re.sub(r"\\\n", " ", path.read_text(encoding="utf-8", errors="replace"))
    candidate_set = set(candidates)
    support: set[str] = set()
    for match in re.finditer(r"^\.names\s+(.*)$", text, re.MULTILINE):
        tokens = match.group(1).split()
        support.update(token for token in tokens[:-1] if token in candidate_set)
    return sorted(support)


def parse_interpolant_support(output: str) -> tuple[int, list[str]]:
    matches = re.findall(r"ForMACE interpolant support \((\d+)\):(.*)", output)
    if not matches:
        # Constant onset/offset pairs are disjoint without any equality group.
        # fm_inter returns the constant network before its normal final support
        # print, but it does report the empty selected shared-PI set.
        matches = re.findall(r"ForMACE selected shared PIs \((\d+)\):(.*)", output)
    if not matches:
        raise ExperimentError("fm_inter did not report selected or interpolant support")
    count, names = matches[-1]
    selected = [] if names.strip() == "(none)" else names.split()
    if int(count) != len(selected):
        raise ExperimentError("interpolant-support count does not match names")
    return int(count), selected


def parse_aig_ands(output: str) -> int:
    matches = re.findall(r"\band\s*=\s*(\d+)", output)
    if not matches:
        raise ExperimentError("ABC did not print an AIG AND count")
    return int(matches[-1])


def rename_module(verilog: str, old: str, new: str) -> str:
    replaced, count = re.subn(rf"\bmodule\s+{re.escape(old)}\b", f"module {new}", verilog, count=1)
    if count != 1:
        raise ExperimentError(f"cannot rename module {old} to {new}")
    return replaced


def make_patch(outputs: list[str], inputs: list[str], modules: list[str]) -> str:
    lines = [
        "// Reconstructed per output by ForMACE fm_inter -m.",
        f"module patch ( {', '.join([*outputs, *inputs])} );",
        f"  output {', '.join(outputs)};",
        f"  input {', '.join(inputs)};",
        "",
    ]
    for index, output in enumerate(outputs):
        module_outputs, module_inputs = parse_module_interface(modules[index], f"fm_eco_inter_{index}")
        if module_outputs != [output]:
            raise ExperimentError(f"interpolant {index} output interface does not match {output}")
        connections = []
        for name in [*module_inputs, output]:
            formal = f"\\{name} " if "[" in name else name
            connections.append(f".{formal}({name})")
        lines.append(f"  fm_eco_inter_{index} u_inter_{index} ( {', '.join(connections)} );")
    lines.extend(["", "endmodule", "", *modules])
    return "\n".join(lines).rstrip() + "\n"


def make_integrated_output(baseline_out: Path, new_patch: str) -> str:
    text = baseline_out.read_text(encoding="utf-8", errors="replace")
    match = re.search(r"^module\s+patch\b", text, re.MULTILINE)
    if not match:
        raise ExperimentError(f"cannot locate patch module in {baseline_out}")
    return text[: match.start()].rstrip() + "\n\n" + new_patch


def extract_one(
    abc: Path,
    patch: Path,
    work: Path,
    index: int,
    output_name: str,
    candidate_count: int,
    limit: int,
    timeout: int,
) -> tuple[OutputResult, str, list[str]]:
    actual = work / f"output_{index:02d}_actual.blif"
    onset = work / f"output_{index:02d}_on.blif"
    offset = work / f"output_{index:02d}_off.blif"
    inter = work / f"output_{index:02d}_inter.v"
    log = work / f"output_{index:02d}_fm_inter.log"
    script = "; ".join(
        [
            f"read_verilog {patch}",
            f"cone -O {index}",
            f"write_blif {actual}",
            f"read_verilog {patch}",
            f"cone -O {index} -a",
            f"write_blif {onset}",
            f"read_blif {onset}",
            "strash -i",
            f"write_blif {offset}",
            f"fm_inter -m -L {limit} {onset} {offset}",
            f"write_verilog {inter}",
        ]
    )
    returncode, seconds, output = run_logged([str(abc), "-c", script], work, log, timeout)
    if returncode != 0 or not inter.is_file():
        status = "TIMEOUT" if returncode == 124 else "FAIL"
        result = OutputResult(index, output_name, candidate_count, len(parse_blif_support(actual, parse_blif_inputs(onset))) if actual.exists() else 0, 0, round(seconds, 6), status)
        return result, "", []
    selected_count, selected_names = parse_interpolant_support(output)
    original_support = len(parse_blif_support(actual, parse_blif_inputs(onset)))
    module_text = rename_module(inter.read_text(encoding="utf-8"), "patch", f"fm_eco_inter_{index}")
    result = OutputResult(index, output_name, candidate_count, original_support, selected_count, round(seconds, 6), "PASS")
    return result, module_text, selected_names


def get_patch_ands(abc: Path, patch: Path, work: Path, label: str, timeout: int) -> int:
    log = work / f"{label}_stats.log"
    _, _, output = run_logged(
        [str(abc), "-c", f"read_verilog {patch}; strash; print_stats"], work, log, timeout
    )
    return parse_aig_ands(output)


def verify_pair(abc: Path, first: Path, second: Path, work: Path, label: str, timeout: int) -> tuple[bool, float]:
    _, seconds, output = run_logged(
        [str(abc), "-c", f"cec {first} {second}"], work, work / f"{label}.log", timeout
    )
    return "Networks are equivalent" in output, seconds


def run_case(case: str, args: argparse.Namespace) -> tuple[CaseResult, list[OutputResult]]:
    baseline = args.baseline / case
    benchmark = args.benchmark / case
    result_dir = args.results / case
    result_dir.mkdir(parents=True, exist_ok=True)
    baseline_patch = baseline / "patch.v"
    baseline_out = baseline / "out.v"
    r2 = benchmark / "r2.fixed.v"
    for required in (baseline_patch, baseline_out, r2):
        if not required.is_file():
            raise ExperimentError(f"missing required input: {required}")

    outputs, inputs = parse_module_interface(baseline_patch.read_text(encoding="utf-8"))
    if len(inputs) > args.limit:
        raise ExperimentError(f"{case} has {len(inputs)} candidates, exceeding --limit {args.limit}")

    output_results: list[OutputResult] = []
    modules: list[str] = []
    selected_union: set[str] = set()
    for index, output_name in enumerate(outputs):
        print(f"[{case}] output {index + 1}/{len(outputs)} {output_name}", flush=True)
        result, module, selected = extract_one(
            args.abc.resolve(), baseline_patch.resolve(), result_dir, index, output_name,
            len(inputs), args.limit, args.output_timeout,
        )
        output_results.append(result)
        if result.status != "PASS":
            return CaseResult(case, "FAIL", len(outputs), len(inputs), 0, 0, 0, 0, 0, 0, 0.0, 0.0, False, False, f"output {index} {result.status}"), output_results
        modules.append(module)
        selected_union.update(selected)

    new_patch_text = make_patch(outputs, inputs, modules)
    new_patch_path = result_dir / "patch_minunsat.v"
    new_patch_path.write_text(new_patch_text, encoding="utf-8")
    new_out_path = result_dir / "out_minunsat.v"
    new_out_path.write_text(make_integrated_output(baseline_out, new_patch_text), encoding="utf-8")

    baseline_ands = get_patch_ands(args.abc, baseline_patch.resolve(), result_dir, "baseline_patch", args.verify_timeout)
    minunsat_ands = get_patch_ands(args.abc, new_patch_path.resolve(), result_dir, "minunsat_patch", args.verify_timeout)
    equivalent_r2, verify_seconds = verify_pair(
        args.abc, r2.resolve(), new_out_path.resolve(), result_dir, "verify_r2_vs_minunsat", args.verify_timeout
    )
    equivalent_baseline, baseline_verify_seconds = verify_pair(
        args.abc, baseline_out.resolve(), new_out_path.resolve(), result_dir,
        "verify_baseline_vs_minunsat", args.verify_timeout,
    )
    total_seconds = sum(item.seconds for item in output_results)
    case_result = CaseResult(
        case=case,
        status="PASS" if equivalent_r2 and equivalent_baseline else "FAIL",
        outputs=len(outputs),
        patch_inputs=len(inputs),
        original_support_sum=sum(item.original_support for item in output_results),
        selected_support_sum=sum(item.selected_support for item in output_results),
        original_support_union=len(inputs),
        selected_support_union=len(selected_union),
        baseline_aig_ands=baseline_ands,
        minunsat_aig_ands=minunsat_ands,
        interpolation_seconds=round(total_seconds, 6),
        verify_seconds=round(verify_seconds + baseline_verify_seconds, 6),
        equivalent_to_r2=equivalent_r2,
        equivalent_to_baseline=equivalent_baseline,
        note="",
    )
    (result_dir / "outputs.json").write_text(
        json.dumps([asdict(item) for item in output_results], indent=2) + "\n", encoding="utf-8"
    )
    return case_result, output_results


def write_summaries(results: list[CaseResult], output_results: dict[str, list[OutputResult]], directory: Path) -> None:
    rows = [asdict(result) for result in results]
    (directory / "summary.json").write_text(json.dumps(rows, indent=2) + "\n", encoding="utf-8")
    with (directory / "summary.csv").open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    details = [dict(case=case, **asdict(item)) for case, items in output_results.items() for item in items]
    (directory / "output_details.json").write_text(json.dumps(details, indent=2) + "\n", encoding="utf-8")
    if details:
        with (directory / "output_details.csv").open("w", newline="", encoding="utf-8") as stream:
            writer = csv.DictWriter(stream, fieldnames=list(details[0]))
            writer.writeheader()
            writer.writerows(details)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--abc", type=Path, default=DEFAULT_ABC)
    parser.add_argument("--baseline", type=Path, default=DEFAULT_BASELINE)
    parser.add_argument("--benchmark", type=Path, default=DEFAULT_BENCHMARK)
    parser.add_argument("--results", type=Path, default=DEFAULT_RESULTS)
    parser.add_argument("--case", action="append", help="Case such as test01; repeatable")
    parser.add_argument("--limit", type=int, default=32, help="Maximum exact MinUNSAT candidates")
    parser.add_argument("--output-timeout", type=int, default=300)
    parser.add_argument("--verify-timeout", type=int, default=180)
    args = parser.parse_args()
    if not args.abc.is_file():
        raise SystemExit(f"ABC binary not found: {args.abc}")
    args.results.mkdir(parents=True, exist_ok=True)

    selected = set(args.case or [])
    cases = [path.name for path in sorted(args.benchmark.glob("test*")) if not selected or path.name in selected]
    if not cases:
        raise SystemExit("no cases selected")

    results: list[CaseResult] = []
    details: dict[str, list[OutputResult]] = {}
    for case in cases:
        try:
            result, outputs = run_case(case, args)
        except ExperimentError as exc:
            result = CaseResult(case, "FAIL", 0, 0, 0, 0, 0, 0, 0, 0, 0.0, 0.0, False, False, str(exc))
            outputs = []
        results.append(result)
        details[case] = outputs
        write_summaries(results, details, args.results)
        outcome = result.note or ("verified" if result.status == "PASS" else "equivalence check failed")
        print(f"[{case}] {result.status}: {outcome}", flush=True)
    return 0 if all(result.status == "PASS" for result in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
