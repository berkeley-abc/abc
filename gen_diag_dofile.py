import re

def parse_pattern_file(pattern_filename):
    patterns = []
    with open(pattern_filename) as f:
        for line in f:
            if not line.strip():
                continue
            parts = line.strip().split()
            if len(parts) != 2:
                print(f"Warning: Skipping malformed pattern line: {line}")
                continue
            patterns.append((parts[0], parts[1]))
    return patterns

def parse_diag_file(diag_filename):
    pattern_po_overrides = {}  # pattern -> dict(po_idx -> bit)
    gat_to_po = {22:0, 23:1}             # gat number -> PO index
    next_po_idx = 0

    pattern_re = re.compile(r"T'([01]+)'")
    gat_re = re.compile(r"(\d+)GAT")

    with open(diag_filename) as f:
        for line in f:
            pat_match = pattern_re.search(line)
            gat_match = gat_re.search(line)
            if not pat_match or not gat_match:
                continue

            pattern = pat_match.group(1)
            gat_num = int(gat_match.group(1))

            if gat_num not in gat_to_po:
                gat_to_po[gat_num] = next_po_idx
                next_po_idx += 1
            po_idx = gat_to_po[gat_num]

            bit = "0" if "observe L" in line else "1"

            if pattern not in pattern_po_overrides:
                pattern_po_overrides[pattern] = {}

            pattern_po_overrides[pattern][po_idx] = bit

    return pattern_po_overrides

def apply_overrides(base_po, override_map):
    po_list = list(base_po)
    for idx, bit in override_map.items():
        if idx < len(po_list):
            po_list[idx] = bit
        else:
            print(f"Warning: PO index {idx} out of range for base PO {base_po}")
    return ''.join(po_list)

def generate_dofile(pattern_file, bench_file, output_file, diag_file=None):
    patterns = parse_pattern_file(pattern_file)
    diag_overrides = parse_diag_file(diag_file) if diag_file else {}
    print(diag_overrides)
    lines = []
    lines.append(f"read {bench_file}")
    lines.append("fault_gen -c")
    lines.append("fault_sim")
    lines.append("backup")

    for idx, (pi, po) in enumerate(patterns):
        if pi in diag_overrides:
            po = apply_overrides(po, diag_overrides[pi])

        lines.append(f"add_tp {pi}")
        lines.append("insert_tp")
        lines.append(f"add_po {po}")
        lines.append("fraig")
        lines.append("strash")
        lines.append("&get")
        lines.append(f"&write_cnf ./diag{idx}.cnf")
        lines.append("restore")

    lines.append("print_io")

    with open(output_file, 'w') as f:
        f.write('\n'.join(lines))
    print(f"Dofile written to {output_file}")

if __name__ == "__main__":
    import sys
    if len(sys.argv) < 4:
        print("Usage: python gen_diag_dofile.py <pattern_file> <bench_file> <output_file> [diag_file]")
        sys.exit(1)

    pattern_file = sys.argv[1]
    bench_file = sys.argv[2]
    output_file = sys.argv[3]
    diag_file = sys.argv[4] if len(sys.argv) > 4 else None

    generate_dofile(pattern_file, bench_file, output_file, diag_file)

# generate_dofile("diag.ptn", "./testcase/c17_pa.bench", "generated.dofile", f"./Project_25S_diag/failLog/c17-001.failLog")
