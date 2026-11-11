"""Shared driver for the differential tests.

A test file defines `gen(rng)`, which returns one `(line, expected)` pair. `line` is the text sent to the Lean executable `npdiff` and `expected` is what the real NumPy printed for the same input. `main(gen)` draws the cases, runs them through `npdiff` in one batch and reports every line where the two sides differ.
"""
import argparse
import os
import random
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIN = os.path.join(ROOT, "lean", ".lake", "build", "bin")


def fmt_ints(xs):
    xs = list(xs)
    return ",".join(str(int(x)) for x in xs) if xs else "_"


def fmt_bool(b):
    return "True" if b else "False"


def run_lean(lines, exe="npdiff"):
    proc = subprocess.run([os.path.join(BIN, exe)], input="\n".join(lines) + "\n", capture_output=True, text=True)
    if proc.returncode != 0:
        sys.exit(f"npdiff failed: {proc.stderr[:2000]}")
    out = proc.stdout.split("\n")
    if out and out[-1] == "":
        out.pop()
    return out


def main(gen, exe="npdiff", default_cases=50000):
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases", type=int, default=default_cases)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--show", type=int, default=20, help="how many mismatches to print")
    args = ap.parse_args()
    rng = random.Random(args.seed)
    pairs = [gen(rng) for _ in range(args.cases)]
    got = run_lean([p[0] for p in pairs], exe)
    if len(got) != len(pairs):
        sys.exit(f"npdiff returned {len(got)} lines for {len(pairs)} cases")
    bad = [(line, exp, g) for (line, exp), g in zip(pairs, got) if exp != g]
    for line, exp, g in bad[: args.show]:
        print(f"MISMATCH {line}\n  numpy: {exp}\n  lean:  {g}")
    kinds = {}
    for _, exp in pairs:
        key = exp.split(" ")[0]
        kinds[key] = kinds.get(key, 0) + 1
    print(f"{len(pairs) - len(bad)}/{len(pairs)} agree, seed {args.seed}, outcomes {kinds}")
    sys.exit(1 if bad else 0)
