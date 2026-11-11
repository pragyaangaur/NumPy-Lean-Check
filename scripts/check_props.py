"""Count the properties in lean/NumpyLean by area and status, and list uses of sorry, axioms and compiler-trusting tactics."""
import collections
import glob
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROP = re.compile(r"PROP\s+(\S+)\s*:\s*(PROVEN|REFUTED|OPEN)")


def main():
    counts = collections.defaultdict(collections.Counter)
    flags = collections.Counter()
    names = collections.Counter()
    for path in sorted(glob.glob(os.path.join(ROOT, "lean", "NumpyLean", "**", "*.lean"), recursive=True)):
        area = os.path.relpath(path, os.path.join(ROOT, "lean", "NumpyLean")).split(os.sep)[0]
        text = open(path).read()
        for name, status in PROP.findall(text):
            counts[area][status] += 1
            names[name] += 1
        code = re.sub(r"/-.*?-/", "", text, flags=re.S)
        code = re.sub(r"--.*", "", code)
        for word in ("sorry", "native_decide", "bv_decide"):
            flags[word] += len(re.findall(rf"\b{word}\b", code))
        flags["axiom"] += len(re.findall(r"^\s*axiom\b", code, flags=re.M))
    total = collections.Counter()
    print(f"{'area':<16}{'proven':>8}{'refuted':>9}{'open':>6}")
    for area in sorted(counts):
        c = counts[area]
        total.update(c)
        print(f"{area:<16}{c['PROVEN']:>8}{c['REFUTED']:>9}{c['OPEN']:>6}")
    print(f"{'total':<16}{total['PROVEN']:>8}{total['REFUTED']:>9}{total['OPEN']:>6}")
    print("flags:", dict(flags))
    dup = [n for n, k in names.items() if k > 1]
    if dup:
        print("duplicate property names:", dup)
    sys.exit(1 if flags["sorry"] or flags["axiom"] or dup else 0)


if __name__ == "__main__":
    main()
