"""Differential test for `searchsorted` (item_selection.c:2141 and npysort/binsearch.cpp) on small int64 arrays, sorted and unsorted, sides left and right, with and without a sorter."""
import numpy as np
from harness import fmt_ints, main

EXT = [-2**63, 2**63 - 1, -2**63 + 1, 2**63 - 2]


def pick_val(rng):
    return rng.randrange(-6, 7) if rng.random() < 0.9 else rng.choice(EXT)


def gen(rng):
    n = rng.randrange(0, 11)
    arr = [pick_val(rng) for _ in range(n)]
    if rng.random() < 0.7:
        arr.sort()
    keys = [pick_val(rng) for _ in range(rng.randrange(1, 6))]
    side = rng.choice("LR")
    r = rng.random()
    if r < 0.5:
        sorter = None
    elif r < 0.75:
        sorter = [int(x) for x in np.argsort(np.array(arr, dtype=np.int64), kind="stable")]
    elif r < 0.85:
        sorter = list(range(n))
        rng.shuffle(sorter)
    elif r < 0.95:
        sorter = [rng.randrange(-2, n + 3) for _ in range(n)]
    else:
        sorter = [rng.randrange(0, max(n, 1)) for _ in range(rng.randrange(0, 12))]
    line = f"searchsorted {fmt_ints(arr)} {fmt_ints(keys)} {side} {'N' if sorter is None else fmt_ints(sorter)}"
    try:
        res = np.searchsorted(np.array(arr, dtype=np.int64), np.array(keys, dtype=np.int64),
                              side="left" if side == "L" else "right",
                              sorter=None if sorter is None else np.array(sorter, dtype=np.int64))
        out = f"OK {fmt_ints(res)}"
    except ValueError as e:
        out = "ERR size" if "sorter.size" in str(e) else ("ERR range" if "out of range" in str(e) else "ERR " + str(e))
    return line, out


if __name__ == "__main__":
    main(gen, exe="npdiff_indexing")
