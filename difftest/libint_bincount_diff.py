"""Differential test for `np.bincount` without weights (`arr_bincount`, compiled_base.c:115) on small `int64` lists.

Lists hold small non-negative values, sometimes a negative value, and sometimes one value of at least `2**60`, where the output length `mx + 1` is too big or wraps. `minlength` is zero, small, negative or huge. A case runs only when the output has at most 4096 elements or when the constructor rejects its size before allocating. A list that holds `2**63 - 1` with a small `minlength` is skipped, because the wrapped length lets the counting loop write before the start of the output buffer, which can crash this process. The bug record libint-bincount-max-intp-out-of-bounds covers it.
"""
import numpy as np
from harness import fmt_ints, main

HUGE = [2**60, 2**61, 2**62, 2**63 - 2, 2**63 - 1]


def gen(rng):
    while True:
        n = rng.choice([0, 1, 2, 5, rng.randrange(0, 12)])
        vals = [rng.randrange(0, 10) if rng.random() < 0.9 else rng.randrange(10, 70) for _ in range(n)]
        r = rng.random()
        if r < 0.1 and vals:
            vals[rng.randrange(n)] = -rng.randrange(1, 5)
        elif r < 0.2 and vals:
            vals[rng.randrange(n)] = rng.choice(HUGE)
        m = rng.choice([0, 0, 0, 1, 5, 12, 70, -1, rng.choice(HUGE)])
        size = max([v + 1 for v in vals] + [m]) if vals or m > 0 else 0
        if 2**63 - 1 in vals and m < 2**60:
            continue
        if size <= 4096 or size >= 2**60:
            break
    line = f"bincount {fmt_ints(vals)} {m}"
    try:
        res = np.bincount(np.array(vals, dtype=np.int64), minlength=m)
        out = f"OK {len(res)} {fmt_ints(res) if len(res) <= 64 else '-'}"
    except ValueError as e:
        msg = str(e)
        if "minlength" in msg:
            out = "ERR minlength"
        elif "no negative" in msg:
            out = "ERR negative"
        elif "negative dimensions" in msg:
            out = "ERR negdim"
        elif "too big" in msg:
            out = "ERR toobig"
        else:
            out = "ERR " + msg
    return line, out


if __name__ == "__main__":
    main(gen, exe="npdiff_libint")
