"""Differential test for the output length of `repeat` (item_selection.c:895) and for the shape and offset of `diagonal` (item_selection.c:2321).

`repeat` writes the true sum of the counts into an output whose length is computed with a wrapping multiply or sum, so a case where the two differ and the output is allocated would write out of bounds. The generator skips those cases and any case that would allocate more than a few kilobytes. The bug record indexing-repeat-count-overflow covers them.
"""
import numpy as np
from harness import fmt_ints, main

BIG = [2**61, 2**62, 2**62 + 1, 2**63 - 1, 2**60 + 3, 2**32, 2**31]


def wrap64(x):
    return (x + 2**63) % 2**64 - 2**63


def pick_count(rng):
    r = rng.random()
    if r < 0.7:
        return rng.randrange(0, 6)
    if r < 0.8:
        return -rng.randrange(1, 4)
    return rng.choice(BIG + [-b for b in BIG])


def safe_to_run(n, counts, itemsize):
    """True unless the call would allocate a large array or write past the end of the output."""
    if len(counts) == 1:
        writes = counts[0] * n
        total = wrap64(writes)
    else:
        if len(counts) != n or any(c < 0 for c in counts):
            return True
        writes = sum(counts)
        total = 0
        for c in counts:
            total = wrap64(total + c)
    if total < 0 or total * itemsize >= 2**63:
        return True
    return total == writes and total <= 10**4


def gen_repeat(rng):
    while True:
        n = rng.randrange(0, 7)
        k = 1 if rng.random() < 0.5 else (n if rng.random() < 0.9 else rng.randrange(0, 8))
        counts = [pick_count(rng) for _ in range(k)]
        itemsize = rng.choice([1, 8])
        if safe_to_run(n, counts, itemsize):
            break
    line = f"repeat {n} {fmt_ints(counts)} {itemsize}"
    a = np.arange(n, dtype=np.int8 if itemsize == 1 else np.int64)
    try:
        out = f"OK {len(np.repeat(a, counts if k != 1 or rng.random() < 0.5 else counts[0]))}"
    except ValueError as e:
        msg = str(e)
        if "broadcast" in msg:
            out = "ERR mismatch"
        elif "repeats may not" in msg:
            out = "ERR negcount"
        elif "negative dimensions" in msg:
            out = "ERR negdim"
        elif "too big" in msg:
            out = "ERR toobig"
        else:
            out = "ERR " + msg
    return line, out


def gen_diag(rng):
    r, c = rng.randrange(0, 7), rng.randrange(0, 7)
    if rng.random() < 0.8:
        k = rng.randrange(-9, 10)
    else:
        e = rng.choice([2**31 - 1, 2**31, 2**31 + 1, 2**40, 2**63 - 1])
        k = rng.choice([e, -e, -e - 1])
    a = np.arange(r * c, dtype=np.int64).reshape(r, c)
    line = f"diag {r} {c} {a.strides[0] // 8} {k}"
    try:
        d = np.diagonal(a, offset=k)
        start = (d.__array_interface__["data"][0] - a.__array_interface__["data"][0]) // 8
        out = f"OK {d.shape[0]} {start} {d.strides[0] // 8}"
    except OverflowError:
        out = "ERR overflow"
    return line, out


def gen(rng):
    return gen_repeat(rng) if rng.random() < 0.6 else gen_diag(rng)


if __name__ == "__main__":
    main(gen, exe="npdiff_indexing")
