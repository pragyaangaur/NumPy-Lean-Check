"""Differential test for `np.unique` on one-dimensional integer arrays of a single dtype (`_unique1d`, _arraysetops_impl.py:350).

The array has up to 14 elements of dtype int8, uint8, int16, uint32, int64 or uint64, drawn from a small pool of repeated values that includes the minimum and maximum of the dtype and values near `2**31`, `2**32`, `2**62` and `2**63`, so that runs of equal values are common. Axis is always None and nothing is NaN. Each case calls `np.unique` with all of `return_index`, `return_inverse` and `return_counts`, and then checks that the other entry points agree with it and with a plain Python model: `np.unique` with each flag alone, `np.unique_values` (whose order is unspecified since NumPy 2.3, so it is compared after sorting), `np.unique_counts`, `np.unique_inverse` and `np.unique_all`. Any disagreement among them, or with the Python model, is reported as `INCONSISTENT` and counts as a mismatch. The Lean side models `_unique1d` line by line.
"""
import numpy as np
from harness import fmt_ints, main

DTYPES = [np.int8, np.uint8, np.int16, np.uint32, np.int64, np.uint64]


def pool(rng, dt):
    info = np.iinfo(dt)
    lo, hi = int(info.min), int(info.max)
    special = {lo, hi, 0, 1, lo + 1, hi - 1, -1, 2**31, 2**31 - 1, 2**32, 2**32 - 1, 2**62, 2**62 + 1, 2**63, 2**63 - 1, 2**63 + 1, -2**31, -2**63, -2**62}
    special = [v for v in special if lo <= v <= hi]
    k = rng.choice([1, 2, 3, 5, 8])
    vals = [rng.choice(special) if rng.random() < 0.6 else rng.randint(lo, hi) for _ in range(k)]
    if rng.random() < 0.3:
        vals = [v for v in vals] + [rng.randint(max(lo, 0), min(hi, 6)) for _ in range(2)]
    return vals


def model(vals):
    n = len(vals)
    perm = sorted(range(n), key=lambda i: vals[i])
    uv, first, counts, inv = [], [], [], [0] * n
    for i in perm:
        if not uv or vals[i] != uv[-1]:
            uv.append(vals[i])
            first.append(i)
            counts.append(0)
        counts[-1] += 1
        inv[i] = len(uv) - 1
    return uv, first, inv, counts


def gen(rng):
    dt = rng.choice(DTYPES)
    p = pool(rng, dt)
    n = rng.choice([0, 1, 2, 3, rng.randrange(0, 15), rng.randrange(0, 15)])
    vals = [rng.choice(p) for _ in range(n)]
    line = f"unique {fmt_ints(vals)}"
    a = np.array(vals, dtype=dt)
    v, i, inv, c = np.unique(a, return_index=True, return_inverse=True, return_counts=True)
    got = (v, i, inv, c)
    fmt = lambda t: "OK " + " ".join(fmt_ints(x) for x in t)
    out = fmt(got)
    mv, mi, minv, mc = model(vals)
    ok = [int(x) for x in v] == mv and [int(x) for x in i] == mi and [int(x) for x in inv] == minv and [int(x) for x in c] == mc
    same = lambda x, y: x.shape == y.shape and x.dtype == y.dtype and bool((x == y).all())
    ok &= same(np.unique(a), v) and same(np.sort(np.unique_values(a)), v) and same(np.sort(np.unique(a, sorted=False)), v)
    r = np.unique(a, return_index=True)
    ok &= same(r[0], v) and same(r[1], i)
    r = np.unique(a, return_inverse=True)
    ok &= same(r[0], v) and same(r[1], inv)
    r = np.unique(a, return_counts=True)
    ok &= same(r[0], v) and same(r[1], c)
    r = np.unique_counts(a)
    ok &= same(r.values, v) and same(r.counts, c)
    r = np.unique_inverse(a)
    ok &= same(r.values, v) and same(r.inverse_indices, inv)
    r = np.unique_all(a)
    ok &= same(r.values, v) and same(r.indices, i) and same(r.inverse_indices, inv) and same(r.counts, c)
    ok &= v.dtype == dt
    if not ok:
        out = "INCONSISTENT " + out
    return line, out


if __name__ == "__main__":
    main(gen, exe="npdiff_libint")
