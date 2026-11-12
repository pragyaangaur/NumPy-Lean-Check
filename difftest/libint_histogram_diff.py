"""Differential test for `np.histogram` and `np.histogram_bin_edges` (_histograms_impl.py:474 and :640) on tiny integer arrays with an integer `bins` count.

The data has up to 10 elements of dtype int8, uint8, int16, uint32, int64 or uint64. `bins` runs from 0 to 12. The range is `None` or a pair of Python integers. Pairs are drawn so that most have a width that is a multiple of `bins` with edges that doubles hold exactly (small integers, or multiples of a power of two up to `2**62`), and the rest are random, empty, reversed, equal, or reach the ends of `int64` and `uint64`. Data is drawn at the edges, one beyond them and one inside them, so that data close to a bin edge is common, including values above `2**53`.

The expected side is NumPy. The Lean side repeats the code path with IEEE doubles: `linspace` for the edges, then the block loop of `histogram` with its integer-to-double conversions and its two correction steps. The edges are compared exactly, as `m@e` pairs from `frexp`. `histogram` must return the same edges as `histogram_bin_edges`, and when it does not the case counts as `INCONSISTENT`. A call where `histogram_bin_edges` succeeds and `histogram` raises is printed as `OK <edges> ERR <name>`.

The test also counts, separately and without affecting the agreement, how many cases with exact edges have counts that differ from an exact integer model. Those cases are the subject of the bug record libint-histogram-int64-rounds-to-double.
"""
import math
import sys

import numpy as np
from harness import fmt_ints, main

DTYPES = [np.int8, np.uint8, np.int16, np.uint32, np.int64, np.uint64]


def fmt_double(f):
    f = float(f)
    if f == 0:
        return "0"
    m, e = math.frexp(abs(f))
    return f"{'-' if f < 0 else ''}{int(m * 2**53)}@{e - 53}"


def classify(e):
    msg = str(e)
    if isinstance(e, OverflowError):
        return "overflow"
    if isinstance(e, IndexError):
        return "index"
    if "must be positive" in msg:
        return "bins"
    if "max must be larger" in msg:
        return "range"
    if "Too many bins" in msg:
        return "toomany"
    if "no negative" in msg:
        return "negindex"
    return "other:" + type(e).__name__ + ":" + msg


def pick_range(rng, bins):
    r = rng.random()
    if r < 0.2:
        return None
    b = max(bins, 1)
    if r < 0.5:
        lo = rng.randint(-20, 20)
        w = b * rng.randint(0, 8)
        return (lo, lo + w)
    if r < 0.75:
        k = rng.randint(20, 62)
        lo = rng.randint(-3, 3) * 2**k
        w = rng.randint(1, 4) * b * 2**(k - 3) if k > 3 else 1
        lo = max(lo, -2**63)
        return (lo, min(lo + w, 2**64 - 1))
    if r < 0.8:
        return rng.choice([(-2**63, 2**63 - 1), (0, 2**63 - 1), (0, 2**64 - 1), (-128, 127), (0, 255), (-2**63, 0), (0, 2**63), (-2**62, 2**62), (-2**53 - 1, 2**53 + 1)])
    if r < 0.85:
        return (rng.randint(-5, 5), rng.randint(-5, 5))
    lo = rng.randint(-2**63, 2**63 - 1)
    return (lo, rng.randint(lo, 2**63 - 1))


def gen(rng):
    dt = rng.choice(DTYPES)
    info = np.iinfo(dt)
    dlo, dhi = int(info.min), int(info.max)
    bins = rng.choice([0, 1, 2, 3, 4, 5, 8, rng.randint(1, 12)])
    rg = pick_range(rng, bins)
    anchors = [0, 1, dlo, dhi]
    if rg is not None:
        lo, hi = rg
        b = max(bins, 1)
        anchors += [lo, hi]
        if hi >= lo:
            anchors += [lo + (hi - lo) * j // b for j in range(b + 1)]
    n = rng.choice([0, 1, 2, 3, rng.randint(0, 10)])
    vals = []
    for _ in range(n):
        if rng.random() < 0.8:
            v = rng.choice(anchors) + rng.choice([0, 0, 0, 1, -1, 2, -2])
        else:
            v = rng.randint(dlo, dhi)
        vals.append(min(max(v, dlo), dhi))
    line = f"hist {fmt_ints(vals)} {bins} {rg[0] if rg else 'N'} {rg[1] if rg else 'N'}"
    a = np.array(vals, dtype=dt)
    try:
        edges = np.histogram_bin_edges(a, bins=bins, range=rg)
    except Exception as e:
        return line, "ERR " + classify(e)
    es = ",".join(fmt_double(x) for x in edges)
    try:
        counts, edges2 = np.histogram(a, bins=bins, range=rg)
    except Exception as e:
        return line, f"OK {es} ERR {classify(e)}"
    out = f"OK {es} {fmt_ints(counts)}"
    if not (edges.shape == edges2.shape and bool((edges == edges2).all())):
        out = "INCONSISTENT " + out
    exact_edges = all(Fraction_exact(edges, rg, bins))
    if exact_edges and rg is not None and rg[0] < rg[1] and (rg[1] - rg[0]) % bins == 0:
        lo, hi = rg
        model = [0] * bins
        for v in vals:
            if lo <= v <= hi:
                model[min((v - lo) * bins // (hi - lo), bins - 1)] += 1
        if model != [int(c) for c in counts]:
            STATS["exact_model_differs"] += 1
        STATS["exact_cases"] += 1
    return line, out


STATS = {"exact_cases": 0, "exact_model_differs": 0}


def Fraction_exact(edges, rg, bins):
    """True for each edge that equals the exact rational `lo + i * (hi - lo) / bins`."""
    from fractions import Fraction
    if rg is None or rg[0] >= rg[1]:
        return [False]
    lo, hi = rg
    return [Fraction(float(e)) == Fraction(lo) + Fraction(i * (hi - lo), bins) for i, e in enumerate(edges)]


if __name__ == "__main__":
    import atexit
    atexit.register(lambda: print("exact-edge cases:", STATS["exact_cases"], "differing from the exact model:", STATS["exact_model_differs"]))
    main(gen, exe="npdiff_libint")
