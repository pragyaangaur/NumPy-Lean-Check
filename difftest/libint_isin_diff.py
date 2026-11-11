"""Differential test for `np.isin` (`_isin`, _arraysetops_impl.py:806) on small integer arrays with all three `kind` values.

The values come from a shared pool of small numbers and numbers near `2**53`, `2**62`, `2**63` and `2**64`, clipped to the dtype, so that matches are common and the sort path meets values that collide as doubles. Lengths of `ar2` range from 0 to 30, which crosses the loop limit `10 * len(ar1) ** 0.145`. A case with `kind='table'` whose table would be large is skipped, because the table path allocates `max - min + 1` booleans.
"""
import numpy as np
from harness import fmt_ints, main

DT = {"i8": np.int8, "u8": np.uint8, "i64": np.int64, "u64": np.uint64}
CENTRES = [0, 0, 0, 2**53, 2**62, 2**63, 2**64 - 1, -2**53, -2**62, -2**63]


def pick(rng, dt, centre):
    info = np.iinfo(DT[dt])
    if dt in ("i8", "u8"):
        v = rng.randrange(-130, 260)
    else:
        v = centre + rng.randrange(-3, 4)
    return min(max(v, int(info.min)), int(info.max))


def gen(rng):
    while True:
        d1 = rng.choice(["i64", "i64", "u64", "u64", "i8", "u8"])
        d2 = rng.choice(["i64", "i64", "u64", "u64", "i8", "u8"])
        centres = [rng.choice(CENTRES) for _ in range(2)]
        n1 = rng.randrange(0, 13)
        n2 = rng.choice([0, 1, 2, 5, rng.randrange(0, 31), rng.randrange(8, 31)])
        a1 = [pick(rng, d1, rng.choice(centres)) for _ in range(n1)]
        a2 = [pick(rng, d2, rng.choice(centres)) for _ in range(n2)]
        if rng.random() < 0.3 and a1 and n2:
            a2[rng.randrange(n2)] = min(max(rng.choice(a1), int(np.iinfo(DT[d2]).min)), int(np.iinfo(DT[d2]).max))
        kind = rng.choice([None, "sort", "table"])
        rng_ok = not a2 or kind != "table" or max(a2) - min(a2) <= 10**5 or max(a2) - min(a2) > int(np.iinfo(DT[d2]).max)
        if rng_ok:
            break
    invert = rng.random() < 0.3
    line = f"isin {fmt_ints(a1)} {d1} {fmt_ints(a2)} {d2} {kind} {int(invert)}"
    x1 = np.array(a1, dtype=DT[d1])
    x2 = np.array(a2, dtype=DT[d2])
    try:
        out = "OK " + fmt_ints(int(b) for b in np.isin(x1, x2, invert=invert, kind=kind))
    except RuntimeError:
        out = "ERR table"
    return line, out


if __name__ == "__main__":
    main(gen, exe="npdiff_libint")
