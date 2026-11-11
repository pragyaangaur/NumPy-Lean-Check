"""Differential test for center, ljust, rjust, zfill and expandtabs on the S, U and T kinds (`string_buffer.h:1496-1660`, `strings.py:693-940`, `stringdtype_ufuncs.cpp:1550-1960`)."""
import numpy as np
from harness import main
from strings_common import (BIG_INTS, KINDS, alphabet, arr, big_width, fmt, fmt_res, rand_str, rand_width, run)

JUST = {"c": np.strings.center, "l": np.strings.ljust, "r": np.strings.rjust}


def rand_fill(rng, kind):
    r = rng.random()
    al = alphabet(kind)
    if r < 0.75:
        return [rng.choice(al)]
    if r < 0.85:
        return []
    if r < 0.93:
        return [0]
    return [rng.choice(al), rng.choice(al)]


def gen(rng):
    kind = rng.choice(KINDS)
    op = rng.choice(["just", "just", "zfill", "expandtabs"])
    a = rand_str(rng, kind, 6)
    if op == "zfill" and rng.random() < 0.5:
        a = [rng.choice([43, 45])] + a  # a leading sign
    if op == "just":
        p = rng.choice("clr")
        w = rand_width(rng, kind)
        f = rand_fill(rng, kind)
        out = run(lambda: fmt_res(kind, JUST[p](arr(kind, a, rng), np.int64(w), arr(kind, f, rng))))
        return f"just {kind} {p} {fmt(a)} {w} {fmt(f)}", out
    if op == "zfill":
        w = rand_width(rng, kind)
        out = run(lambda: fmt_res(kind, np.strings.zfill(arr(kind, a, rng), np.int64(w))))
        return f"zfill {kind} {fmt(a)} {w}", out
    r = rng.random()
    ts = rng.randrange(-2, 10) if r < 0.8 else (rng.choice([2**31, 2**32, 2**62, 2**63 - 1, -(2**63)]) if r < 0.9 else rng.choice([100, 1000, 100000]))
    a = [rng.choice([9, 9, 97, 10, 13]) if rng.random() < 0.5 else x for x in a] if rng.random() < 0.5 else a
    out = run(lambda: fmt_res(kind, np.strings.expandtabs(arr(kind, a, rng), np.int64(ts))))
    return f"expandtabs {kind} {fmt(a)} {ts}", out


if __name__ == "__main__":
    main(gen, exe="npdiff_strings")
