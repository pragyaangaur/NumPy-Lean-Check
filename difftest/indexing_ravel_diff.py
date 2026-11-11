"""Differential test for `ravel_multi_index` (compiled_base.c:1140) and `unravel_index` (compiled_base.c:1336) on one point, with modes raise, wrap and clip and orders C and F."""
import numpy as np
from harness import fmt_ints, main

BIG = [2**31, 2**32, 3037000500, 2**62, 2**63 - 1, 4611686018427387904]
MODES = {"r": "raise", "w": "wrap", "c": "clip"}


def pick_dim(rng):
    r = rng.random()
    if r < 0.6:
        return rng.randrange(1, 7)
    if r < 0.7:
        return 0
    if r < 0.82:
        return -rng.randrange(1, 5)
    if r < 0.95:
        return rng.choice(BIG)
    return rng.randrange(-2**63, 2**63)


def pick_val(rng, size):
    r = rng.random()
    if r < 0.4:
        return rng.randrange(-3, max(size, 1) + 3) if 0 <= size < 10**6 else rng.randrange(-3, 50)
    if r < 0.6:
        return rng.randrange(-30, 30)
    e = rng.choice([2**31, 2**32, 2**62, 2**63 - 1, 2**63, 2**64 - 1, size, size - 1, size + 1])
    v = rng.choice([e, -e, e + 1, e - 1])
    return v if -2**63 <= v < 2**64 else 0


def gen_ravel(rng):
    nd = rng.randrange(0, 5)
    dims = [pick_dim(rng) for _ in range(nd)]
    coords = [pick_val(rng, abs(d)) for d in dims]
    modes = [rng.choice("rwc") for _ in dims]
    order = rng.choice("CF")
    line = f"ravel {fmt_ints(coords)} {fmt_ints(dims)} {','.join(modes) if modes else '_'} {order}"
    try:
        v = np.ravel_multi_index(tuple(coords), tuple(dims), mode=tuple(MODES[m] for m in modes), order=order)
        out = f"OK {int(v)}"
    except ValueError as e:
        msg = str(e)
        if "invalid dims" in msg:
            out = "ERR toolarge"
        elif "zero entries" in msg:
            out = "ERR zero"
        elif "invalid entry" in msg:
            out = "ERR invalid"
        else:
            out = "ERR " + msg
    return line, out


def gen_unravel(rng):
    nd = rng.randrange(0, 5)
    dims = [pick_dim(rng) for _ in range(nd)]
    size = 1
    for d in dims:
        size *= d
    if 0 < size and rng.random() < 0.5:
        val = rng.randrange(0, min(size, 2**63))
    else:
        val = pick_val(rng, size)
    order = rng.choice("CF")
    line = f"unravel {val} {fmt_ints(dims)} {order}"
    try:
        r = np.unravel_index(val, tuple(dims), order=order)
        out = f"OK {fmt_ints(r)}"
    except ValueError as e:
        msg = str(e)
        if "too large" in msg:
            out = "ERR toolarge"
        elif "out of bounds" in msg:
            words = msg.split()
            out = f"ERR bounds {words[1]} {words[-1]}"
        else:
            out = "ERR " + msg
    return line, out


def gen(rng):
    return gen_ravel(rng) if rng.random() < 0.5 else gen_unravel(rng)


if __name__ == "__main__":
    main(gen, exe="npdiff_indexing")
