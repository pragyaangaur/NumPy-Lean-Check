"""Differential test for `take` (item_selection.c:234), `put` (item_selection.c:384) and `choose` (item_selection.c:1019) with one index and modes raise, wrap and clip.

The wrap mode loops once per multiple of the axis length (see `wrapLoop` in the model), so the generator never sends a wrap case that would need more than 2**22 iterations.
"""
import numpy as np
from harness import main

MODES = {"r": "raise", "w": "wrap", "c": "clip"}
EDGES = [2**31, 2**32, 2**62, 2**63 - 1]


def pick_index(rng, n, unsigned):
    r = rng.random()
    if r < 0.5:
        i = rng.randrange(-2 * n - 3, 2 * n + 4)
    elif r < 0.7:
        i = rng.randrange(-200, 200)
    else:
        e = rng.choice(EDGES)
        i = rng.choice([e, -e, e - 1, -e + 1, -e - 1])
    if unsigned and rng.random() < 0.3:
        i = rng.choice([2**63, 2**63 + 1, 2**64 - 1, 2**64 - max(n, 1), 2**64 - 2**32, 2**63 + rng.randrange(0, 2**63)])
    return i


def wrap_is_slow(i, n):
    i = (i + 2**63) % 2**64 - 2**63
    return n == 0 or abs(i) // max(n, 1) > 2**22


def gen_take(rng):
    n = rng.randrange(0, 12)
    mode = rng.choice("rwc")
    while True:
        i = pick_index(rng, n, True)
        if mode != "w" or not wrap_is_slow(i, n) or n == 0:
            break
    line = f"take {n} {i} {mode}"
    idx = np.array([i], dtype=np.uint64 if i >= 2**63 else np.int64)
    try:
        out = f"OK {int(np.take(np.arange(n), idx, mode=MODES[mode])[0])}"
    except IndexError as e:
        out = "ERR empty" if "empty" in str(e) else "ERR bounds"
    return line, out


def gen_put(rng):
    n = rng.randrange(0, 12)
    mode = rng.choice("rwc")
    nv = rng.choice([0, 1, 1, 1, 2])
    while True:
        i = pick_index(rng, n, False)
        if mode != "w" or not wrap_is_slow(i, n) or n == 0 or nv == 0:
            break
    line = f"put {n} {i} {nv} {mode}"
    a = np.arange(n)
    try:
        np.put(a, np.array([i], dtype=np.int64), np.full(nv, -1), mode=MODES[mode])
        hit = np.flatnonzero(a == -1)
        out = f"OK {int(hit[0])}" if len(hit) else "OK none"
    except IndexError as e:
        out = "ERR empty" if "empty" in str(e) else "ERR bounds"
    return line, out


def gen_choose(rng):
    n = rng.randrange(1, 10)
    mode = rng.choice("rwc")
    while True:
        i = pick_index(rng, n, False)
        if mode != "w" or not wrap_is_slow(i, n):
            break
    line = f"choose {n} {i} {mode}"
    try:
        r = np.choose(np.array([i], dtype=np.int64), [np.array([k]) for k in range(n)], mode=MODES[mode])
        out = f"OK {int(r[0])}"
    except ValueError:
        out = "ERR invalid"
    return line, out


def gen(rng):
    r = rng.random()
    if r < 0.4:
        return gen_take(rng)
    if r < 0.75:
        return gen_put(rng)
    return gen_choose(rng)


if __name__ == "__main__":
    main(gen, exe="npdiff_indexing")
