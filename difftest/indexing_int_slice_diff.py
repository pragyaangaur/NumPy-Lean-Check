"""Differential test for integer indices (mapping.c:373, check_and_adjust_index in common.h:167) and slices (mapping.c:898, PySlice_GetIndicesEx) on one axis.

The array is an `as_strided` view of shape (n, 1) or (n,) with byte strides over a one-byte buffer, so that n can be as large as 2**63 - 1. Indexing only builds a view and never reads memory, and the start and step of the view are read back from its data pointer and strides.
"""
import numpy as np
from numpy.lib.stride_tricks import as_strided
from harness import main

BUF = np.zeros(1, dtype=np.uint8)
BASE = BUF.__array_interface__["data"][0]
EDGES = [2**31, 2**32, 2**62, 2**63 - 1, 2**63, 2**64 - 1, 2**64, 2**80, 10**30]


def pick_n(rng):
    r = rng.random()
    if r < 0.5:
        return rng.randrange(0, 12)
    if r < 0.7:
        return rng.randrange(0, 1000)
    return rng.choice([2**31 - 1, 2**31, 2**32, 2**62, 2**63 - 2, 2**63 - 1, rng.randrange(0, 2**63)])


def pick_index(rng, n):
    r = rng.random()
    if r < 0.4:
        return rng.randrange(-n - 3, n + 3) if n < 10**6 else rng.randrange(-20, 20)
    if r < 0.6:
        return rng.choice([n, n - 1, -n, -n - 1, n + 1, -n + 1])
    if r < 0.9:
        e = rng.choice(EDGES)
        return rng.choice([e, -e, e - 1, -e + 1, e + 1, -e - 1])
    return rng.randrange(-2**65, 2**65)


def gen_int(rng):
    n = pick_n(rng)
    i = pick_index(rng, n)
    line = f"int_index {n} {i}"
    arr = as_strided(BUF, shape=(n, 1), strides=(1, 0))
    try:
        v = arr[i]
        out = f"OK {v.__array_interface__['data'][0] - BASE}"
    except OverflowError:
        out = "ERR overflow"
    except IndexError as e:
        out = "ERR bounds" if "out of bounds" in str(e) else "ERR type"
    return line, out


def pick_bound(rng, n):
    if rng.random() < 0.2:
        return None
    return pick_index(rng, n)


def gen_slice(rng):
    n = pick_n(rng)
    a, b = pick_bound(rng, n), pick_bound(rng, n)
    r = rng.random()
    if r < 0.15:
        s = None
    elif r < 0.25:
        s = 0
    elif r < 0.75:
        s = rng.choice([1, 2, 3, -1, -2, -3, 5, -7])
    else:
        e = rng.choice(EDGES + [n, n + 1, n - 1] if n > 1 else EDGES)
        s = rng.choice([e, -e, e - 1, -e + 1, -e - 1])
    fmt = lambda x: "N" if x is None else str(x)
    line = f"slice {n} {fmt(a)} {fmt(b)} {fmt(s)}"
    arr = as_strided(BUF, shape=(n,), strides=(1,))
    try:
        v = arr[a:b:s]
        out = f"OK {v.__array_interface__['data'][0] - BASE} {v.strides[0]} {v.shape[0]}"
    except ValueError as e:
        out = "ERR step0" if "zero" in str(e) else "ERR other"
    return line, out


def gen(rng):
    return gen_int(rng) if rng.random() < 0.4 else gen_slice(rng)


if __name__ == "__main__":
    main(gen, exe="npdiff_indexing")
