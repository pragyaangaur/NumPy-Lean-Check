"""Differential test for `np.arange` with Python integer arguments (`PyArray_ArangeObj`, ctors.c:3291): the dtype, the length and the values.

The length is computed through a double, so the generator mixes small values with values near `2**53`, `2**63` and `2**64` and builds many cases where `stop` is a few steps past `start`, which keeps the result short even when the values are large. A case runs only when the result has at most 4096 elements or when the size check of the array constructor rejects it before any allocation.
"""
import math

import numpy as np
from harness import fmt_ints, main

EDGE = [0, 1, 2, 3, 7, 100, 255, 256, 2**31 - 1, 2**31, 2**32, 2**53 - 1, 2**53, 2**53 + 1, 2**62, 2**63 - 2, 2**63 - 1,
        2**63, 2**63 + 1, 2**64 - 1, 2**64, 2**64 + 1, 2**80]
STEPS = [1, 1, 1, 2, 3, 5, 7, 255, 2**31, 2**32 + 1, 2**52, 2**53, 2**53 + 1, 2**60, 2**62, 2**63, 2**64]
DTYPES = [None, None, None, None, "b", "i8", "u8", "i16", "u16", "i32", "u32", "i64", "u64", "f8", "O"]
CODE = {"bool": "b", "int8": "i8", "uint8": "u8", "int16": "i16", "uint16": "u16", "int32": "i32", "uint32": "u32",
        "int64": "i64", "uint64": "u64", "float64": "f8", "object": "O"}
NPDT = {"b": np.bool_, "i8": np.int8, "u8": np.uint8, "i16": np.int16, "u16": np.uint16, "i32": np.int32,
        "u32": np.uint32, "i64": np.int64, "u64": np.uint64, "f8": np.float64, "O": object}


def signed(rng, pool):
    v = rng.choice(pool)
    if rng.random() < 0.3:
        v += rng.randrange(-3, 4)
    return -v if rng.random() < 0.4 else v


def safe(start, stop, step, itemsize):
    """True when the call cannot allocate more than a small array."""
    if step == 0:
        return True
    try:
        q = (stop - start) / step
    except OverflowError:
        return True
    c = math.ceil(q)
    if c < -2**63 or c > 2**63:
        return True
    n = max(0, min(c, 2**63 - 1))
    return n <= 4096 or n * itemsize > 2**63 - 1


def gen(rng):
    while True:
        start = signed(rng, EDGE) if rng.random() < 0.7 else rng.randrange(-50, 50)
        r = rng.random()
        step = None
        if r < 0.15:
            stop = signed(rng, EDGE)
        elif r < 0.25:
            stop = rng.randrange(-60, 60)
        else:
            step = signed(rng, STEPS) if rng.random() < 0.9 else rng.choice([0, 10**400, -10**400])
            stop = start + rng.randrange(-3, 12) * step + rng.choice([-1, 0, 0, 1, rng.randrange(-5, 6)])
        if step is None and rng.random() < 0.5:
            step = signed(rng, STEPS) if rng.random() < 0.9 else 0
        dt = rng.choice(DTYPES)
        if dt == "f8" and max(abs(start), abs(stop)) > 2**200:
            continue
        itemsize = 8 if dt is None else np.dtype(NPDT[dt]).itemsize
        if safe(start, stop, 1 if step is None else step, itemsize):
            break
    line = f"arange {start} {stop} {'N' if step is None else step} {'N' if dt is None else dt}"
    try:
        kw = {} if dt is None else {"dtype": NPDT[dt]}
        a = np.arange(start, stop, step, **kw) if step is not None else np.arange(start, stop, **kw)
        vals = fmt_ints(int(v) for v in a) if len(a) <= 64 else "-"
        out = f"OK {CODE[a.dtype.name]} {len(a)} {vals}"
    except ZeroDivisionError:
        out = "ERR zerodiv"
    except OverflowError:
        out = "ERR setitem"
    except TypeError as e:
        out = "ERR boolfill" if "booleans" in str(e) else "ERR type " + str(e)
    except ValueError as e:
        msg = str(e)
        if "Maximum allowed" in msg:
            out = "ERR maxsize"
        elif "too big" in msg:
            out = "ERR toobig"
        else:
            out = "ERR value " + msg
    return line, out


if __name__ == "__main__":
    main(gen, exe="npdiff_libint")
