"""Differential test for Python ints of any size combined with floating point and complex NumPy values under NEP 50.

The three paths `dtype.type(1) + v` (scalarmath.c.src:973, then the `setitem` of the dtype), `np.ones(1, dtype) + v` and `np.asarray(v, dtype)` (the `setitem` of the dtype: arraytypes.c.src:123-150 for half and float, arraytypes.c.src:449-540 for complex, arraytypes.c.src:526 and common/npy_longdouble.c:128 for longdouble) must all give the modelled outcome: the result dtype, whether the value is finite or infinite, and the warning category, or the kind of error. The model prints only that, because floating point values themselves are out of scope. If the three paths disagree, the expected side is `DIFFER ...` and the case fails.

The edges are the limits where an outcome changes: 2**1024 - 2**970 (the first int that `float(v)` rejects), the float32 limit 2**128 - 2**103 with the integers within 2**74 of it (the double rounding window), and the half limit 65520.
"""
import warnings

import numpy as np
from dtype_common import fmt_dtype
from harness import main

DTYPES = list("efdgFDG")
DLIM = 2**1024 - 2**970
F32 = 2**128 - 2**103
OFFSETS = [0, 1, -1, 2, -2, 3, 2**10, -2**10, 2**53, -2**53, 2**69, -2**69, 2**73, -2**73, 2**74 - 1, 2**74, 2**74 + 1,
           -2**74 + 1, -2**74, -2**74 - 1, 2**75, -2**75, 2**100, -2**100, 2**969, -2**969, 2**970, -2**970]
EDGES = [DLIM, F32, 2**128 - 2**104, 2**128, 2**1023, 2**1024, 2**1024 - 1, 2**1025, 65504, 65519, 65520, 65521, 65535, 65536,
         2**24, 2**53, 2**63, 2**63 - 1, 2**64, 0, 1, 2**11, 2**16, 2**127, 2**127 + 2**103, 10**308, 10**309, 10**400]


def outcome(f):
    with warnings.catch_warnings(record=True) as w:
        warnings.simplefilter("always")
        try:
            r = np.asarray(f())
        except OverflowError:
            return "ERR overflow"
        except Exception as e:
            return "ERR OTHER " + type(e).__name__
    v = r.reshape(-1)[0]
    parts = [v.real, v.imag] if r.dtype.kind == "c" else [v]
    cls = "nan" if any(np.isnan(p) for p in parts) else "inf" if any(np.isinf(p) for p in parts) else "fin"
    cats = sorted({x.category.__name__ for x in w})
    return f"OK {fmt_dtype(r.dtype)} {cls} {','.join(cats) if cats else 'none'}"


def gen(rng):
    d = rng.choice(DTYPES)
    r = rng.random()
    if r < 0.4:
        v = rng.choice(EDGES) + rng.choice(OFFSETS) * rng.choice([0, 1, 1, 1])
    elif r < 0.65:
        v = rng.getrandbits(rng.randrange(1, 1100)) + rng.choice([0, 1])
    elif r < 0.72:
        v = rng.randrange(1, 10) * 10 ** rng.randrange(0, 330)
    elif r < 0.85:
        v = rng.choice([65504, 65520, 2**16, 2**24, 2**53]) + rng.randrange(-40, 40)
    else:
        v = rng.randrange(-2**70, 2**70)
    if rng.random() < 0.4:
        v = -v
    t = np.dtype(d).type
    arr = outcome(lambda: np.add(np.ones(1, dtype=d), v))
    sca = outcome(lambda: t(1) + v)
    asr = outcome(lambda: np.asarray(v, dtype=d))
    # np.asarray(v, dtype) does not add one, so its value class is the stored value, and the add keeps it.
    out = arr if arr == sca == asr else f"DIFFER {arr} {sca} {asr}"
    return f"bigint_float {d} {v}", out


if __name__ == "__main__":
    main(gen, exe="npdiff_dtype")
