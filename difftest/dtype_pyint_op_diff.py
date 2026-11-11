"""Differential test for NEP 50 handling of a Python int operand: `np.add(np.ones(2, dtype), v)` and `dtype.type(1) + v` must both give the modelled result dtype or both raise OverflowError (abstractdtypes.c:168, arraytypes.c.src:286)."""
import warnings

from dtype_common import fmt_dtype
from harness import main
import numpy as np

NUMERIC = list("?bBhHiIlLqQefdgFDG")
EDGES = [0, 1, -1, 127, 128, -128, -129, 255, 256, 300, 32767, 32768, -32768, -32769, 65535, 65536,
         2**31 - 1, 2**31, -2**31, -2**31 - 1, 2**32 - 1, 2**32, 2**62, 2**63 - 1, 2**63, -2**63, -2**63 - 1,
         2**64 - 1, 2**64, -2**64]


def outcome(f):
    try:
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            return "OK " + fmt_dtype(np.asarray(f()).dtype)
    except OverflowError:
        return "ERR overflow"


def gen(rng):
    d = rng.choice(NUMERIC)
    if rng.random() < 0.7:
        v = rng.choice(EDGES) + rng.choice([0, 0, 0, -1, 1])
    else:
        v = rng.randrange(-2**65, 2**65) >> rng.randrange(0, 66)
    arr = outcome(lambda: np.add(np.ones(2, dtype=d), v))
    sca = outcome(lambda: np.dtype(d).type(1) + v)
    out = arr if arr == sca else f"DIFFER {arr} {sca}"
    return f"pyint_op {d} {v}", out


if __name__ == "__main__":
    main(gen, exe="npdiff_dtype")
