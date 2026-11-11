"""Differential test for `np.packbits` and `np.unpackbits` (compiled_base.c:1760 and 1865) on tiny arrays.

Shapes have up to three dimensions with lengths up to 19, so that both full groups of eight and short tails occur. The axis is None, in range or out of range, the bit order is big or little, and `count` of `unpackbits` is None, positive, zero or negative. A few empty arrays with a huge first dimension check the wrapped multiplication `outdims[axis] *= 8`.
"""
import numpy as np
from harness import fmt_ints, main

HUGE = [2**60, 2**61, 2**61 + 1, 2**62, 2**63 - 1]


def pick_shape(rng):
    if rng.random() < 0.05:
        return []
    nd = rng.choice([1, 1, 2, 2, 3])
    return [rng.choice([0, 1, 2, 3, 7, 8, 9, 16, 17, rng.randrange(0, 20)]) for _ in range(nd)]


def fmt_result(a, src=None):
    """The contents of an `unpackbits` result for an empty input and a non-empty output are uninitialised memory, printed as `?`. The bug record libint-unpackbits-empty-count-uninitialized covers it."""
    if src is not None and src.size == 0 and a.size > 0:
        return f"OK {fmt_ints(a.shape)} ?"
    return f"OK {fmt_ints(a.shape)} {fmt_ints(a.ravel())}"


def gen(rng):
    axis = rng.choice([None, None, None, 0, 0, 0, 1, 1, -1, -1, 2, -2, 3, -4])
    if rng.random() < 0.5:
        shape = pick_shape(rng)
        size = int(np.prod(shape)) if shape else 1
        kind = rng.choice(["int"] * 9 + ["float"])
        dt = rng.choice([np.int8, np.int64, np.uint8, np.bool_]) if kind == "int" else np.float64
        data = [rng.choice([0, 0, 1, -1, 2, 128, 256]) if rng.random() < 0.8 else 0 for _ in range(size)]
        a = np.array(data, dtype=np.int64).astype(dt).reshape(shape)
        flat = [0 if v == 0 else 1 for v in a.ravel().tolist()]
        order = rng.choice(["big", "little"])
        line = f"pack {'S' if not shape else fmt_ints(shape)} {fmt_ints(flat)} {kind} {'N' if axis is None else axis} {order}"
        try:
            out = fmt_result(np.packbits(a, axis=axis, bitorder=order))
        except TypeError:
            out = "ERR type"
        except np.exceptions.AxisError:
            out = "ERR axis"
        return line, out
    if rng.random() < 0.05:
        shape = [rng.choice(HUGE), 0]
        axis = rng.choice([0, 0, None])
    else:
        shape = pick_shape(rng)
    size = int(np.prod(shape)) if shape else 1
    kind = "u8" if rng.random() < 0.95 else "i8"
    data = [rng.randrange(0, 256) for _ in range(size)]
    a = np.array(data, dtype=np.uint8).reshape(shape)
    if kind == "i8":
        a = a.astype(np.int8)
    count = rng.choice([None, None, 0, 1, 5, 8, 13, 30, -1, -3, -8, -9, -20])
    order = rng.choice(["big", "little"])
    line = (f"unpack {'S' if not shape else fmt_ints(shape)} {fmt_ints(data)} {kind} {'N' if axis is None else axis} "
            f"{'N' if count is None else count} {order[0]}")
    try:
        out = fmt_result(np.unpackbits(a, axis=axis, count=count, bitorder=order), a)
    except TypeError:
        out = "ERR type"
    except np.exceptions.AxisError:
        out = "ERR axis"
    except ValueError as e:
        out = "ERR count" if "-count" in str(e) else ("ERR negdim" if "negative dimensions" in str(e) else "ERR " + str(e))
    return line, out


if __name__ == "__main__":
    main(gen, exe="npdiff_libint")
