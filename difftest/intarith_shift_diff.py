"""Differential test for left_shift and right_shift (npy_math_internal.h.src:685, :695) on the scalar operators `<<` and `>>` and the ufuncs, with shift amounts at, past and below the bit width."""
import operator

import numpy as np
from harness import fmt_ints, main
from intarith_common import NAMES, as_numpy, bounds, ints, operands, run, value


def amount(rng, name):
    lo, hi = bounds(name)
    bits = int(name[1:])
    r = rng.random()
    if r < 0.6:
        v = rng.choice([0, 1, bits - 1, bits, bits + 1, 2 * bits, rng.randrange(0, bits)])
    elif r < 0.75 and lo < 0:
        v = rng.choice([-1, -bits, lo])
    else:
        v = value(rng, name)
    return v if lo <= v <= hi else value(rng, name)


def gen(rng):
    op = rng.choice(["left_shift", "right_shift"])
    name = rng.choice(NAMES)
    path = rng.choice(["scalar", "array", "bcast"])
    xs, ys = operands(rng, name, path, value, amount)
    line = f"shift {op} {name} {path} {fmt_ints(xs)} {fmt_ints(ys)}"
    a, b = as_numpy(name, path, xs, ys)
    if path == "scalar":
        f = operator.lshift if op == "left_shift" else operator.rshift
    else:
        f = np.left_shift if op == "left_shift" else np.right_shift
    r, flags, err = run(lambda: f(a, b))
    if err is not None:
        return line, f"ERR {type(err).__name__}"
    return line, f"OK {fmt_ints(ints(r))} {flags}"


if __name__ == "__main__":
    main(gen, exe="npdiff_intarith")
