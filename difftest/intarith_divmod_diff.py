"""Differential test for integer floor_divide, remainder and divmod on the scalar path (scalarmath.c.src:175, :205, :463) and the array paths (loops_arithmetic.dispatch.c.src:346, loops_modulo.dispatch.c.src:571, :614), with the warnings they raise."""
import operator

import numpy as np
from harness import fmt_ints, main
from intarith_common import NAMES, as_numpy, bounds, ints, operands, run, value

OPS = {"floor_divide": (operator.floordiv, np.floor_divide), "remainder": (operator.mod, np.remainder), "divmod": (divmod, np.divmod)}


def dividend(rng, name):
    lo, _ = bounds(name)
    return lo if rng.random() < 0.15 else value(rng, name)


def divisor(rng, name):
    r = rng.random()
    if r < 0.15:
        return 0
    if r < 0.3 and name.startswith("i"):
        return -1
    return value(rng, name)


def gen(rng):
    op = rng.choice(list(OPS))
    name = rng.choice(NAMES)
    path = rng.choice(["scalar", "array", "bcast"])
    xs, ys = operands(rng, name, path, dividend, divisor)
    line = f"div {op} {name} {path} {fmt_ints(xs)} {fmt_ints(ys)}"
    a, b = as_numpy(name, path, xs, ys)
    pyop, ufunc = OPS[op]
    r, flags, err = run(lambda: pyop(a, b) if path == "scalar" else ufunc(a, b))
    if err is not None:
        return line, f"ERR {type(err).__name__}"
    if op == "divmod":
        return line, f"OK {fmt_ints(ints(r[0]))} {fmt_ints(ints(r[1]))} {flags}"
    return line, f"OK {fmt_ints(ints(r))} {flags}"


if __name__ == "__main__":
    main(gen, exe="npdiff_intarith")
