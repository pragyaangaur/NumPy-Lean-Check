"""Differential test for integer absolute and sign. The scalar path of absolute is the builtin `abs` on a NumPy scalar (scalarmath.c.src:610), and the array path is the ufunc loop (loops_autovec.dispatch.c.src:120, :220)."""
import numpy as np
from harness import fmt_ints, main
from intarith_common import NAMES, TYPES, bounds, ints, length, run, value


def operand(rng, name):
    lo, _ = bounds(name)
    return lo if rng.random() < 0.2 else value(rng, name)


def gen(rng):
    op = rng.choice(["absolute", "sign"])
    name = rng.choice(NAMES)
    path = rng.choice(["scalar", "array"])
    t = TYPES[name]
    n = 1 if path == "scalar" else length(rng)
    xs = [operand(rng, name) for _ in range(n)]
    line = f"un {op} {name} {path} {fmt_ints(xs)}"
    if path == "scalar":
        x = t(xs[0])
        f = (lambda: abs(x)) if op == "absolute" else (lambda: np.sign(x))
    else:
        x = np.array(xs, dtype=t)
        f = (lambda: np.absolute(x)) if op == "absolute" else (lambda: np.sign(x))
    r, flags, err = run(f)
    if err is not None:
        return line, f"ERR {type(err).__name__}"
    return line, f"OK {fmt_ints(ints(r))} {flags}"


if __name__ == "__main__":
    main(gen, exe="npdiff_intarith")
