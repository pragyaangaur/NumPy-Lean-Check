"""Differential test for integer power on the scalar path (scalarmath.c.src:244, :1549) and both array loops of `@TYPE@_power` (loops.c.src:510), including negative exponents."""
import numpy as np
from harness import fmt_ints, main
from intarith_common import NAMES, as_numpy, ints, operands, run, value


def base(rng, name):
    r = rng.random()
    if r < 0.4:
        return rng.choice([0, 1, 2, 3, -1, -2, 1, 1]) if name.startswith("i") else rng.choice([0, 1, 2, 3, 1])
    return value(rng, name)


def exponent(rng, name):
    r = rng.random()
    if r < 0.5:
        return rng.choice([0, 1, 2, 3, 4, 5, 7, 8, 15, 16, 31, 32, 63, 64, 65])
    if r < 0.6 and name.startswith("i"):
        return rng.choice([-1, -2, -128])
    return value(rng, name)


def gen(rng):
    name = rng.choice(NAMES)
    path = rng.choice(["scalar", "array", "bcast"])
    xs, ys = operands(rng, name, path, base, exponent)
    if path == "array" and xs and rng.random() < 0.7 and name.startswith("i"):
        # Keep most array cases free of negative exponents so that values are compared too.
        ys = [abs(y) if y != -2**(int(name[1:]) - 1) else 0 for y in ys]
    line = f"pow {name} {path} {fmt_ints(xs)} {fmt_ints(ys)}"
    a, b = as_numpy(name, path, xs, ys)
    r, flags, err = run(lambda: a ** b if path == "scalar" else np.power(a, b))
    if err is not None:
        if isinstance(err, ValueError) and "negative integer powers" in str(err):
            return line, "ERR negexp"
        return line, f"ERR {type(err).__name__}"
    return line, f"OK {fmt_ints(ints(r))} {flags}"


if __name__ == "__main__":
    main(gen, exe="npdiff_intarith")
