"""Differential test for integer gcd and lcm (loops.c.src:564, :583 with npy_math_internal.h.src:630-668) on NumPy scalars and arrays."""
import numpy as np
from harness import fmt_ints, main
from intarith_common import NAMES, as_numpy, bounds, ints, operands, run, value


def operand(rng, name):
    lo, hi = bounds(name)
    r = rng.random()
    if r < 0.15:
        return lo
    if r < 0.3:
        # Products of small primes give large gcds and lcms that overflow.
        v = 1
        for _ in range(rng.randrange(1, 12)):
            v *= rng.choice([2, 3, 5, 7, 11, 13])
        v = v if lo == 0 or rng.random() < 0.5 else -v
        return v if lo <= v <= hi else value(rng, name)
    return value(rng, name)


def gen(rng):
    op = rng.choice(["gcd", "lcm"])
    name = rng.choice(NAMES)
    path = rng.choice(["scalar", "array", "bcast"])
    xs, ys = operands(rng, name, path, operand, operand)
    line = f"gl {op} {name} {path} {fmt_ints(xs)} {fmt_ints(ys)}"
    a, b = as_numpy(name, path, xs, ys)
    ufunc = np.gcd if op == "gcd" else np.lcm
    r, flags, err = run(lambda: ufunc(a, b))
    if err is not None:
        return line, f"ERR {type(err).__name__}"
    return line, f"OK {fmt_ints(ints(r))} {flags}"


if __name__ == "__main__":
    main(gen, exe="npdiff_intarith")
