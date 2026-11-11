"""Differential test for integer multiply on the scalar operator (scalarmath.c.src:122, :149), which warns on overflow, and on arrays (loops_autovec.dispatch.c.src:60), which does not. The properties compare it with power."""
import operator

import numpy as np
from harness import fmt_ints, main
from intarith_common import NAMES, as_numpy, ints, operands, run, value


def gen(rng):
    name = rng.choice(NAMES)
    path = rng.choice(["scalar", "array", "bcast"])
    xs, ys = operands(rng, name, path, value, value)
    line = f"mul {name} {path} {fmt_ints(xs)} {fmt_ints(ys)}"
    a, b = as_numpy(name, path, xs, ys)
    r, flags, err = run(lambda: operator.mul(a, b) if path == "scalar" else np.multiply(a, b))
    if err is not None:
        return line, f"ERR {type(err).__name__}"
    return line, f"OK {fmt_ints(ints(r))} {flags}"


if __name__ == "__main__":
    main(gen, exe="npdiff_intarith")
