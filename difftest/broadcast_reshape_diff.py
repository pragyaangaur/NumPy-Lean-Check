"""Differential test for `reshape(..., copy=False)` on strided views, which runs `_reshape_with_copy_arg` and `_attempt_nocopy_reshape` (`_core/src/multiarray/shape.c:225` and `:379`). The strides of the result are compared."""
import numpy as np
from harness import fmt_ints, main
from broadcast_strided import make, strided


def factor(rng, n):
    """A random shape with product n, with ones inserted anywhere."""
    out = []
    while n > 1:
        ds = [d for d in range(2, n + 1) if n % d == 0]
        d = rng.choice(ds)
        out.append(d)
        n //= d
    rng.shuffle(out)
    for _ in range(rng.randrange(0, 3)):
        out.insert(rng.randrange(len(out) + 1), 1)
    return out


def gen(rng):
    dims, strides, dt = strided(rng, allow_zero=rng.random() < 0.1)
    size = int(np.prod(dims)) if dims else 1
    r = rng.random()
    if r < 0.1:
        new = list(dims)
    elif r < 0.85 and size > 0:
        new = factor(rng, size)
    elif size == 0:
        new = [rng.choice([0, 1, 2, 3]) for _ in range(rng.randrange(1, 4))]
        if 0 not in new and rng.random() < 0.8:
            new[rng.randrange(len(new))] = 0
    else:
        new = [rng.choice([1, 2, 3, 4]) for _ in range(rng.randrange(0, 4))]
    order = rng.choice("CF")
    a = make(dims, strides, dt)
    line = f"reshape {fmt_ints(dims)} {fmt_ints(strides)} {dt.itemsize} {fmt_ints(new)} {order}"
    try:
        out = "OK " + fmt_ints(a.reshape(new, order=order, copy=False).strides)
    except ValueError as e:
        msg = str(e)
        out = "ERR copy" if "avoid creating a copy" in msg else ("ERR mismatch" if "cannot reshape" in msg else "UNKNOWN " + msg)
    return line, out


if __name__ == "__main__":
    main(gen, exe="npdiff_broadcast")
