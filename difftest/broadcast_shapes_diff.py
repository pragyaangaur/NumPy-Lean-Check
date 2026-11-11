"""Differential test for `np.broadcast_shapes` (`lib/_stride_tricks_impl.py:541`), which runs `PyArray_Broadcast` (`_core/src/multiarray/iterators.c:1147`) on arrays of item size 0, in chunks of 64 arguments."""
import numpy as np
from harness import fmt_ints, main
from broadcast_common import classify, dim


def shape(rng, nd):
    return tuple(dim(rng) for _ in range(nd))


def gen(rng):
    r = rng.random()
    if r < 0.6:
        # A few shapes built around a common target so that many cases succeed.
        n = rng.randrange(0, 5)
        target = [rng.choice([1, 2, 3, 0, 4]) for _ in range(rng.randrange(0, 5))]
        shapes = []
        for _ in range(n):
            if rng.random() < 0.7:
                k = rng.randrange(0, len(target) + 1)
                s = [t if rng.random() < 0.7 else 1 for t in target[len(target) - k:]]
                if rng.random() < 0.15 and s:
                    s[rng.randrange(len(s))] = dim(rng, 0.4)
                shapes.append(tuple(s))
            else:
                shapes.append(shape(rng, rng.randrange(0, 5)))
    elif r < 0.75:
        # Huge entries, to reach the overflow checks.
        n = rng.randrange(1, 4)
        shapes = []
        for _ in range(n):
            s = [rng.choice([1, 2, 0, 2**31, 2**32, 2**61, 2**62, 2**63 - 1, 3, 4]) for _ in range(rng.randrange(1, 4))]
            shapes.append(tuple(s))
    elif r < 0.8:
        # Too many dimensions in one argument.
        shapes = [tuple([1] * rng.choice([31, 32, 33, 40, 63, 64, 65, 66]))]
        if rng.random() < 0.5:
            shapes.append((2,))
    else:
        # More than 64 arguments, mostly trivial, with a few real shapes anywhere.
        n = rng.randrange(60, 140)
        shapes = [rng.choice([(), (1,), (1, 1)]) for _ in range(n)]
        for _ in range(rng.randrange(0, 4)):
            shapes[rng.randrange(n)] = rng.choice([(2,), (3,), (2, 1), (1, 3), (0,), (2**61,), (2**60,), (2**59, 1), (0, 2**62, 2), (2**62, 2, 0), (2**63 - 1,)])
    line = "bshapes" + "".join(" " + fmt_ints(s) for s in shapes)
    try:
        out = "OK " + fmt_ints(np.broadcast_shapes(*shapes))
    except (ValueError, OverflowError, TypeError, RuntimeError) as e:
        out = classify(e)
    return line, out


if __name__ == "__main__":
    main(gen, exe="npdiff_broadcast")
