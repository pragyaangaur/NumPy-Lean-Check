"""Differential test for the width normalisation of `np.pad` in constant mode (`_as_pairs` at `lib/_arraypad_impl.py:471` and the shape logic of `pad` at `547`). The output is the shape of the padded float64 array, or the error kind."""
import itertools
import numpy as np
from harness import fmt_ints, main

VALS = [0, 1, 2, 3, 1, 2, 0, 4]
BIGV = [2**60, 2**61, 2**62, 2**62 + 1, 2**63 - 1, 2**63 - 2, 2**63 - 1, 2**63 - 3, 2**63, 2**64, -2**63, -2**63 - 1, -2**60, -1, -2]


def classify(e):
    msg = str(e)
    if isinstance(e, TypeError):
        return "ERR type"
    if "negative dimensions" in msg:
        return "ERR negdim"
    if "could not broadcast input array" in msg:
        return "ERR assign"
    if "negative values" in msg:
        return "ERR negative"
    if "more dimensions than allowed" in msg or "could not be broadcast" in msg:
        return "ERR broadcast"
    if "Maximum allowed dimension exceeded" in msg:
        return "ERR conv"
    if "too big" in msg:
        return "ERR toobig"
    return f"UNKNOWN {type(e).__name__}: {msg[:200]}"


def nest(rng, shape, big):
    if not shape:
        if big and rng.random() < 0.3:
            return rng.choice(BIGV)
        if rng.random() < 0.02:
            return -rng.randrange(1, 3)
        return rng.choice(VALS)
    return [nest(rng, shape[1:], big) for _ in range(shape[0])]


def flat(x):
    if isinstance(x, list):
        return [y for e in x for y in flat(e)]
    return [x]


def gen(rng):
    import warnings
    warnings.simplefilter("ignore")
    nd = rng.choice([0, 1, 1, 2, 2, 2, 3])
    shape = tuple(rng.choice([0, 1, 2, 3, 4]) for _ in range(nd))
    # Width arrays of shapes that hit every branch of `_as_pairs`.
    pshape = rng.choice([(), (1,), (2,), (1, 1), (1, 2), (2, 1), (2, 2), (nd, 2), (nd, 1), (nd,), (3,), (2, 3), (3, 2), (1, 1, 1), (2, 1, 2), (0,), (1, 0), (nd, 2), (nd, 2), (nd, 2), (nd, 2)])
    big = rng.random() < 0.25
    lst = nest(rng, pshape, big)
    if rng.random() < 0.04:
        lst = rng.choice([0, 1, 2, 5])
    ps = np.array(lst).shape if not isinstance(lst, int) else ()
    data = flat(lst)
    a = np.zeros(shape)
    try:
        out = "OK " + fmt_ints(np.pad(a, lst).shape)
    except Exception as e:
        out = classify(e)
    return f"pad {fmt_ints(shape)} {fmt_ints(ps)} {fmt_ints(data)}", out


if __name__ == "__main__":
    main(gen, exe="npdiff_broadcast")
