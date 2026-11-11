"""Differential test for `np.result_type` (multiarraymodule.c:3624 and convert_datatype.c:1618) with one to four arguments drawn from dtypes and the Python scalars of NEP 50.

Each token stands for one Python object, so that the skip of repeated objects at multiarraymodule.c:3645 sees the same thing on both sides.
"""
from dtype_common import fmt_dtype, rand_token, to_dtype
from harness import main
import numpy as np

PY = {"Pi": 7, "Pf": 1.5, "Pc": 2j}


def obj(tok, cache):
    if tok in PY:
        return PY[tok]
    if tok not in cache:
        cache[tok] = to_dtype(tok)
    return cache[tok]


def gen(rng):
    n = rng.choice([1, 2, 2, 3, 3, 3, 4, 4])
    toks = []
    for _ in range(n):
        r = rng.random()
        if r < 0.25:
            toks.append(rng.choice(list(PY)))
        elif toks and r < 0.32:
            toks.append(toks[-1])
        else:
            toks.append(rand_token(rng, strings=0.25))
    cache = {}
    try:
        out = "OK " + fmt_dtype(np.result_type(*[obj(t, cache) for t in toks]))
    except TypeError:
        out = "ERR promotion"
    return "result_type " + " ".join(toks), out


if __name__ == "__main__":
    main(gen, exe="npdiff_dtype")
