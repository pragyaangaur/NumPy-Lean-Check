"""Differential test for the section boundaries of `np.array_split` and `np.split` (`lib/_shape_base_impl.py:720` and `781`). The output is the shape of every piece."""
import numpy as np
from harness import fmt_ints, main


def classify(e):
    msg = str(e)
    if isinstance(e, ZeroDivisionError):
        return "ERR zerodiv"
    if isinstance(e, IndexError):
        return "ERR index"
    if "number sections must be larger than 0" in msg:
        return "ERR sections"
    if "equal division" in msg:
        return "ERR notequal"
    return f"UNKNOWN {type(e).__name__}: {msg[:200]}"


def gen(rng):
    nd = rng.choice([0, 1, 1, 1, 2, 2, 3])
    shape = tuple(rng.choice([0, 1, 2, 3, 4, 5, 6, 8, 12]) for _ in range(nd))
    r = rng.random()
    if nd == 0 or r < 0.08:
        axis = rng.choice([nd, nd + 1, -nd - 1, -nd - 2, 0, -1])
    else:
        axis = rng.randrange(-nd, nd)
    N = shape[axis] if -nd <= axis < nd else 4
    if rng.random() < 0.5:
        # An integer number of sections.
        r = rng.random()
        if r < 0.1:
            n = 0
        elif r < 0.2:
            n = -rng.randrange(1, 6)
        elif r < 0.5:
            divs = [d for d in range(1, 13) if N % d == 0]
            n = rng.choice(divs)
        else:
            n = rng.randrange(1, 14)
        secs, token = n, f"c:{n}"
    else:
        k = rng.choice([0, 0, 1, 2, 3, 4, 6])
        pool = [0, 1, 2, 3, N, N + 1, N + 5, -1, -2, -N, -N - 1, -N - 3, 2**40, -2**40, 2**64, -2**64]
        if rng.random() < 0.5:
            ind = sorted(rng.randrange(0, N + 3) for _ in range(k))
        else:
            ind = [rng.choice(pool) if rng.random() < 0.6 else rng.randrange(-N - 2, N + 3) for _ in range(k)]
        secs, token = ind, f"l:{fmt_ints(ind)}"
    a = np.empty(shape, dtype=np.int8)
    shp = fmt_ints(shape)
    out = {}
    for name, f in (("asplit", np.array_split), ("split", np.split)):
        try:
            out[name] = "OK " + ";".join(fmt_ints(p.shape) for p in f(a, secs, axis))
        except (ValueError, IndexError, ZeroDivisionError, OverflowError) as e:
            out[name] = classify(e)
    name = rng.choice(["asplit", "split"])
    return f"{name} {shp} {axis} {token}", out[name]


if __name__ == "__main__":
    main(gen, exe="npdiff_broadcast")
