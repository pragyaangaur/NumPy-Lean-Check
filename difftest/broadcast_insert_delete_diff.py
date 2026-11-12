"""Differential test for the index handling of `np.delete` and `np.insert` (`lib/_function_base_impl.py:5222` and `5406`) on 0-d and 1-d integer arrays. The output is the content of the result."""
import numpy as np
from harness import fmt_ints, main


def classify(e):
    if isinstance(e, np.exceptions.AxisError):
        return "ERR axis"
    if isinstance(e, IndexError):
        return "ERR index"
    if isinstance(e, ValueError):
        return "ERR value"
    if isinstance(e, AttributeError):
        return "ERR attr"
    return f"UNKNOWN {type(e).__name__}: {str(e)[:200]}"


def opt(x):
    return "n" if x is None else str(x)


def idx(rng, N):
    r = rng.random()
    if r < 0.04:
        return rng.choice([2**31, -2**31, 2**40, -2**40, 2**63 - 1, -2**63, 2**63, 2**64, -2**64])
    if r < 0.25:
        return rng.choice([N, N + 1, N + 2, -N, -N - 1, -N - 2, -N - 4])
    return rng.randrange(-N - 1, N + 2) if N else rng.randrange(-2, 3)


def make_obj(rng, N, for_insert):
    kind = rng.choice(["i", "i", "s", "s", "l", "l", "l", "m", "q", "e"])
    if kind == "i":
        v = idx(rng, N)
        return f"i:{v}", v
    if kind == "s":
        def b():
            return None if rng.random() < 0.25 else idx(rng, N)
        step = rng.choice([None, None, 1, 2, 3, -1, -2, 0, 5, -3, 2**40, -2**40])
        a, b2 = b(), b()
        return f"s:{opt(a)}:{opt(b2)}:{opt(step)}", slice(a, b2, step)
    if kind == "l":
        k = rng.choice([1, 1, 2, 2, 3, 4])
        l = [idx(rng, N) for _ in range(k)]
        return f"l:{fmt_ints(l)}", l
    if kind == "e":
        return "l:_", []
    n = N if rng.random() < 0.7 else max(0, N + rng.choice([-2, -1, 1, 2, 4]))
    bits = [rng.random() < 0.4 for _ in range(n)]
    s = "".join("1" if b else "0" for b in bits) or "_"
    if kind == "m":
        return f"m:{s}", np.array(bits, dtype=bool)
    if not bits:
        return "l:_", []
    return f"q:{s}", bits


def gen(rng):
    if rng.random() < 0.1:
        shape = ()
        N = 0
    else:
        N = rng.choice([0, 1, 1, 2, 3, 3, 4, 5, 6, 7])
        shape = (N,)
    ax = rng.choice(["none"] * 5 + [0] * 4 + [-1] * 3 + [1, -2])
    axis = None if ax == "none" else ax
    a = np.arange(int(np.prod(shape)))
    a = a.reshape(shape)
    N_eff = a.size if axis is None else (N if shape else 0)
    if axis is None and not shape:
        N_eff = 1
    token, obj = make_obj(rng, N_eff, False)
    shp = fmt_ints(shape)
    if rng.random() < 0.5:
        try:
            out = "OK " + fmt_ints(np.delete(a, obj, axis=axis))
        except Exception as e:
            out = classify(e)
        return f"delete {shp} {ax} {token}", out
    vk = rng.random()
    if vk < 0.35:
        vals, scalar = [100], True
    else:
        vals = [100 + j for j in range(rng.choice([0, 1, 1, 2, 3, 4]))]
        scalar = False
    values = vals[0] if scalar else vals
    try:
        out = "OK " + fmt_ints(np.insert(a, obj, values, axis=axis))
    except Exception as e:
        out = classify(e)
    return f"insert {shp} {ax} {token} {fmt_ints(vals)}", out


if __name__ == "__main__":
    main(gen, exe="npdiff_broadcast")
