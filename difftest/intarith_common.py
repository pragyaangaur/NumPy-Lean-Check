"""Shared pieces of the integer arithmetic differential tests: the dtypes, an edge-biased value generator and a runner that records warnings as flags."""
import warnings

import numpy as np

TYPES = {
    "i8": np.int8, "i16": np.int16, "i32": np.int32, "i64": np.int64,
    "u8": np.uint8, "u16": np.uint16, "u32": np.uint32, "u64": np.uint64,
}
NAMES = list(TYPES)


def bounds(name):
    info = np.iinfo(TYPES[name])
    return int(info.min), int(info.max)


def value(rng, name):
    """Draw one value of the dtype, biased toward the edges."""
    lo, hi = bounds(name)
    r = rng.random()
    if r < 0.25:
        c = [lo, hi, lo + 1, hi - 1, 0, 1, 2, 3, -1, -2, -3, 7, 8, 64, 100, 127, 128, 255, 256]
        v = rng.choice(c)
    elif r < 0.45:
        k = rng.choice([7, 8, 15, 16, 31, 32, 62, 63])
        v = rng.choice([1, -1]) * (2**k) + rng.choice([-1, 0, 1])
    elif r < 0.75:
        v = rng.randrange(-20, 21)
    else:
        v = rng.randrange(lo, hi + 1)
    if lo <= v <= hi:
        return v
    # Out of range draws wrap into the type, so unsigned types see values near the maximum.
    return (v - lo) % (hi - lo + 1) + lo


def length(rng):
    return rng.choice([0, 1, 1, 2, 3, 4, rng.randrange(0, 40)])


def flag_names(caught):
    out = set()
    for w in caught:
        msg = str(w.message)
        if "divide by zero" in msg:
            out.add("divbyzero")
        elif "overflow" in msg:
            out.add("overflow")
        elif "invalid" in msg:
            out.add("invalid")
        else:
            out.add("other")
    return ",".join(sorted(out)) if out else "_"


def run(f):
    """Call `f` with every floating point error set to warn and return `(result, flags, error)`."""
    with warnings.catch_warnings(record=True) as caught, np.errstate(all="warn"):
        warnings.simplefilter("always")
        try:
            r = f()
            err = None
        except Exception as e:  # the outcome string records the error class
            r = None
            err = e
    return r, flag_names(caught), err


def operands(rng, name, path, xgen, ygen):
    """Draw the operand lists for a path: one value each for `scalar`, equal lengths for `array`, one divisor for `bcast`."""
    if path == "scalar":
        return [xgen(rng, name)], [ygen(rng, name)]
    n = length(rng)
    xs = [xgen(rng, name) for _ in range(n)]
    if path == "bcast":
        return xs, [ygen(rng, name)]
    return xs, [ygen(rng, name) for _ in range(n)]


def as_numpy(name, path, xs, ys):
    t = TYPES[name]
    if path == "scalar":
        return t(xs[0]), t(ys[0])
    a = np.array(xs, dtype=t)
    b = np.array(ys[0], dtype=t) if path == "bcast" else np.array(ys, dtype=t)
    return a, b


def ints(r):
    return [int(v) for v in np.ravel(np.asarray(r))]
