"""Differential test for axis arguments: `np.moveaxis` (`_core/numeric.py:1536`), `np.transpose` through `PyArray_Transpose` (`_core/src/multiarray/shape.c:677`) and `ndarray.squeeze(axis=...)` through `PyArray_ConvertMultiAxis` (`_core/src/multiarray/conversion_utils.c:368`)."""
import numpy as np
from harness import fmt_ints, main
from broadcast_common import classify

EDGE = [2**31 - 1, 2**31, -2**31, -2**31 - 1, 2**32, 2**32 + 1, -2**32, -2**32 + 1, 2**33 + 2, 2**63 - 1, 2**63, -2**63]


def axis(rng, ndim):
    r = rng.random()
    if r < 0.08:
        return rng.choice(EDGE)
    if r < 0.18:
        return rng.choice([ndim, ndim + 1, -ndim - 1, -ndim - 2])
    if ndim == 0:
        return rng.choice([0, -1])
    return rng.randrange(-ndim, ndim)


def gen(rng):
    ndim = rng.randrange(0, 6)
    kind = rng.choice(["moveaxis", "transpose", "squeeze"])
    if kind == "moveaxis":
        a = np.empty(tuple(range(2, ndim + 2)), dtype=np.int8)
        k = rng.randrange(0, ndim + 1)
        src = [axis(rng, ndim) for _ in range(k)]
        dst = [axis(rng, ndim) for _ in range(k if rng.random() < 0.9 else rng.randrange(0, ndim + 1))]
        line = f"moveaxis {ndim} {fmt_ints(src)} {fmt_ints(dst)}"
        try:
            out = "OK " + fmt_ints(d - 2 for d in np.moveaxis(a, src, dst).shape)
        except Exception as e:
            out = classify(e)
    elif kind == "transpose":
        a = np.empty(tuple(range(2, ndim + 2)), dtype=np.int8)
        n = ndim if rng.random() < 0.9 else rng.randrange(0, ndim + 2)
        perm = list(range(n))
        rng.shuffle(perm)
        axes = [p if rng.random() < 0.6 else (p - ndim if rng.random() < 0.5 else axis(rng, ndim)) for p in perm]
        if rng.random() < 0.15 and axes:
            # Shift an axis by a multiple of 2**32.
            i = rng.randrange(len(axes))
            axes[i] += rng.choice([2**32, -2**32, 2**33, 3 * 2**32])
        line = f"transpose {ndim} {fmt_ints(axes)}"
        try:
            out = "OK " + fmt_ints(d - 2 for d in np.transpose(a, axes).shape)
        except Exception as e:
            out = classify(e)
    else:
        shape = tuple(rng.choice([1, 1, 2, 0]) for _ in range(ndim))
        a = np.empty(shape, dtype=np.int8)
        is_tuple = rng.random() < 0.6
        axes = [axis(rng, ndim) for _ in range(rng.randrange(0, 4) if is_tuple else 1)]
        line = f"squeeze {fmt_ints(shape)} {'t' if is_tuple else 'i'} {fmt_ints(axes)}"
        try:
            out = "OK " + fmt_ints(a.squeeze(axis=tuple(axes) if is_tuple else axes[0]).shape)
        except Exception as e:
            out = classify(e)
    return line, out


if __name__ == "__main__":
    main(gen, exe="npdiff_broadcast")
