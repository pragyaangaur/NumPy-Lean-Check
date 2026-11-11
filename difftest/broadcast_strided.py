"""Shared generator of small strided views for the flags and reshape differential tests. Views are made with `as_strided` on a one-element buffer and never read, so any strides are safe."""
import numpy as np
from numpy.lib.stride_tricks import as_strided

DTYPES = [np.dtype(np.int8), np.dtype(np.int16), np.dtype(np.int32), np.dtype(np.int64), np.dtype(np.complex128)]


def c_strides(dims, itemsize):
    out = []
    s = itemsize
    for d in reversed(dims):
        out.append(s)
        s *= max(d, 1)
    return list(reversed(out))


def strided(rng, dims=None, allow_zero=True):
    """Return dims, strides and dtype of a view whose layout is often close to contiguous."""
    dt = rng.choice(DTYPES)
    it = dt.itemsize
    if dims is None:
        choices = [0, 1, 1, 2, 2, 3, 4] if allow_zero else [1, 1, 2, 2, 3, 4]
        dims = [rng.choice(choices) for _ in range(rng.randrange(0, 5))]
    r = rng.random()
    if r < 0.3:
        strides = c_strides(dims, it)
    elif r < 0.45:
        strides = list(reversed(c_strides(list(reversed(dims)), it)))
    elif r < 0.75:
        # A transposed or stepped view of a contiguous parent.
        base = c_strides(dims, it)
        strides = [s * rng.choice([1, 1, 1, 2, -1, 3]) for s in base]
        if rng.random() < 0.5 and len(dims) > 1:
            perm = list(range(len(dims)))
            rng.shuffle(perm)
            dims = [dims[p] for p in perm]
            strides = [strides[p] for p in perm]
    else:
        strides = [rng.choice([0, it, -it, 2 * it, 3 * it, 4 * it, 6 * it, 8 * it, 12 * it, 1, 5, -7]) for _ in dims]
    return dims, strides, dt


def make(dims, strides, dt):
    buf = np.zeros(1, dtype=dt)
    return as_strided(buf, shape=tuple(dims), strides=tuple(strides))
