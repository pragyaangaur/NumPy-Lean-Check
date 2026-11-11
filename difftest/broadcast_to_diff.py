"""Differential test for `np.broadcast_to` (`lib/_stride_tricks_impl.py:447`), which runs the shape logic of `np.nditer` with `itershape` (`_core/src/multiarray/nditer_constr.c:1471`) and builds the view in `NpyIter_GetIterView`. The view's shape and strides are compared."""
import numpy as np
from harness import fmt_ints, main
from broadcast_common import classify, dim

DTYPES = [np.dtype(np.int8), np.dtype(np.int16), np.dtype(np.int64), np.dtype(np.complex128), np.dtype([])]


def gen(rng):
    dt = rng.choice(DTYPES)
    op = tuple(rng.choice([0, 1, 1, 2, 3, 4]) for _ in range(rng.randrange(0, 4)))
    r = rng.random()
    if r < 0.6:
        lead = [rng.choice([0, 1, 2, 3, 5]) for _ in range(rng.randrange(0, 3))]
        tail = [d if (d != 1 or rng.random() < 0.5) else rng.choice([0, 1, 2, 3]) for d in op]
        if rng.random() < 0.2 and tail:
            tail[rng.randrange(len(tail))] = dim(rng, 0.2)
        if rng.random() < 0.15 and tail:
            tail.pop(0)
        shape = tuple(lead + tail)
    elif r < 0.8:
        shape = tuple(dim(rng, 0.35) for _ in range(rng.randrange(0, 5)))
    elif r < 0.9:
        # Huge entries with a zero somewhere, to reach the iterator size check and the view size check.
        shape = [rng.choice([2**31, 2**32, 2**60, 2**61, 2**62, 2**63 - 1, 2, 3]) for _ in range(rng.randrange(1, 4))]
        if rng.random() < 0.5:
            shape.insert(rng.randrange(len(shape) + 1), 0)
        shape = tuple(shape + list(op))
    else:
        shape = tuple([1] * rng.choice([32, 33, 63, 64, 65]) + list(op))
    line = f"bto {fmt_ints(op)} {dt.itemsize} {fmt_ints(shape)}"
    try:
        v = np.broadcast_to(np.empty(op, dtype=dt), shape)
        out = f"OK {fmt_ints(v.shape)} {fmt_ints(v.strides)}"
    except (ValueError, OverflowError, TypeError, RuntimeError) as e:
        out = classify(e)
    return line, out


if __name__ == "__main__":
    main(gen, exe="npdiff_broadcast")
