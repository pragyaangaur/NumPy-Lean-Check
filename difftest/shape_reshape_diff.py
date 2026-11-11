"""Differential test for `_fix_unknown_dimension` (shape.c:485) through `ndarray.reshape`."""
import numpy as np
from harness import fmt_ints, main

BIG = [2**31, 2**32, 2**62, 2**63 - 1, 3037000500, 4611686018427387904]


def gen(rng):
    size = rng.choice([0, 1, 2, 6, 12, 24, 60, 64, rng.randrange(0, 200)])
    n = rng.randrange(0, 5)
    dims = []
    for _ in range(n):
        r = rng.random()
        if r < 0.15:
            dims.append(-1)
        elif r < 0.22:
            dims.append(-rng.randrange(2, 9))
        elif r < 0.27:
            dims.append(rng.choice(BIG))
        else:
            dims.append(rng.choice([0, 1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12]))
    dtype = rng.choice([np.int8, np.int16, np.int64])
    line = f"reshape_fix {fmt_ints(dims)} {size} {np.dtype(dtype).itemsize}"
    try:
        out = "OK " + fmt_ints(np.empty(size, dtype=dtype).reshape(dims).shape)
    except ValueError as e:
        msg = str(e)
        if "one unknown dimension" in msg:
            out = "ERR multiple"
        elif "too big" in msg:
            out = "ERR toobig"
        else:
            out = "ERR mismatch"
    return line, out


if __name__ == "__main__":
    main(gen)
