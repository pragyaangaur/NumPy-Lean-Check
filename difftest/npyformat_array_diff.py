"""Differential test for the count and reshape logic of `read_array` (lib/_format_impl.py:837 to 894).

The header declares the dtype `|V0`, whose itemsize is zero, so no data is read and no memory is allocated whatever the shape says. A shape that mixes entries above 2**63 - 1 with smaller ones makes NumPy build a float64 array, which depends on the platform's float to int cast, so the test leaves those out.
"""
import io

import numpy as np
from harness import fmt_ints, main
from npyformat_common import fmt

BIG = [2**31, 2**32, 2**62, 2**63 - 1, 2**63, 2**64 - 1, 2**64, 2**32 + 1, 3037000500, 4611686018427387904]
SMALL = [0, 0, 1, 1, 2, 3, 4, 5, 6, 10, 100]


def gen(rng):
    while True:
        n = rng.choice([0, 1, 1, 2, 2, 3, 3, 4])
        shape = []
        for _ in range(n):
            r = rng.random()
            if r < 0.5:
                shape.append(rng.choice(SMALL))
            elif r < 0.7:
                shape.append(rng.choice(BIG))
            elif r < 0.85:
                shape.append(-rng.choice([1, 1, 2, 3, 2**31, 2**32, 2**62, 2**63, 2**63 + 1]))
            else:
                shape.append(rng.choice([2**32, 2**31]) * rng.choice([1, 1, 1, -1]) + rng.randrange(-1, 2))
        if any(d > 2**63 - 1 for d in shape) and not all(d > 2**63 - 1 for d in shape):
            continue
        break
    if rng.random() < 0.04:
        shape = [rng.choice([2**63, 2**63 + 1, 2**64 - 1]) for _ in range(rng.randrange(1, 4))]
    fortran = rng.random() < 0.4
    bio = io.BytesIO()
    fmt._write_array_header(bio, {"descr": "|V0", "fortran_order": fortran, "shape": tuple(shape)}, (1, 0))
    bio.seek(0)
    line = f"npy_array {int(fortran)} {fmt_ints(shape)}"
    try:
        a = fmt.read_array(bio)
        out = "OK " + (fmt_ints(a.shape))
    except OverflowError:
        out = "ERR overflow"
    except ValueError as e:
        m = str(e)
        out = ("ERR neg" if "negative dimensions" in m else "ERR maxdim" if "Maximum allowed" in m
               else "ERR multiple" if "one unknown" in m else "ERR mismatch" if "cannot reshape" in m else "ERR OTHER " + m[:60])
    return line, out


if __name__ == "__main__":
    main(gen, exe="npdiff_npyformat")
