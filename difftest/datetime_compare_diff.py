"""Differential test for the common unit of two datetimes, compute_datetime_metadata_greatest_common_divisor (datetime.c:1495) through np.result_type, and for the comparison ufuncs that cast both operands to that unit."""
import numpy as np
from datetime_common import UNITS, dtype, rand_moderate, rand_value
from harness import main

NUMS = [1, 1, 1, 2, 3, 5, 7, 12, 14, 24, 60, 1000, 2**30, 2**31 - 1]


def gen(rng):
    u1, u2 = rng.choice(UNITS), rng.choice(UNITS)
    n1 = rng.choice(NUMS) if rng.random() < 0.5 else 1
    n2 = rng.choice(NUMS) if rng.random() < 0.5 else 1
    v1 = rand_moderate(rng, u1) if rng.random() < 0.6 else rand_value(rng, u1)
    if rng.random() < 0.5:
        # Put the second value on the same instant or next to it, so that equality and order are tested where they matter.
        try:
            v2 = int(np.array([v1], dtype=dtype(u1, n1)).astype(dtype(u2, n2)).view("i8")[0]) + rng.choice([-1, 0, 0, 1])
        except OverflowError:
            v2 = rand_value(rng, u2)
        v2 = max(-2**63 + 1, min(2**63 - 1, v2))
    else:
        v2 = rand_moderate(rng, u2) if rng.random() < 0.6 else rand_value(rng, u2)
    line = f"cmp {u1} {n1} {v1} {u2} {n2} {v2}"
    try:
        c = np.result_type(dtype(u1, n1), dtype(u2, n2))
    except OverflowError:
        return line, "ERR gcd"
    unit, num = np.datetime_data(c)
    a = np.array([v1], dtype=dtype(u1, n1))
    b = np.array([v2], dtype=dtype(u2, n2))
    try:
        lt = bool((a < b)[0])
        eq = bool((a == b)[0])
    except OverflowError as e:
        return line, "ERR factor" if "conversion factor" in str(e) else "ERR overflow"
    return line, f"OK {unit} {num} {lt} {eq}"


if __name__ == "__main__":
    main(gen, exe="npdiff_datetime")
