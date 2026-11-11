"""Differential test for casting between datetime64 units: get_datetime_conversion_factor (datetime.c:1057), _datetime_scale_with_overflow_check (_datetime.h:354) and the struct based cast for years and months (dtype_transfer.c:775)."""
import numpy as np
from datetime_common import UNITS, dtype, i64, rand_num, rand_value
from harness import main


def gen(rng):
    u1 = rng.choice(UNITS)
    u2 = rng.choice(UNITS) if rng.random() < 0.9 else u1
    n1 = rand_num(rng) if rng.random() < 0.3 else 1
    n2 = rand_num(rng) if rng.random() < 0.3 else 1
    v = rand_value(rng, u1)
    line = f"cast {u1} {n1} {u2} {n2} {v}"
    a = np.array([v], dtype=dtype(u1, n1))
    try:
        out = f"OK {i64(a.astype(dtype(u2, n2)))}"
    except OverflowError as e:
        out = "ERR factor" if "conversion factor" in str(e) else "ERR overflow"
    return line, out


if __name__ == "__main__":
    main(gen, exe="npdiff_datetime")
