"""Differential test for NpyDatetime_ConvertDatetime64ToDatetimeStruct (datetime.c:440) and NpyDatetime_MakeISO8601Datetime (datetime_strings.c:868) through np.datetime_as_string."""
import numpy as np
from datetime_common import UNITS, dtype, rand_num, rand_value
from harness import main


def gen(rng):
    unit = rng.choice(UNITS)
    num = rand_num(rng) if rng.random() < 0.25 else 1
    v = rand_value(rng, unit)
    r = rng.random()
    pu = "_" if r < 0.5 else ("auto" if r < 0.75 else rng.choice(UNITS))
    line = f"tostr {unit} {num} {v} {pu}"
    a = np.array([v], dtype=dtype(unit, num))
    try:
        s = np.datetime_as_string(a, unit=None if pu == "_" else pu)[0]
        out = f"OK {s}"
    except OverflowError:
        out = "ERR overflow"
    return line, out


if __name__ == "__main__":
    main(gen, exe="npdiff_datetime")
