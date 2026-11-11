"""Shared helpers for the datetime differential tests: unit names and value generators biased toward the edges of the calendar code."""
import warnings

import numpy as np

warnings.simplefilter("ignore")

UNITS = ["Y", "M", "W", "D", "h", "m", "s", "ms", "us", "ns", "ps", "fs", "as"]
NUMS = [1, 1, 1, 1, 1, 1, 2, 3, 7, 10, 12, 24, 60, 1000]
I64_MIN = -2**63
I64_MAX = 2**63 - 1

# Day counts on the edges of the Neri and Schneider range of set_datetimestruct_days, near the 400 year cycle and near the int64 limits.
DAY_EDGES = [-12699422, -12699423, 1061042401, 1061042402, -719468, -719469, -719528, -719162, 0, -1, 59, 60, 10957, 11016, 2932896, -146097, 146097]

# Unit sizes in attoseconds, used to pick values that land on year boundaries.
AS_PER = {"D": 86400 * 10**18, "h": 3600 * 10**18, "m": 60 * 10**18, "s": 10**18, "ms": 10**15, "us": 10**12, "ns": 10**9, "ps": 10**6, "fs": 10**3, "as": 1}


def dtype(unit, num):
    return np.dtype(f"M8[{num}{unit}]" if num != 1 else f"M8[{unit}]")


def rand_num(rng):
    return rng.choice(NUMS)


def rand_value(rng, unit):
    """An int64 value for a datetime of the given unit, biased toward edges."""
    r = rng.random()
    if r < 0.08:
        return rng.choice([I64_MIN, I64_MIN + 1, I64_MIN + 2, I64_MAX, I64_MAX - 1, I64_MAX - 1970, I64_MAX - 1969, 2**62, -2**62, 2**31, -2**31, 2**32, -2**32, 2**53])
    if r < 0.18:
        return rng.choice([0, 1, -1, 2, -2, 6, -6, 7, -7, 12, -12, 23, -23, 24, -24, 59, -59, 60, -60, 999, -999, 1000, -1000])
    if r < 0.32 and unit in ("D", "W"):
        e = rng.choice(DAY_EDGES)
        return (e // 7 if unit == "W" else e) + rng.randrange(-3, 4)
    if r < 0.5:
        # A date between year -30000 and year 30000 in this unit.
        days = rng.randrange(-11700000, 10300000)
        if unit == "Y":
            return days // 365
        if unit == "M":
            return days // 30
        if unit == "W":
            return days // 7
        v = days * AS_PER["D"] // AS_PER[unit] + rng.randrange(0, max(1, AS_PER["D"] // AS_PER[unit]))
        return max(I64_MIN + 1, min(I64_MAX, v))
    if r < 0.6:
        # Years that fit the 64-bit ranges of each unit, from the table in arrays.datetime.rst.
        return rng.randrange(-2**40, 2**40)
    return rng.randrange(I64_MIN + 1, I64_MAX + 1)


def i64(x):
    return int(np.asarray(x).view("i8").reshape(-1)[0])
