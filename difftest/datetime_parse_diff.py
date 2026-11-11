"""Differential test for NpyDatetime_ParseISO8601Datetime (datetime_strings.c:220) and NpyDatetime_ConvertDatetimeStructToDatetime64 (datetime.c:301) through np.datetime64(str) and np.datetime64(str, unit). The strings 'today' and 'now' are never generated, because they depend on the clock."""
import re

import numpy as np
from datetime_common import UNITS, i64
from harness import main

CHARS = "0123456789-+:. TZtzNnAa\t"


def year(rng):
    r = rng.random()
    if r < 0.5:
        return str(rng.randrange(0, 10000)).zfill(4)
    if r < 0.6:
        return str(rng.randrange(0, 100))
    if r < 0.75:
        return str(rng.randrange(10000, 10**rng.randrange(5, 19)))
    if r < 0.85:
        return rng.choice(["9223372036854775807", "9223372036854775808", "9223372036854775809", "18446744073709551616", "18446744073709551617", "99999999999999999999", "292277026596", "292277026597", "2262", "1677", "1678"])
    return "".join(rng.choice("0123456789") for _ in range(rng.randrange(0, 25)))


def field(rng, lo, hi, edge):
    r = rng.random()
    if r < 0.85:
        return str(rng.randrange(lo, hi)).zfill(2)
    if r < 0.93:
        return str(rng.choice(edge)).zfill(2)
    return str(rng.randrange(0, 100)).zfill(2)


def valid(rng):
    y = year(rng)
    s = rng.choice(["", "", "", "-", "+", " -", "  ", " +", "\t-"]) + y
    depth = rng.randrange(0, 8)
    if depth >= 1:
        s += "-" + field(rng, 1, 13, [0, 12, 13])
    if depth >= 2:
        s += "-" + field(rng, 1, 29, [0, 29, 30, 31, 32])
    if depth >= 3:
        s += rng.choice("T T") + field(rng, 0, 24, [23, 24])
    if depth >= 4:
        s += ":" + field(rng, 0, 60, [59, 60])
    if depth >= 5:
        s += ":" + field(rng, 0, 60, [59, 60])
    if depth >= 6:
        s += "." + "".join(rng.choice("0123456789") for _ in range(rng.randrange(0, 21)))
    if depth >= 3 and rng.random() < 0.3:
        s += rng.choice(["Z", "Z ", "Z+01", "+01", "-01", "+0130", "-01:30", "+23:59", "+24", "+01:60", "+1", "+01:3", " ", "  ", "z", "+01 "])
    return s


def mutate(rng, s):
    s = list(s)
    for _ in range(rng.randrange(1, 3)):
        k = rng.random()
        i = rng.randrange(0, len(s) + 1)
        if k < 0.4:
            s.insert(i, rng.choice(CHARS))
        elif k < 0.7 and s:
            del s[min(i, len(s) - 1)]
        elif s:
            s[min(i, len(s) - 1)] = rng.choice(CHARS)
    return "".join(s)


def rand_string(rng):
    r = rng.random()
    if r < 0.05:
        return rng.choice(["", "NaT", "nat", "NAT", "nAt", " NaT", "NaT ", "na", "-", "+", " ", "T", "--01", "-+5", "+-5"])
    s = valid(rng)
    if r < 0.3:
        s = mutate(rng, s)
    return s


ERRS = [("Month out of range", "month"), ("Day out of range", "day"), ("Hours out of range", "hour"), ("Minutes out of range", "minute"), ("Seconds out of range", "second"), ("Timezone hours offset", "tzhour"), ("Timezone minutes offset", "tzminute")]


def gen(rng):
    s = rand_string(rng)
    while s.lower() in ("today", "now"):
        s = rand_string(rng)
    if rng.random() < 0.6:
        unit, num, arg = "_", 1, ()
    else:
        unit = rng.choice(UNITS)
        num = rng.choice([1, 1, 1, 2, 3, 7, 1000])
        arg = (f"{num}{unit}",)
    line = f"parse {unit} {num} {s.encode('ascii').hex() or '_'}"
    try:
        d = np.datetime64(s, *arg)
    except ValueError as e:
        msg = str(e)
        m = re.search(r"at position (\d+)$", msg)
        if m:
            return line, f"ERR parse {m.group(1)}"
        for key, name in ERRS:
            if msg.startswith(key):
                return line, f"ERR {name}"
        return line, f"ERR ValueError {msg}"
    u, n = np.datetime_data(d.dtype)
    return line, f"OK {u} {n} {i64(d)}"


if __name__ == "__main__":
    main(gen, exe="npdiff_datetime")
