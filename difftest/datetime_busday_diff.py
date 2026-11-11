"""Differential test for np.busday_offset, np.busday_count and np.is_busday (datetime_busday.c:159, :272, :362, :729) with small weekmasks and holiday lists, including NaT, duplicate and weekend holidays and dates near the int64 limits."""
import numpy as np
from datetime_common import I64_MAX, I64_MIN
from harness import fmt_ints, main

ROLLS = ["raise", "nat", "forward", "following", "backward", "preceding", "modifiedfollowing", "modifiedpreceding"]
EDGE_DATES = [I64_MIN + 1, I64_MIN + 2, I64_MIN + 5, I64_MIN + 9, I64_MAX, I64_MAX - 1, I64_MAX - 6, -2**62, 2**62, -12699422, 1061042401]


def wrap(x):
    return (x + 2**63) % 2**64 - 2**63


def rand_date(rng):
    r = rng.random()
    if r < 0.03:
        return I64_MIN
    if r < 0.1:
        return max(I64_MIN + 1, min(I64_MAX, rng.choice(EDGE_DATES) + rng.randrange(-3, 4) * (0 if r < 0.05 else 1)))
    if r < 0.85:
        return 10957 + rng.randrange(-120, 120)
    return rng.randrange(-2**62, 2**62)


def rand_mask(rng):
    r = rng.random()
    if r < 0.02:
        return "0000000"
    if r < 0.4:
        return rng.choice(["1111100", "1111110", "1111111", "0000001", "1000000", "0111110", "1010100"])
    while True:
        m = "".join(rng.choice("01") for _ in range(7))
        if "1" in m:
            return m


def rand_holidays(rng, near):
    n = rng.choice([0, 0, 1, 2, 3, 5, 8])
    hs = []
    for _ in range(n):
        if rng.random() < 0.08:
            hs.append(I64_MIN)
        elif near is None or abs(near) > 2**61:
            hs.append(10957 + rng.randrange(-60, 60))
        else:
            hs.append(near + rng.randrange(-15, 25))
    if hs and rng.random() < 0.2:
        hs.append(rng.choice(hs))
    return [max(I64_MIN, min(I64_MAX, h)) for h in hs]


def hang(b, e):
    """True when the remaining days loop of apply_business_day_count would run more than 1000 times."""
    if b == I64_MIN or e == I64_MIN or b == e:
        return False
    if b > e:
        b, e = wrap(e + 1), wrap(b + 1)
    d = wrap(e - b)
    weeks = abs(d) // 7 * (1 if d >= 0 else -1)
    b = wrap(b + weeks * 7)
    return e - b > 1000


def dates(xs):
    return np.array(xs, dtype="M8[D]")


def gen(rng):
    kind = rng.choice(["busoff", "busoff", "buscount", "isbus"])
    mask = rand_mask(rng)
    wm = [c == "1" for c in mask]
    d = rand_date(rng)
    hs = rand_holidays(rng, d)
    try:
        if kind == "busoff":
            off = rng.choice([0, 1, -1, 2, -2, 3, -3, 4, 5, -5, 6, 7, -7, 10, -10, 23, -23]) if rng.random() < 0.85 else rng.choice([2**62, -2**62, I64_MAX, I64_MIN + 1, 2**40, -2**40, rng.randrange(I64_MIN + 1, I64_MAX)])
            roll = rng.choice(ROLLS)
            line = f"busoff {d} {off} {roll} {mask} {fmt_ints(hs)}"
            r = np.busday_offset(dates([d])[0], off, roll=roll, weekmask=wm, holidays=dates(hs))
            return line, f"OK {int(np.asarray(r).view('i8'))}"
        if kind == "buscount":
            e = d + rng.randrange(-40, 40) if rng.random() < 0.8 else rand_date(rng)
            e = max(I64_MIN, min(I64_MAX, e))
            while hang(d, e):
                e = d + rng.randrange(-40, 40)
                e = max(I64_MIN, min(I64_MAX, e))
            line = f"buscount {d} {e} {mask} {fmt_ints(hs)}"
            r = np.busday_count(dates([d])[0], dates([e])[0], weekmask=wm, holidays=dates(hs))
            return line, f"OK {int(r)}"
        line = f"isbus {d} {mask} {fmt_ints(hs)}"
        r = np.is_busday(dates([d])[0], weekmask=wm, holidays=dates(hs))
        return line, f"OK {bool(r)}"
    except ValueError as err:
        msg = str(err)
        if "weekmask must have" in msg:
            return line, "ERR emptymask"
        if "NaT input" in msg:
            return line, "ERR natinput"
        if "Non-business day" in msg:
            return line, "ERR nonbusiness"
        if "business day count with a NaT" in msg:
            return line, "ERR natcount"
        return line, f"ERR ValueError {msg}"


if __name__ == "__main__":
    main(gen, exe="npdiff_datetime")
