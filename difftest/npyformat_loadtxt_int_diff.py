"""Differential test for the integer conversion of `np.loadtxt` (textreading/str_to_int.h:20 and :98).

Each case is one field of a one-line text with the delimiter ','. The field never contains a comma or a line break."""
import numpy as np
from harness import main
from npyformat_common import hx_text

CODES = ["i1", "i2", "i4", "i8", "u1", "u2", "u4", "u8"]
SPACES = [" ", " ", "\t", "\x0b", "\x0c", "\x1c", "\x1f", "\x85", " ", " ", " ", " ", " ", "　"]
ODD = ["_", "a", ".", "e", "x", "٣", "５", "²", "+", "-", "0", "​", "﻿"]


def limits(code):
    bits = 8 * int(code[1:])
    return (-(2 ** (bits - 1)), 2 ** (bits - 1) - 1) if code[0] == "i" else (0, 2 ** bits - 1)


def field(rng, code):
    lo, hi = limits(code)
    r = rng.random()
    if r < 0.45:
        v = rng.choice([lo, hi, lo - 1, hi + 1, 0, -1, 1, lo + 1, hi - 1, 2 ** 63, 2 ** 64, -2 ** 63 - 1, 2 ** 64 - 1, rng.randrange(lo - 3, hi + 4)])
        s = str(v)
    elif r < 0.6:
        s = str(rng.randrange(0, 10 ** rng.randrange(1, 22)))
        s = rng.choice(["", "+", "-", "-", "+"]) + s
    elif r < 0.75:
        s = "".join(rng.choice("0123456789") for _ in range(rng.randrange(0, 6)))
        if rng.random() < 0.5:
            s = rng.choice(["+", "-", ""]) + s
    else:
        s = "".join(rng.choice("0123456789+-" if rng.random() < 0.6 else ODD) for _ in range(rng.randrange(0, 5)))
    if rng.random() < 0.3:
        s = "".join(rng.choice(SPACES) for _ in range(rng.randrange(0, 3))) + s
    if rng.random() < 0.3:
        s = s + "".join(rng.choice(SPACES) for _ in range(rng.randrange(0, 3)))
    if rng.random() < 0.08 and s:
        i = rng.randrange(len(s) + 1)
        s = s[:i] + rng.choice(SPACES + ODD) + s[i:]
    return s


def gen(rng):
    code = rng.choice(CODES)
    s = field(rng, code)
    line = f"loadtxt_int {code} {hx_text(s) if s else '_'}"
    try:
        a = np.loadtxt([f"0,{s},0"], dtype=np.dtype(code), delimiter=",", usecols=1, comments=None, quotechar=None, ndmin=1)
        out = f"OK {int(a[0])}"
    except ValueError:
        out = "ERR"
    return line, out


if __name__ == "__main__":
    main(gen, exe="npdiff_npyformat")
