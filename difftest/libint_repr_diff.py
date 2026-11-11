"""Differential test for `np.binary_repr` (numeric.py:1999) and `np.base_repr` (numeric.py:2106).

Numbers are biased toward zero, powers of two and their neighbours, where the two's complement width fix of gh-8679 applies. Widths and paddings include None, zero and negative values.
"""
import numpy as np
from harness import main


def pick_num(rng):
    r = rng.random()
    if r < 0.15:
        v = 0
    elif r < 0.6:
        v = 2 ** rng.randrange(0, 70) + rng.choice([-1, 0, 0, 1])
    else:
        v = rng.randrange(0, 2 ** rng.randrange(1, 70))
    return -v if rng.random() < 0.5 else v


def gen(rng):
    num = pick_num(rng)
    if rng.random() < 0.5:
        width = rng.choice([None, None, 0, -1, -5, rng.randrange(0, 80), num.bit_length(), num.bit_length() + 1])
        line = f"binrepr {num} {'N' if width is None else width}"
        try:
            out = f"OK '{np.binary_repr(num, width=width)}'"
        except ValueError:
            out = "ERR insufficient"
        return line, out
    base = rng.choice([2, 3, 8, 10, 16, 36, rng.randrange(2, 37), rng.randrange(2, 37), 0, 1, 37, -2])
    padding = rng.choice([0, 0, 0, 1, 2, 5, -1, -3])
    line = f"baserepr {num} {base} {padding}"
    try:
        out = f"OK '{np.base_repr(num, base, padding)}'"
    except ValueError as e:
        out = "ERR big" if "greater" in str(e) else "ERR small"
    return line, out


if __name__ == "__main__":
    main(gen, exe="npdiff_libint")
