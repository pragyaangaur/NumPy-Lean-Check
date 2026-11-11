"""Shared helpers for the dtype differential tests: the wire names of dtypes and a generator biased toward the string lengths where casting and promotion change."""
import numpy as np

CHARS = list("?bBhHiIlLqQefdgFDGO")
WIDTHS = [0, 1, 2, 3, 4, 5, 6, 9, 10, 11, 19, 20, 21, 22, 31, 32, 33, 47, 48, 49, 63, 64, 65, 95, 96, 97]


def rand_width(rng):
    return rng.choice(WIDTHS) if rng.random() < 0.8 else rng.randrange(0, 120)


def rand_token(rng, strings=0.3):
    if rng.random() < strings:
        return rng.choice("SU") + str(rand_width(rng))
    return rng.choice(CHARS)


def to_dtype(tok):
    return np.dtype(tok)


def fmt_dtype(dt):
    if dt.char == "S":
        return f"S{dt.itemsize}"
    if dt.char == "U":
        return f"U{dt.itemsize // 4}"
    return dt.char
