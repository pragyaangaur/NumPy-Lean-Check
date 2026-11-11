"""Shared helpers for the string differential tests.

A string is a list of code units: bytes for kind S, code points for kinds U and T. The same list is sent to the Lean executable as comma separated integers, and built into a one element NumPy array of the right dtype.
"""
import numpy as np

KINDS = ["S", "U", "T"]
STRING_DTYPE = np.dtypes.StringDType()
INT64_MIN = -(2**63)
INT64_MAX = 2**63 - 1

# a, b, space, tab, newline, NUL, and a non-ASCII letter. U and T add a 3 byte and a 4 byte UTF-8 character and two Unicode spaces.
ALPHA_S = [97, 98, 97, 98, 32, 9, 10, 0, 233]
ALPHA_U = [97, 98, 97, 98, 32, 9, 10, 0, 233, 0x20AC, 0x1D11E, 0xA0, 0x2003]
BIG_INTS = [2**31 - 1, 2**31, 2**32, 2**62, 2**63 - 1, -(2**31), -(2**32), -(2**62), -(2**63)]


def alphabet(kind):
    return ALPHA_S if kind == "S" else ALPHA_U


def rand_str(rng, kind, maxlen=6):
    n = rng.choice([0, 0, 1, 1, 2, 3, 4, 5, maxlen])
    al = alphabet(kind)
    return [rng.choice(al) for _ in range(n)]


def rand_needle(rng, kind, hay, maxlen=3):
    """A needle that is often a piece of the haystack, so that matches are common."""
    r = rng.random()
    if r < 0.45 and hay:
        i = rng.randrange(0, len(hay))
        j = rng.randrange(i, min(len(hay), i + maxlen) + 1)
        return hay[i:j]
    if r < 0.5:
        return []
    return rand_str(rng, kind, maxlen)


def rand_index(rng, span=8):
    r = rng.random()
    if r < 0.7:
        return rng.randrange(-span, span + 1)
    if r < 0.85:
        return rng.choice(BIG_INTS)
    return rng.choice([INT64_MIN, INT64_MAX, 0, -1, 1])


def fmt(codes):
    return ",".join(str(c) for c in codes) if codes else "_"


def to_py(kind, codes):
    if kind == "S":
        return bytes(codes)
    return "".join(chr(c) for c in codes)


def from_py(x):
    if isinstance(x, (bytes, bytearray)):
        return list(x)
    return [ord(c) for c in x]


def arr(kind, codes, rng=None):
    """One element array. S and U get extra padding at random so that trailing NULs inside the buffer are tested."""
    x = to_py(kind, codes)
    if kind == "T":
        return np.array([x], dtype=STRING_DTYPE)
    pad = rng.choice([0, 0, 1, 2]) if rng else 0
    w = max(1, len(codes) + pad)
    return np.array([x], dtype=f"{kind}{w}")


def cls(n):
    n = int(n)
    return f"NEG {n}" if n < 0 else ("ZERO 0" if n == 0 else f"POS {n}")


def out_codes(kind, a):
    """Read element 0 of a result array back as code units."""
    v = a[0]
    if kind == "S":
        return list(bytes(v))
    return [ord(c) for c in str(v)]


def run(f):
    """Run `f`, mapping NumPy errors to the classes the model prints."""
    try:
        return f()
    except MemoryError:
        return "ERR alloc"
    except OverflowError:
        return "ERR overflow"
    except TypeError:
        return "ERR type"
    except ValueError as e:
        if "Maximum allowed size" in str(e) or "too large" in str(e) or "too big" in str(e):
            return "ERR alloc"
        return "ERR value"


def big_width(rng, kind):
    """A width that fails in every kind without a large allocation: above the dtype limit for S and U, above any real memory for T."""
    if kind == "T":
        return rng.choice([2**58, 2**60, 2**61, 2**62, 2**63 - 1])
    return rng.choice([2**31, 2**32, 2**40, 2**62, 2**63 - 1])


def rand_width(rng, kind):
    r = rng.random()
    if r < 0.8:
        return rng.randrange(-3, 14)
    if r < 0.9:
        return big_width(rng, kind)
    return rng.choice([INT64_MIN, -(2**31), 0, 1, 2])


def fmt_res(kind, a):
    return "OK " + fmt(out_codes(kind, a))
