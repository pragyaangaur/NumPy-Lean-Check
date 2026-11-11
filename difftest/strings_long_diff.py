"""Differential test for find, rfind and count on long, periodic strings. `fastsearch` (`string_fastsearch.h:1258`) switches from `default_find` to `two_way_find`, `two_way_count` and `adaptive_find` only for haystacks of 2500 or more units, so the short tests never reach those branches. Strings are sent as `unit:count` pieces to keep the lines short."""
import numpy as np
from harness import main
from strings_common import STRING_DTYPE, cls

LETTERS = {"a": 97, "b": 98, "c": 233}


def build(kind, spec):
    s = "".join(u * n for u, n in spec)
    if kind == "S":
        return np.array([bytes(LETTERS[c] for c in s)], dtype=f"S{max(1, len(s))}")
    t = "".join(chr(LETTERS[c]) for c in s)
    if kind == "T":
        return np.array([t], dtype=STRING_DTYPE)
    return np.array([t], dtype=f"U{max(1, len(s))}")


def fmt_spec(spec):
    return ";".join(f"{u}:{n}" for u, n in spec) if spec else "_"


def rand_unit(rng):
    n = rng.choice([1, 1, 2, 3, 5, 7])
    return "".join(rng.choice("aab" if rng.random() < 0.9 else "abc") for _ in range(n))


def rand_spec(rng, total, pieces):
    """About `total` units made of up to `pieces` repeated units."""
    spec = []
    left = total
    for i in range(pieces):
        u = rand_unit(rng)
        n = left // len(u) if i == pieces - 1 else rng.randrange(0, left // len(u) + 1)
        if n:
            spec.append((u, n))
            left -= n * len(u)
    return spec


def total(spec):
    return sum(len(u) * n for u, n in spec)


def adjust(start, end, n):
    """`adjust_offsets` (`string_buffer.h:829`)."""
    if end > n:
        end = n
    elif end < 0:
        end = max(0, end + n)
    if start < 0:
        start = max(0, start + n)
    return start, end


def in_adaptive_regime(n, m):
    """Whether `fastsearch` takes `adaptive_find`, which the model does not port, for a window of n units and a needle of m units."""
    if n < 2500 or (m < 100 and n < 30000) or m < 6:
        return False
    return not ((m >> 2) * 3 < (n >> 2))


def gen(rng):
    kind = rng.choice(["S", "U", "T"])
    op = rng.choice(["find", "rfind", "count", "count", "find"])
    r = rng.random()
    if r < 0.4:
        nh, nn = rng.randrange(0, 300), rng.randrange(0, 40)
    elif r < 0.8:
        nh, nn = rng.randrange(2500, 3600), rng.randrange(100, 400)  # two-way, since m >= 100
    elif r < 0.9:
        nh, nn = rng.randrange(2500, 3600), rng.randrange(1000, 2600)  # needle above a third of the haystack
    else:
        nh, nn = rng.randrange(30000, 31500), rng.randrange(6, 100)  # n >= 30000 and m < 100
    hay = rand_spec(rng, nh, rng.choice([1, 2, 3, 5]))
    if rng.random() < 0.6 and total(hay) > 0:
        # a needle cut from the haystack, or the haystack unit extended by a different tail
        flat = "".join(u * n for u, n in hay)
        i = rng.randrange(0, max(1, total(hay) - nn))
        piece = flat[i:i + nn]
        needle = [(piece, 1)] if piece else []
        if rng.random() < 0.3 and piece:
            needle = [(piece[:-1], 1), (rng.choice("ab"), 1)]
    else:
        needle = rand_spec(rng, nn, rng.choice([1, 2, 3]))
    if rng.random() < 0.7:
        s, e = 0, 2**63 - 1
    else:
        s, e = rng.randrange(-50, nh // 2 + 1), rng.choice([2**63 - 1, nh - rng.randrange(0, 50), -rng.randrange(0, 50)])
    if kind == "U" and op != "rfind":
        s2, e2 = adjust(s, e, total(hay))
        if in_adaptive_regime(e2 - s2, total(needle)):
            kind = "S"  # the model does not port adaptive_find for U
    a, n = build(kind, hay), build(kind, needle)
    res = getattr(np.strings, op)(a, n, np.int64(s), np.int64(e))[0]
    return f"long {kind} {op} {fmt_spec(hay)} {fmt_spec(needle)} {s} {e}", cls(res)


if __name__ == "__main__":
    main(gen, exe="npdiff_strings")
