"""Differential test for find, rfind, index, rindex, count, startswith, endswith and str_len on the S, U and T kinds (`string_buffer.h:829-1160`, `string_ufuncs.cpp:314`, `stringdtype_ufuncs.cpp:876`)."""
import numpy as np
from harness import main
from strings_common import KINDS, arr, cls, fmt, rand_index, rand_needle, rand_str, run

FUNCS = {
    "find": lambda a, n, s, e: cls(np.strings.find(a, n, s, e)[0]),
    "rfind": lambda a, n, s, e: cls(np.strings.rfind(a, n, s, e)[0]),
    "index": lambda a, n, s, e: cls(np.strings.index(a, n, s, e)[0]),
    "rindex": lambda a, n, s, e: cls(np.strings.rindex(a, n, s, e)[0]),
    "count": lambda a, n, s, e: cls(np.strings.count(a, n, s, e)[0]),
    "startswith": lambda a, n, s, e: str(bool(np.strings.startswith(a, n, s, e)[0])),
    "endswith": lambda a, n, s, e: str(bool(np.strings.endswith(a, n, s, e)[0])),
}
NAMES = list(FUNCS) + ["str_len"]


def gen(rng):
    kind = rng.choice(KINDS)
    op = rng.choice(NAMES)
    hay = rand_str(rng, kind, 7)
    if op == "str_len":
        a = arr(kind, hay, rng)
        return f"str_len {kind} {fmt(hay)}", cls(np.strings.str_len(a)[0])
    needle = rand_needle(rng, kind, hay)
    s, e = rand_index(rng), rand_index(rng)
    a, n = arr(kind, hay, rng), arr(kind, needle, rng)
    out = run(lambda: FUNCS[op](a, n, np.int64(s), np.int64(e)))
    return f"{op} {kind} {fmt(hay)} {fmt(needle)} {s} {e}", out


if __name__ == "__main__":
    main(gen, exe="npdiff_strings")
