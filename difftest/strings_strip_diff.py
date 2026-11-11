"""Differential test for strip, lstrip, rstrip and slice on the S, U and T kinds (`string_buffer.h:1166`, `:1230`, `string_ufuncs.cpp:670`, `stringdtype_ufuncs.cpp:1070`, `:1203`, `:2249`)."""
import numpy as np
from harness import main
from strings_common import BIG_INTS, INT64_MAX, INT64_MIN, KINDS, alphabet, arr, fmt, out_codes, rand_str, run

FUNCS = {"l": np.strings.lstrip, "r": np.strings.rstrip, "b": np.strings.strip}
SPACES_S = [32, 9, 10, 13, 11, 12]
SPACES_U = SPACES_S + [0xA0, 0x2003, 0x85, 0x1C]


def rand_text(rng, kind):
    """Text with plenty of whitespace and NULs at the edges."""
    sp = SPACES_S if kind == "S" else SPACES_U
    al = alphabet(kind)
    n = rng.choice([0, 1, 2, 3, 4, 5, 7])
    return [rng.choice(sp + [0]) if rng.random() < 0.5 else rng.choice(al) for _ in range(n)]


def rand_step_arg(rng):
    r = rng.random()
    if r < 0.75:
        return rng.randrange(-9, 10)
    if r < 0.9:
        return rng.choice(BIG_INTS)
    return rng.choice([INT64_MIN, INT64_MAX])


def gen(rng):
    kind = rng.choice(KINDS)
    if rng.random() < 0.7:
        m = rng.choice("lrb")
        a = rand_text(rng, kind)
        if rng.random() < 0.5:
            chars = None
        else:
            chars = [rng.choice(alphabet(kind)) for _ in range(rng.choice([0, 1, 1, 2, 3]))]
        if chars is None:
            out = run(lambda: "OK " + fmt(out_codes(kind, FUNCS[m](arr(kind, a, rng)))))
            return f"strip {kind} {m} {fmt(a)} !", out
        out = run(lambda: "OK " + fmt(out_codes(kind, FUNCS[m](arr(kind, a, rng), arr(kind, chars, rng)))))
        return f"strip {kind} {m} {fmt(a)} {fmt(chars)}", out
    a = rand_str(rng, kind, 7)
    s, e, st = rand_step_arg(rng), rand_step_arg(rng), rand_step_arg(rng)
    if rng.random() < 0.3:
        st = rng.choice([1, 1, -1, 2, -2])
    out = run(lambda: "OK " + fmt(out_codes(kind, np.strings.slice(arr(kind, a, rng), np.int64(s), np.int64(e), np.int64(st)))))
    return f"slice {kind} {fmt(a)} {s} {e} {st}", out


if __name__ == "__main__":
    main(gen, exe="npdiff_strings")
