"""Differential test for replace, partition and rpartition on the S, U and T kinds (`string_buffer.h:1372`, `:1658`, `strings.py:1291`, `:1538`, `stringdtype_ufuncs.cpp:1358`, `:2022`)."""
import numpy as np
from harness import main
from strings_common import BIG_INTS, KINDS, arr, fmt, from_py, out_codes, rand_needle, rand_str, run


def part_res(kind, parts):
    return "OK " + "|".join(fmt(out_codes(kind, p)) for p in parts)


def gen(rng):
    kind = rng.choice(KINDS)
    op = rng.choice(["replace", "replace", "partition", "rpartition"])
    hay = rand_str(rng, kind, 7)
    if op == "replace":
        old = rand_needle(rng, kind, hay)
        new = rand_str(rng, kind, 3)
        r = rng.random()
        count = rng.randrange(-2, 6) if r < 0.8 else rng.choice(BIG_INTS + [2**63 - 1, -(2**63)])
        out = run(lambda: "OK " + fmt(out_codes(kind, np.strings.replace(arr(kind, hay, rng), arr(kind, old, rng), arr(kind, new, rng), np.int64(count)))))
        return f"replace {kind} {fmt(hay)} {fmt(old)} {fmt(new)} {count}", out
    sep = rand_needle(rng, kind, hay)
    f = np.strings.partition if op == "partition" else np.strings.rpartition
    out = run(lambda: part_res(kind, f(arr(kind, hay, rng), arr(kind, sep, rng))))
    return f"{op} {kind} {fmt(hay)} {fmt(sep)}", out


if __name__ == "__main__":
    main(gen, exe="npdiff_strings")
