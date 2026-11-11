"""Differential test for the contiguity flags computed by `_UpdateContiguousFlags` (`_core/src/multiarray/flagsobject.c:115`) on views made with `as_strided`."""
from harness import fmt_bool, fmt_ints, main
from broadcast_strided import make, strided


def gen(rng):
    dims, strides, dt = strided(rng)
    a = make(dims, strides, dt)
    line = f"flags {fmt_ints(dims)} {fmt_ints(strides)} {dt.itemsize}"
    return line, f"{fmt_bool(a.flags.c_contiguous)} {fmt_bool(a.flags.f_contiguous)}"


if __name__ == "__main__":
    main(gen, exe="npdiff_broadcast")
