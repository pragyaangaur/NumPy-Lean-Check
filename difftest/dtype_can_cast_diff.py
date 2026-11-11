"""Differential test for `np.can_cast(from, to, casting)` on dtype arguments, for all five casting levels at once (convert_datatype.c:728 and the cast implementations)."""
from dtype_common import rand_token, to_dtype
from harness import main
import numpy as np

LEVELS = ["no", "equiv", "safe", "same_kind", "unsafe"]


def gen(rng):
    a = rand_token(rng)
    if rng.random() < 0.3 and a[0] in "SU":
        # Same kind of string with a nearby length, where the level changes.
        b = rng.choice([a[0], "S", "U"]) + str(max(0, int(a[1:]) + rng.randrange(-2, 3)))
    else:
        b = rand_token(rng)
    bits = "".join("1" if np.can_cast(to_dtype(a), to_dtype(b), c) else "0" for c in LEVELS)
    return f"can_cast {a} {b}", bits


if __name__ == "__main__":
    main(gen, exe="npdiff_dtype")
