"""Differential test for `np.digitize` (_function_base_impl.py:5766) with `int64` values and bins.

Bins are increasing, decreasing, constant or shuffled, and are built either from small numbers or from numbers next to `2**53`, `2**62` and `2**63 - 1`, where neighbouring `int64` values have the same double. The monotonicity check works on doubles, so those bins test the agreement between the check and the integer search.
"""
import numpy as np
from harness import fmt_ints, main

CENTRES = [0, 0, 2**53, 2**62, 2**63 - 8, -2**53, -2**63 + 4]


def gen(rng):
    c = rng.choice(CENTRES)
    spread = rng.choice([3, 3, 10])
    nb = rng.choice([0, 1, 2, 3, 4, rng.randrange(0, 9)])
    bins = [min(max(c + rng.randrange(-spread, spread + 1), -2**63), 2**63 - 1) for _ in range(nb)]
    shape = rng.random()
    if shape < 0.4:
        bins.sort()
    elif shape < 0.75:
        bins.sort(reverse=True)
    elif shape < 0.8:
        bins = [c] * nb
    nx = rng.randrange(0, 6)
    xs = [min(max(c + rng.randrange(-spread - 2, spread + 3), -2**63), 2**63 - 1) for _ in range(nx)]
    right = rng.random() < 0.5
    line = f"digitize {fmt_ints(xs)} {fmt_ints(bins)} {int(right)}"
    try:
        out = "OK " + fmt_ints(np.digitize(np.array(xs, dtype=np.int64), np.array(bins, dtype=np.int64), right=right))
    except ValueError:
        out = "ERR mono"
    return line, out


if __name__ == "__main__":
    main(gen, exe="npdiff_libint")
