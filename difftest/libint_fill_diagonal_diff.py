"""Differential test for `np.fill_diagonal` (_index_tricks_impl.py:905) on tiny arrays.

Shapes have one to five dimensions with lengths from 0 to 6 for two dimensions and from 0 to 4 for more. About half of the N-d shapes have all lengths equal, since otherwise the call raises. `wrap` is True or False. The array is zeros of dtype int64 and the value is 1, so the written flat indices are the non-zero positions. The two error messages are told apart by their text.
"""
import numpy as np
from harness import fmt_ints, main


def gen(rng):
    nd = rng.choice([0, 1, 2, 2, 2, 3, 3, 4, 5])
    if nd == 2:
        shape = [rng.choice([0, 1, 2, 3, 4, 5, 6, rng.randrange(7)]) for _ in range(2)]
    elif nd > 2:
        if rng.random() < 0.6:
            shape = [rng.randrange(0, 5 if nd <= 4 else 4)] * nd
        else:
            shape = [rng.randrange(0, 4) for _ in range(nd)]
    else:
        shape = [rng.randrange(0, 4) for _ in range(nd)]
    wrap = rng.random() < 0.5
    line = f"filldiag {fmt_ints(shape)} {int(wrap)}"
    a = np.zeros(shape, dtype=np.int64)
    try:
        np.fill_diagonal(a, 1, wrap=wrap)
        out = f"OK {fmt_ints(np.flatnonzero(a))}"
    except ValueError as e:
        msg = str(e)
        out = "ERR ndim" if "at least 2-d" in msg else "ERR dims" if "equal length" in msg else "ERR " + msg
    return line, out


if __name__ == "__main__":
    main(gen, exe="npdiff_libint")
