"""Differential test for `np.promote_types` (convert_datatype.c:1075) on numeric, object, bytes and unicode dtypes."""
from dtype_common import fmt_dtype, rand_token, to_dtype
from harness import main
import numpy as np


def gen(rng):
    a = rand_token(rng)
    b = rand_token(rng)
    try:
        out = "OK " + fmt_dtype(np.promote_types(to_dtype(a), to_dtype(b)))
    except TypeError:
        out = "ERR promotion"
    return f"promote {a} {b}", out


if __name__ == "__main__":
    main(gen, exe="npdiff_dtype")
