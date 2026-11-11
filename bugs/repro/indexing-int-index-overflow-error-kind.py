import numpy as np


def kind(i):
    try:
        np.arange(5)[i]
    except Exception as e:
        return type(e).__name__
    return "none"


print("REPRODUCED" if kind(2**63) == "OverflowError" and kind(2**64) == "IndexError" else "NOT REPRODUCED")
