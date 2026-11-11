import warnings

import numpy as np


def overflow_warned(f):
    with warnings.catch_warnings(record=True) as caught, np.errstate(over="warn"):
        warnings.simplefilter("always")
        value = f()
    return int(value), any("overflow" in str(w.message) for w in caught)


mul = overflow_warned(lambda: np.int8(100) * np.int8(100))
power = overflow_warned(lambda: np.int8(100) ** np.int8(2))
# Same wrapped value, but only the multiply warns.
print("REPRODUCED" if mul == (16, True) and power == (16, False) else "NOT REPRODUCED")
