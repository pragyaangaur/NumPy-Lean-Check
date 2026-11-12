import warnings

import numpy as np

big = 2**1024
with warnings.catch_warnings(record=True) as w:
    warnings.simplefilter("always")
    real = np.asarray(big, dtype=np.longdouble)
    real_ok = bool(np.isinf(real)) and any(issubclass(x.category, RuntimeWarning) for x in w)
try:
    np.asarray(big, dtype=np.clongdouble)
    print("NOT REPRODUCED")
except OverflowError:
    print("REPRODUCED" if real_ok else "NOT REPRODUCED")
