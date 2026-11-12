import warnings

import numpy as np

# The float32 limit is 2**128 - 2**104. Integers from 2**128 - 2**103 on round to infinity, the ones below round to the limit.
v = 2**128 - 2**103 - 2**73
with warnings.catch_warnings():
    warnings.simplefilter("ignore")
    stored = np.asarray(v, dtype=np.float32)
print("REPRODUCED" if np.isinf(stored) and v < 2**128 - 2**103 else "NOT REPRODUCED")
