import numpy as np

try:
    r = tuple(int(x) for x in np.unravel_index(5, (-2, -3)))
except ValueError:
    r = None
print("REPRODUCED" if r is not None and min(r) < 0 else "NOT REPRODUCED")
