import numpy as np

try:
    r = int(np.ravel_multi_index((1, 1), (-2, 3), mode="clip"))
except ValueError:
    r = None
print("REPRODUCED" if r is not None and r < 0 else "NOT REPRODUCED")
