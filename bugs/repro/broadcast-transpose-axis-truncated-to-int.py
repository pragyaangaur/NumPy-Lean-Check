import numpy as np

a = np.zeros((2, 3))
try:
    shapes = (np.transpose(a, (2**32, 1)).shape, a.transpose(2**32 + 1, 2**33).shape)
except (ValueError, OverflowError, IndexError):
    shapes = None
print("REPRODUCED" if shapes == ((2, 3), (3, 2)) else "NOT REPRODUCED")
