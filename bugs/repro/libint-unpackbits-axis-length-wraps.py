import numpy as np

try:
    shape = np.unpackbits(np.empty((2**61, 0), np.uint8), axis=0).shape
except ValueError:
    shape = None
print("REPRODUCED" if shape == (0, 0) else "NOT REPRODUCED")
