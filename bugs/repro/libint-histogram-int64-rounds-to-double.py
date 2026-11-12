import numpy as np

# 2**61 - 1 is below the middle edge 2**61, so the exact answer is one value in the lower bin.
signed = np.histogram(np.array([2**61 - 1], dtype=np.int64), bins=2, range=(0, 2**62))[0].tolist()
unsigned = np.histogram(np.array([2**61 - 1], dtype=np.uint64), bins=2, range=(0, 2**62))[0].tolist()
print("REPRODUCED" if signed == [0, 1] and unsigned == [0, 1] else "NOT REPRODUCED")
