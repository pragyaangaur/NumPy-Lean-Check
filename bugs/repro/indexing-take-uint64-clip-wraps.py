import numpy as np

r = np.take(np.arange(3), np.array([2**64 - 1], dtype=np.uint64), mode="clip")
print("REPRODUCED" if int(r[0]) == 0 else "NOT REPRODUCED")
