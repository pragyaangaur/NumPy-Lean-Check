import numpy as np

ok = np.broadcast_shapes((0, 2**62, 2)) == (0, 2**62, 2)
try:
    np.broadcast_shapes((2**62, 2, 0))
    late_zero_fails = False
except ValueError:
    late_zero_fails = True
print("REPRODUCED" if ok and late_zero_fails else "NOT REPRODUCED")
