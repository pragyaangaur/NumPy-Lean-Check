import numpy as np

late = np.broadcast_shapes(*[()] * 64, (2**61,))
try:
    early = np.broadcast_shapes((2**61,), *[()] * 64)
except ValueError:
    early = None
print("REPRODUCED" if late == (2**61,) and early is None else "NOT REPRODUCED")
