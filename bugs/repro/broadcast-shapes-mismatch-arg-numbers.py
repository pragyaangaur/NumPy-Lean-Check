import numpy as np

try:
    np.broadcast_shapes(*[()] * 64, (2,), (3,))
    msg = ""
except ValueError as e:
    msg = str(e)
print("REPRODUCED" if "arg 1 with shape (2,) and arg 2 with shape (3,)" in msg else "NOT REPRODUCED")
