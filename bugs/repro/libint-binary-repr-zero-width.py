import numpy as np

empty = np.binary_repr(0, width=-1) == ""
try:
    np.binary_repr(1, width=0)
    one_raises = False
except ValueError:
    one_raises = True
zero_ok = np.binary_repr(0, width=0) == "0"
print("REPRODUCED" if empty or (one_raises and zero_ok) else "NOT REPRODUCED")
