import numpy as np

a = np.array([2**62 + 1], dtype=np.int64)
b = np.array([2**62] * 10, dtype=np.uint64)
sort = np.isin(a, b, kind="sort")
table = np.isin(a, b, kind="table")
default = np.isin(a, np.array([0] + [2**62] * 10, dtype=np.uint64))
print("REPRODUCED" if bool(sort[0]) != bool(table[0]) or bool(default[0]) else "NOT REPRODUCED")
