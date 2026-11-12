import numpy as np

a = np.array([1], dtype=np.uint64)
edges = np.histogram_bin_edges(a, bins=2, range=(0, 2**64 - 1))
try:
    np.histogram(a, bins=2, range=(0, 2**64 - 1))
    failed = False
except OverflowError:
    failed = True
print("REPRODUCED" if len(edges) == 3 and failed else "NOT REPRODUCED")
