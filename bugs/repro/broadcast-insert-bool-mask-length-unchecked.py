import numpy as np

a = np.arange(3)
mask = np.array([False] * 5)
inserted = np.insert(a, mask, 9).tolist()
try:
    np.delete(a, mask)
    deleted = "accepted"
except ValueError:
    deleted = "ValueError"
print("REPRODUCED" if inserted == [0, 1, 2] and deleted == "ValueError" else "NOT REPRODUCED")
