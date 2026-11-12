import numpy as np

a = np.arange(3)
ok = np.insert(a, np.array([True, False, True]), 9).tolist() == [9, 0, 1, 9, 2]
try:
    np.insert(a, [True, False, True], 9)
    msg = ""
except AttributeError as e:
    msg = str(e)
print("REPRODUCED" if ok and "has no attribute 'ndim'" in msg else "NOT REPRODUCED")
