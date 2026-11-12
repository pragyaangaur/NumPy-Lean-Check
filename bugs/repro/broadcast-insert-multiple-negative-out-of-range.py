import numpy as np

a = np.arange(3)
try:
    np.insert(a, -5, 9)
    single = "accepted"
except IndexError:
    single = "IndexError"
try:
    multi = np.insert(a, [-5, 1], 9).tolist()
except IndexError:
    multi = "IndexError"
print("REPRODUCED" if single == "IndexError" and multi == [0, 1, 9, 9, 2] else "NOT REPRODUCED")
