import numpy as np

dt = np.dtype([("a", "i4"), ("b", "i1")])
longer = np.array(memoryview(np.zeros(2, dt))).dtype == dt
try:
    np.array(memoryview(np.zeros(1, dt)))
    print("NOT REPRODUCED")
except RuntimeError as e:
    print("REPRODUCED" if longer and "does not match the dtype" in str(e) else "NOT REPRODUCED")
