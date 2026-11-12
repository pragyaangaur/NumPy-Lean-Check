import numpy as np

dt = np.dtype([("a", ("u1", (3,)), (2,))])
a = np.zeros(1, dt)
try:
    np.array(memoryview(a))
    print("NOT REPRODUCED")
except ValueError as e:
    print("REPRODUCED" if "is not a valid PEP 3118" in str(e) else "NOT REPRODUCED")
