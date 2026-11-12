import numpy as np

inner = np.dtype({"names": ["a"], "formats": ["<i4"], "offsets": [0], "itemsize": 6})
dt = np.dtype({"names": ["x", "y"], "formats": [(inner, (2,)), "<i4"], "offsets": [0, 12], "itemsize": 16})
a = np.zeros(1, dt)
a["x"]["a"] = [[11, 22]]
a["y"] = 99
b = np.array(memoryview(a))
same = (a["x"]["a"] == b["x"]["a"]).all() and (a["y"] == b["y"]).all()
print("NOT REPRODUCED" if same else "REPRODUCED")
