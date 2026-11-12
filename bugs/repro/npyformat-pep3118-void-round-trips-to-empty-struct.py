import numpy as np

a = np.zeros(3, "V4")
b = np.array(memoryview(a))
print("REPRODUCED" if b.dtype != a.dtype and b.dtype.names == () else "NOT REPRODUCED")
