import numpy as np

try:
    shape = np.zeros(6).reshape(-5, 2).shape
except ValueError:
    shape = None
print("REPRODUCED" if shape == (3, 2) else "NOT REPRODUCED")
