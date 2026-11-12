import warnings
import numpy as np

warnings.simplefilter("ignore")
M = 2**63 - 1
try:
    np.pad(np.zeros((4, 4)), M)
    scalar = ""
except ValueError as e:
    scalar = str(e)
try:
    np.pad(np.zeros((4, 4)), [[M, M], [M, M]])
    nested = ""
except ValueError as e:
    nested = str(e)
print("REPRODUCED" if "could not broadcast input array" in scalar and "Maximum allowed dimension exceeded" in nested else "NOT REPRODUCED")
