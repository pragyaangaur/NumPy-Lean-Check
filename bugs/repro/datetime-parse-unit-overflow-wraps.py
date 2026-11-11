import warnings

import numpy as np

warnings.simplefilter("ignore")
try:
    d = np.datetime64("2300-01-01", "ns")
    wrapped = d.astype("M8[D]") != np.datetime64("2300-01-01")
except OverflowError:
    wrapped = False
print("REPRODUCED" if wrapped else "NOT REPRODUCED")
