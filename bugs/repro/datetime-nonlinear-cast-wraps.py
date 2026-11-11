import numpy as np

try:
    np.array(["2300-01-01"], dtype="M8[D]").astype("M8[ns]")
    linear_raises = False
except OverflowError:
    linear_raises = True
try:
    back = np.array(["2300"], dtype="M8[Y]").astype("M8[ns]").astype("M8[Y]")
    wrapped = back[0] != np.datetime64("2300", "Y")
except OverflowError:
    wrapped = False
print("REPRODUCED" if linear_raises and wrapped else "NOT REPRODUCED")
