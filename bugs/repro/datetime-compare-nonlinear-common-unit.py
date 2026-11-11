import numpy as np

year = np.datetime64("1971", "Y")
other = np.datetime64(26, "14D")
different_day = other.astype("M8[D]") != year.astype("M8[D]")
print("REPRODUCED" if bool(year == other) and different_day else "NOT REPRODUCED")
