import numpy as np

a = np.array([2**63 - 1970], dtype="M8[Y]")
year_nat = np.datetime_as_string(a)[0] == "NaT" and not np.isnat(a)[0]
week = np.datetime_as_string(np.array([2**61], dtype="M8[W]"))[0]
print("REPRODUCED" if year_nat and week.startswith("-") else "NOT REPRODUCED")
