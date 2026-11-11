import numpy as np

print("REPRODUCED" if np.base_repr(0, padding=2) == "00" or np.base_repr(0, padding=-1) == "" else "NOT REPRODUCED")
