import numpy as np

print("REPRODUCED" if np.datetime64(" -2000") == np.datetime64("2000") else "NOT REPRODUCED")
