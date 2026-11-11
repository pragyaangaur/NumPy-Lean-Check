import numpy as np

clip = int(np.ravel_multi_index((2**63,), (3,), mode="clip"))
wrap = int(np.ravel_multi_index((2**63,), (3,), mode="wrap"))
print("REPRODUCED" if clip != 2 or wrap != 2**63 % 3 else "NOT REPRODUCED")
