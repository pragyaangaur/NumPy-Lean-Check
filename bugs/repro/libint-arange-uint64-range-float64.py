import numpy as np

a = np.arange(2**63, 2**63 + 3)
print("REPRODUCED" if a.dtype == np.float64 and len(set(a.tolist())) < 3 else "NOT REPRODUCED")
