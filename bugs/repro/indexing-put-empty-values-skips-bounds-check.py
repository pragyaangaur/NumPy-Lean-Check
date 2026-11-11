import numpy as np

try:
    np.put(np.arange(3), [100], [])
    raised = False
except IndexError:
    raised = True
print("REPRODUCED" if not raised else "NOT REPRODUCED")
