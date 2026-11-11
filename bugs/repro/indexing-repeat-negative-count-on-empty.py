import numpy as np

try:
    np.repeat(np.arange(0), -5)
    raised = False
except ValueError:
    raised = True
print("REPRODUCED" if not raised else "NOT REPRODUCED")
