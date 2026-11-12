import numpy as np

try:
    np.strings.center(np.array(["a"]), 2**32)
    kind = None
except Exception as e:
    kind = type(e).__name__
try:
    np.strings.center(np.array(["a"], dtype=np.dtypes.StringDType()), 2**62)
    kind2 = None
except Exception as e:
    kind2 = type(e).__name__
print("REPRODUCED" if kind == "TypeError" and kind2 == "MemoryError" else "NOT REPRODUCED")
