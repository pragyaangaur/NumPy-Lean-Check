import numpy as np

kinds = []
for f in (np.split, np.array_split):
    try:
        f(np.arange(4), 0)
        kinds.append("none")
    except Exception as e:
        kinds.append(type(e).__name__)
print("REPRODUCED" if kinds == ["ZeroDivisionError", "ValueError"] else "NOT REPRODUCED")
