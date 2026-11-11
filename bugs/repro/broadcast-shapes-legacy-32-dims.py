import numpy as np

a = np.empty((1,) * 40)
fails = 0
for f in (lambda: np.broadcast_shapes((1,) * 33), lambda: np.broadcast_arrays(a, a)):
    try:
        f()
    except RuntimeError:
        fails += 1
ufunc_ok = (a + a).shape == (1,) * 40
print("REPRODUCED" if fails == 2 and ufunc_ok else "NOT REPRODUCED")
