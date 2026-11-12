import numpy as np

try:
    np.frombuffer(bytes(8), dtype="i8", count=2**61 + 1)
    print("NOT REPRODUCED")
except ValueError as e:
    # The size test of ctors.c:3809 should refuse this with "buffer is smaller than requested size".
    print("REPRODUCED" if "too big" in str(e) else "NOT REPRODUCED")
