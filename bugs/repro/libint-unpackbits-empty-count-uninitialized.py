import numpy as np

# NumPy keeps a cache of small data buffers. Freeing an 8-byte buffer full of 0xAB makes the next 8-byte output likely to reuse it, which shows that the output is never written.
bad = False
for _ in range(100):
    junk = np.full(8, 0xAB, dtype=np.uint8)
    del junk
    out = np.unpackbits(np.empty((0, 1), np.uint8), axis=0, count=8)
    if out.shape == (8, 1) and out.any():
        bad = True
        break
print("REPRODUCED" if bad else "NOT REPRODUCED")
