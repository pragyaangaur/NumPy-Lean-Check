"""Differential test for the count and offset checks of `np.frombuffer` (ctors.c:3714). The buffer is a bytes object of at most 64 bytes, so no case reads or allocates anything large."""
import numpy as np
from harness import main

CODES = ["i1", "u1", "i2", "u2", "i4", "f4", "i8", "u8", "f8", "c8", "c16", "f2", "S1", "S3", "S7", "U1", "U3", "V1", "V5", "V13",
         "M8", "m8", "b1", "O", "S0", "U0", "V0"]
COUNTS = [-1, -1, -2, -2**63, 2**63 - 1, 2**63, -2**63 - 1, 2**62, 2**61, 2**61 + 1, 2**60, 2**60 + 1, 2**32, 2**31, 2**64, 2**63 + 8,
          2**56, 2**57 + 1, 2**58, 2**59 + 1]
OFFSETS = [0, 0, 0, -1, -2**63, 2**63 - 1, 2**63, 2**62, 2**31, -2**63 - 1]


def gen(rng):
    length = rng.choice([0, 1, 2, 3, 4, 7, 8, 9, 16, 24, 31, 32, 33, 63, 64, rng.randrange(0, 65)])
    code = rng.choice(CODES)
    r = rng.random()
    count = rng.choice(COUNTS) if r < 0.35 else rng.randrange(-1, 20) if r < 0.9 else rng.randrange(0, 2**rng.randrange(1, 64))
    r = rng.random()
    offset = rng.choice(OFFSETS) if r < 0.3 else rng.randrange(0, length + 3) if r < 0.9 else rng.randrange(-3, 70)
    line = f"frombuffer {length} {code} {count} {offset}"
    try:
        a = np.frombuffer(bytes(length), dtype=np.dtype(code), count=count, offset=offset)
        out = f"OK {a.shape[0]}"
    except OverflowError:
        out = "ERR overflow"
    except ValueError as e:
        m = str(e)
        out = ("ERR object" if "OBJECT" in m else "ERR unsized" if "cannot be zero" in m else "ERR offset" if "offset must" in m
               else "ERR multiple" if "multiple" in m else "ERR small" if "smaller than" in m else "ERR toobig" if "too big" in m
               else "ERR countunknown" if "cannot determine" in m else "ERR OTHER " + m[:60])
    return line, out


if __name__ == "__main__":
    main(gen, exe="npdiff_npyformat")
