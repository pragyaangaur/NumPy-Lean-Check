"""Shared helpers for the broadcast differential tests."""
import re

BIG = [2**31, 2**32, 2**61, 2**62, 2**63 - 1, 3037000500, 4611686018427387904, 2**63, -2**63 - 1]
MISMATCH = re.compile(r"Mismatch is between arg (\d+) with shape .* and arg (\d+) with shape")


def classify(e):
    """Map a NumPy exception to the error token that the Lean handlers print."""
    msg = str(e)
    m = MISMATCH.search(msg)
    if m:
        return f"ERR mismatch {m.group(1)} {m.group(2)}"
    table = [
        ("broadcast dimensions too large", "ERR bcastlarge"),
        ("at most 64 array objects", "ERR toomany"),
        ("maximum supported dimension", "ERR maxdims"),
        ("Maximum allowed dimension exceeded", "ERR conv"),
        ("negative dimensions are not allowed", "ERR negative"),
        ("must be non-negative", "ERR negative"),
        ("array is too big", "ERR toobig"),
        ("non-scalar to a scalar", "ERR scalar"),
        ("more dimensions than allowed", "ERR opndim"),
        ("could not be broadcast together with remapped shapes", "ERR iterbcast"),
        ("iterator is too large", "ERR iterlarge"),
        ("only supports up to 32 dimensions", "ERR legacydims"),
        ("Unable to avoid creating a copy", "ERR copy"),
        ("cannot reshape array", "ERR mismatch"),
        ("too large to convert to C int", "ERR cint"),
        ("won't fit into a C int", "ERR cint"),
        ("too large to convert to C long", "ERR cint"),
        ("out of bounds for array of dimension", "ERR axis"),
        ("repeated axis", "ERR repeated"),
        ("duplicate value in 'axis'", "ERR repeated"),
        ("same number of elements", "ERR lengths"),
        ("axes don't match array", "ERR axesmismatch"),
        ("size not equal to one", "ERR notone"),
    ]
    for key, tok in table:
        if key in msg:
            return tok
    return f"UNKNOWN {type(e).__name__}: {msg[:200]}"


def dim(rng, big=0.05):
    r = rng.random()
    if r < big:
        return rng.choice(BIG)
    if r < big + 0.04:
        return -rng.randrange(1, 4)
    return rng.choice([0, 1, 1, 1, 1, 2, 2, 3, 3, 4, 5])
