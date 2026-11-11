"""Differential test for `_wrap_header`, `_wrap_header_guess_version` and `_write_array_header` (lib/_format_impl.py:397 to 480)."""
import io

import numpy as np
from harness import fmt_ints, main
from npyformat_common import DESCR_CHARS, fmt, hx, hx_text, ver_name

VERSIONS = [None, (1, 0), (2, 0), (3, 0)]
BIG = [2**31, 2**32, 2**62, 2**63 - 1, 2**63, 2**64 - 1, 10**20, 10**21, 10**22, 10**30]


def describe(fn):
    try:
        b = fn()
    except UnicodeEncodeError:
        return "ERR unicode", None
    except ValueError as e:
        if "too big" in str(e):
            return "ERR toobig", None
        raise
    nb = 2 if b[6] == 1 else 4
    hfield = int.from_bytes(b[8:8 + nb], "little")
    return (b[6], b[7], hfield, len(b)), b


def gen_wrap(rng):
    v = rng.choice(VERSIONS)
    r = rng.random()
    if r < 0.5:
        n = rng.randrange(0, 140)
    elif r < 0.8:
        n = rng.randrange(0, 600)
    elif r < 0.98:
        n = rng.choice([65535 - 10, 65535 - 9, 65535 - 8, 65535 - 7, 65535 - 6, 65535 - 5, 65535 - 4, 65535 - 3, 65535 - 2, 65535 - 1, 65535, 65536, 65536 + 63, 65536 + 64, 65536 + 65]) - rng.randrange(0, 3) * rng.randrange(0, 40)
        n = max(n, 0)
    else:
        n = rng.randrange(65000, 70000)
    alphabet = [chr(c) for c in range(33, 127)]
    if rng.random() < 0.3:
        alphabet += ["é", "ÿ"]
    if rng.random() < 0.15:
        alphabet += ["Ā", "日", "\U0001f600"]
    k = min(n, rng.choice([0, 1, 2, 5, 20, 60]))
    text = "".join(rng.choice(alphabet) for _ in range(k))
    fill = n - k
    h = text + " " * fill
    # The length is counted in characters. With wide characters the encoded size differs, which is the point.
    line = f"npy_wrap {ver_name(v)} {hx_text(text)} {fill}"
    if v is None:
        fn = lambda: fmt._wrap_header_guess_version(h)
    else:
        fn = lambda: fmt._wrap_header(h, v)
    res, b = describe(fn)
    if b is None:
        return line, res
    enc = "utf8" if b[6] == 3 else "latin1"
    nb = 2 if b[6] == 1 else 4
    body = b[8 + nb:]
    he = h.encode(enc)
    assert body.startswith(he) and body.endswith(b"\n") and set(body[len(he):-1]) <= {32}
    assert (8 + nb + len(body)) % 64 == 0
    padlen = len(body) - len(he) - 1
    return line, "OK %d %d %d %d %d" % (res + (padlen,))


def gen_shape(rng):
    r = rng.random()
    if r < 0.05:
        n = rng.randrange(0, 4) + rng.choice([0, 0, 0, 6000, 22000, 22500, 23500])
    else:
        n = rng.randrange(0, 5)
    out = []
    for _ in range(n):
        q = rng.random()
        if q < 0.35:
            out.append(rng.randrange(0, 10))
        elif q < 0.5:
            out.append(rng.randrange(0, 100000))
        elif q < 0.65:
            out.append(rng.choice(BIG))
        elif q < 0.75:
            out.append(-rng.choice([1, 2, 3, 10**5, 10**20, 10**19]))
        else:
            out.append(rng.randrange(0, 10**rng.randrange(1, 22)))
    return out


def gen_descr(rng):
    r = rng.random()
    if r < 0.4:
        return rng.choice(["<f8", "|u1", "<i4", ">f4", "|b1", "<U5", "|S3", "<M8[ns]", "<c16", "|O"])
    n = rng.choice([1, 2, 3, 5, 10, 40, 300])
    if r < 0.5:
        n = rng.choice([70000, 140000]) if rng.random() < 0.02 else n
    chars = DESCR_CHARS if rng.random() < 0.6 else DESCR_CHARS[:95]
    if rng.random() < 0.2:
        chars = ["'", "'", '"', "\\", "a", "b"]
    return "".join(rng.choice(chars) for _ in range(n))


def gen_write(rng):
    v = rng.choice(VERSIONS)
    fortran = rng.random() < 0.4
    shape = gen_shape(rng)
    descr = gen_descr(rng)
    line = f"npy_write {ver_name(v)} {int(fortran)} {fmt_ints(shape)} {hx_text(descr)}"
    d = {"descr": descr, "fortran_order": fortran, "shape": tuple(shape)}

    def fn():
        bio = io.BytesIO()
        fmt._write_array_header(bio, d, v)
        return bio.getvalue()

    res, b = describe(fn)
    if b is None:
        return line, res
    nb = 2 if b[6] == 1 else 4
    body = b[8 + nb:].rstrip(b" \n")
    return line, "OK %d %d %d %d %s" % (res + (body.hex() if body else "_",))


def gen(rng):
    return gen_wrap(rng) if rng.random() < 0.5 else gen_write(rng)


if __name__ == "__main__":
    main(gen, exe="npdiff_npyformat")
