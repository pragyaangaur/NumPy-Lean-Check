"""Differential test for the PEP 3118 buffer format round trip.

Three kinds of case run against `npdiff_npyformat`:

- `pep3118_format <n> <dtype>` compares `memoryview(np.zeros(n, dtype)).format` (buffer.c:191, `_buffer_format_string`) or the error kind.
- `pep3118_roundtrip <n> <dtype>` compares the canonical form of `np.array(memoryview(np.zeros(n, dtype))).dtype`, which runs the C fast path (buffer.c:1002), `_dtype_from_pep3118` (_core/_internal.py:627) and the item size check (ctors.c:1245), or the error kind.
- `pep3118_parse <hex>` compares `_dtype_from_pep3118(spec)` on strings that come from the writer or from random mutations of its alphabet, which also reaches the parser's error paths.

A dtype goes over the wire as `<order><char>[length]` for a scalar, `A<dim>x<dim>(<base>)` for a subarray and `T<itemsize>{<hex name>@<offset>@<dtype>;...}` for a structured dtype. The canonical form uses the same notation with `byteorder`, `kind` and `itemsize` for scalars. Structured dtypes with object fields only run the format test, because a round trip that changes their layout makes NumPy read garbage pointers and crash. Arrays are one dimensional of length `n` from one to three and stay far below 1 kB.
"""
import atexit
import collections
import warnings

import numpy as np
from harness import main
from numpy._core import _internal

warnings.simplefilter("ignore")

TALLY = collections.Counter()
atexit.register(lambda: print("detail", dict(sorted(TALLY.items()))))

SCALARS = list("?bBhHiIlLqQefdgFDG") + ["S", "U", "V", "O", "M", "m"]
ORDERS = ["=", "<", ">", "|"]
NAMES = ["a", "b", "c", "d", "x", "y", "f0", "f1", "ab", "name", "x1", "A", "z z", "(", "}", "T{", "3", "ü"]


def rand_scalar(rng):
    c = rng.choice(SCALARS)
    if c in "SUV":
        n = rng.choice([1, 1, 2, 3, 4, 5]) if c != "V" else rng.choice([0, 1, 2, 3, 4, 5, 7, 8])
        spec = c + str(n)
    elif c == "M":
        spec = "M8[s]"
    elif c == "m":
        spec = "m8[s]"
    else:
        spec = c
    if c in "?bBSVO":
        order = "|"
    else:
        order = rng.choice(ORDERS[:3])
    try:
        return np.dtype(order + spec)
    except TypeError:
        return np.dtype(spec)


def rand_dtype(rng, depth):
    r = rng.random()
    if depth <= 0 or r < 0.45:
        return rand_scalar(rng)
    if r < 0.62:
        base = rand_dtype(rng, depth - 1)
        shape = tuple(rng.choice([0, 1, 1, 2, 2, 3]) for _ in range(rng.choice([1, 1, 1, 2, 3])))
        try:
            return np.dtype((base, shape))
        except (ValueError, TypeError):
            return base
    return rand_struct(rng, depth)


def rand_struct(rng, depth):
    k = rng.choice([0, 1, 1, 2, 2, 2, 3, 3, 4])
    names = rng.sample(NAMES[:12], k) if rng.random() < 0.9 else rng.sample(NAMES, k)
    if rng.random() < 0.03 and k:
        names[rng.randrange(k)] = rng.choice(["a:b", ":", "q:"])
    formats, offsets = [], []
    end = 0
    for _ in range(k):
        f = rand_dtype(rng, depth - 1)
        if f.names is not None and f.itemsize == 0 and not f.names:
            f = rand_scalar(rng)
        gap = 0 if rng.random() < 0.55 else rng.choice([1, 1, 2, 3, 4, 7])
        if rng.random() < 0.25:
            a = max(f.alignment, 1)
            off = -(-(end + gap) // a) * a
        else:
            off = end + gap
        if rng.random() < 0.02:
            off = max(0, off - rng.choice([1, 2, 4, 8]))
        formats.append(f)
        offsets.append(off)
        end = max(end, off + f.itemsize) if rng.random() < 0.98 else off + f.itemsize
    tail = 0 if rng.random() < 0.6 else rng.choice([1, 1, 2, 3, 4, 8])
    spec = {"names": names, "formats": formats, "offsets": offsets, "itemsize": max(end + tail, max([o + f.itemsize for o, f in zip(offsets, formats)], default=0))}
    try:
        return np.dtype(spec)
    except (ValueError, TypeError):
        return np.dtype("i4")


def wire(dt):
    if dt.subdtype is not None:
        base, shape = dt.subdtype
        return "A" + "x".join(map(str, shape)) + "(" + wire(base) + ")"
    if dt.names is not None:
        parts = []
        for nm in dt.names:
            f, off = dt.fields[nm][:2]
            parts.append(nm.encode().hex() + "@" + str(off) + "@" + wire(f))
        return "T" + str(dt.itemsize) + "{" + ";".join(parts) + "}"
    tail = ""
    if dt.char in "SV":
        tail = str(dt.itemsize)
    elif dt.char == "U":
        tail = str(dt.itemsize // 4)
    return dt.byteorder + dt.char + tail


def canon(dt):
    if dt.subdtype is not None:
        base, shape = dt.subdtype
        return "A" + "x".join(map(str, shape)) + "(" + canon(base) + ")"
    if dt.names is not None:
        parts = []
        for nm in dt.names:
            f, off = dt.fields[nm][:2]
            parts.append(nm.encode().hex() + "@" + str(off) + "@" + canon(f))
        return "T" + str(dt.itemsize) + "{" + ";".join(parts) + "}"
    return dt.byteorder + dt.kind + str(dt.itemsize)


def format_error(e):
    m = str(e)
    if "cannot include dtype" in m:
        return "ERR notinbuffer"
    if "native-only" in m:
        return "ERR nativeonly"
    if "overlapping or out-of-order" in m:
        return "ERR overlap"
    if "':' is not an allowed" in m:
        return "ERR colon"
    return "ERR OTHER " + m[:80]


def make_array(dt, n):
    try:
        return np.zeros(n, dt), None
    except Exception as e:
        return None, "ERR NPZEROS " + type(e).__name__ + str(e)[:60]


def expect_format(dt, n):
    a, err = make_array(dt, n)
    if err:
        return err
    try:
        return "OK " + memoryview(a).format.encode().hex()
    except ValueError as e:
        return format_error(e)


def expect_roundtrip(dt, n):
    a, err = make_array(dt, n)
    if err:
        return err
    try:
        m = memoryview(a)
    except ValueError as e:
        return format_error(e)
    try:
        return "OK " + canon(np.array(m).dtype)
    except RuntimeError as e:
        return "ERR itemsize" if "does not match the dtype" in str(e) else "ERR OTHER " + str(e)[:80]
    except ValueError as e:
        return "ERR parse" if "is not a valid PEP 3118" in str(e) else "ERR OTHER " + str(e)[:80]


def parse_outcome(spec):
    try:
        return "OK " + canon(_internal._dtype_from_pep3118(spec))
    except ValueError:
        return "ERR value"
    except NotImplementedError:
        return "ERR notimpl"
    except RuntimeError:
        return "ERR runtime"
    except IndexError:
        return "ERR index"
    except KeyError:
        return "ERR key"
    except Exception as e:
        return "ERR OTHER " + type(e).__name__ + str(e)[:60]


TOKENS = ["@", "=", "<", ">", "^", "!", "?", "c", "b", "B", "h", "H", "i", "I", "l", "L", "q", "Q", "e", "f", "d", "g",
          "Zf", "Zd", "Zg", "Z", "s", "w", "x", "O", "u", "&", "t", "X", "n", "N", "T{", "T", "{", "}", "(2)", "(2,3)", "(1)",
          "(0)", "(", ")", ",", "-1", "(-1)", "(a)", "()", "(2,)", ":a:", ":b:", ":", ":x1:", "0", "1", "2", "3", "5", "12"]


def rand_spec(rng):
    r = rng.random()
    if r < 0.5:
        dt = rand_dtype(rng, 2)
        n = rng.choice([1, 2, 3])
        a, err = make_array(dt, n)
        try:
            spec = memoryview(a).format if not err else None
        except ValueError:
            spec = None
        if spec is not None and rng.random() < 0.55:
            return spec
        base = spec if spec is not None else ""
        # mutate: delete, duplicate, replace or insert a token
        out = list(base)
        for _ in range(rng.choice([1, 1, 2, 3])):
            op = rng.random()
            i = rng.randrange(len(out) + 1)
            if op < 0.3 and out:
                del out[min(i, len(out) - 1)]
            elif op < 0.6:
                out.insert(i, rng.choice(TOKENS))
            elif out:
                out[min(i, len(out) - 1)] = rng.choice(TOKENS)
        return "".join(out)
    k = rng.choice([1, 2, 3, 4, 5, 6, 8])
    return "".join(rng.choice(TOKENS) for _ in range(k))


def gen(rng):
    r = rng.random()
    if r < 0.6:
        dt = rand_dtype(rng, 3)
        if dt.subdtype is not None:
            dt = rand_struct(rng, 2)
        n = rng.choice([1, 1, 2, 3])
        w = wire(dt)
        # A structured dtype with an object field can read garbage pointers when the round trip changes the layout, and then NumPy crashes (see the record npyformat-pep3118-struct-padding-dropped), so those only get the format test.
        if r < 0.28 or (dt.hasobject and dt.names is not None):
            out = expect_format(dt, n)
            line = f"pep3118_format {n} {w}"
            TALLY["format " + out.split(" ")[0] + (" " + out.split(" ")[1] if out.startswith("ERR") else "")] += 1
        else:
            out = expect_roundtrip(dt, n)
            line = f"pep3118_roundtrip {n} {w}"
            key = out.split(" ")[0] + (" " + out.split(" ")[1] if out.startswith("ERR") else "")
            if out.startswith("OK"):
                key += " same" if out == "OK " + canon(dt) else " changed"
            TALLY["roundtrip " + key] += 1
        return line, out
    spec = rand_spec(rng)
    if not spec.isascii() or any(ch.isspace() for ch in spec):
        spec = spec.encode("ascii", "ignore").decode().replace(" ", "")
    if not spec:
        spec = "i"
    out = parse_outcome(spec)
    TALLY["parse " + (out.split(" ")[0] + (" " + out.split(" ")[1] if out.startswith("ERR") else ""))] += 1
    return f"pep3118_parse {spec.encode().hex()}", out


if __name__ == "__main__":
    main(gen, exe="npdiff_npyformat")
