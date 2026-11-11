"""Differential test for `_read_array_header` (lib/_format_impl.py:621) and the magic check on in-memory files.

Only the header functions run. The data section is never read, so a header that declares a huge shape costs nothing. The header text is built from tokens, mutated, and sent to both sides. A text that Python parses into a node type that the Lean parser does not model (calls, subscripts and so on) is left out, see `supported`.
"""
import ast
import io
import tokenize

import numpy as np
from harness import main
from npyformat_common import fmt, hx

KEYS = ["'descr'", "'fortran_order'", "'shape'"]
OTHER_KEYS = ["'foo'", "'Shape'", "1", "None", "'descr '", "'shape'", "'descr'", '"shape"', "[1]", "{}", "(1, [2])", "(1,)", "(1, 2)"]
DESCRS = ["'<f8'", "'|u1'", "'<i4'", "'>f4'", "'|b1'", "'<U5'", "'|S3'", "'<M8[ns]'", "'<c16'", "'|O'", "'=i8'", "'f4'",
          "'i'", "'b'", "'c'", "'S'", "'U0'", "'V7'", "'<m8[s]'", "'<M8[10us]'", "'<M8'", "'>U3'", "'<f16'", "'<f3'", "'<i16'",
          "'|f8'", "'<u3'", "'x'", "''", "'<'", "'<M8[]'", "'<M8[x]'", "'M8[0s]'", "'O8'", "'O4'", "'O3'", "'<O'", 
          "'<f8 '", "'<f8é'", "'<f8' '<f4'", "'e'", "'?'", "'S05'", "'|S0'", "'<U01'",
          "5", "None", "True", "1.5", "foo"]
FORTRANS = ["False", "True", "False", "True", "0", "1", "None", "'False'", "foo", "1.0", "-1", "(False)", "(False,)", "{[1]}", "{[1]: 2}", "{[1]: foo}", "{foo: [1]}", "{1: [2]}", "{(1,): 2}", "[{}]", "{1, 2}"]
SHAPES = ["()", "(3,)", "(3, 4)", "(0,)", "(0, 5)", "(1, 1, 1)", "(-1,)", "(-2, 3)", "(3, -1)", "(99999999999999999999,)", "(9223372036854775807,)",
          "(9223372036854775808,)", "(4294967296, 4294967296)", "(1.5,)", "3", "[3]", "(True,)", "(3L,)", "(3, 4L)", "(+3,)", "(-3, 4)", "(3 ,)",
          "(3)", "(3, 4,)", "((3,),)", "('a',)", "(None,)", "(3, (4,))", "{3}", "{3: 4}", "3, 4", "(3, 4", "3.", "(.5,)", "(3.,)",
          "(00,)", "(007,)", "(0,)", "(2147483648,)", "(10,) + (3,)", "(1+2,)", "(--3,)", "(-(3),)", "(3 4)", "(,)", "((3))"]
POOL = ["{", "}", "(", ")", "[", "]", ",", ":", "+", "-", "'a'", "3", "L", "True", "None", "foo", "1.5", "''", '"x"', "0", ".5", "'shape'"]
WORDY = set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_.'\"")
OK_NODES = (ast.Expression, ast.Constant, ast.Name, ast.UnaryOp, ast.BinOp, ast.Tuple, ast.List, ast.Dict, ast.Set,
            ast.Load, ast.UAdd, ast.USub, ast.Add, ast.Sub)


def join(rng, toks):
    out = ""
    toks = [t for t in toks if t]
    for t in toks:
        if out and out[-1] in WORDY and t[0] in WORDY:
            out += " "
        elif rng.random() < 0.3:
            out += " "
        out += t
    return out


def supported(text):
    """False when Python parses the text, or the text after `_filter_header`, into a node that the model does not cover."""
    for t in (text, None):
        if t is None:
            try:
                t = fmt._filter_header(text)
            except Exception:
                return True
        try:
            tree = ast.parse(t.lstrip(" \t"), mode="eval")
        except (SyntaxError, ValueError):
            continue
        return all(isinstance(n, OK_NODES) for n in ast.walk(tree))
    return True


def base_tokens(rng):
    keys = list(KEYS)
    r = rng.random()
    if r < 0.15:
        keys.pop(rng.randrange(3))
    elif r < 0.25:
        keys.append(rng.choice(OTHER_KEYS))
    elif r < 0.3:
        keys.append(rng.choice(KEYS))
    rng.shuffle(keys) if rng.random() < 0.4 else None
    vals = {"'descr'": rng.choice(DESCRS) if rng.random() < 0.6 else "'<f8'",
            "'fortran_order'": rng.choice(FORTRANS) if rng.random() < 0.3 else "False",
            "'shape'": rng.choice(SHAPES) if rng.random() < 0.6 else rng.choice(["(3,)", "(3, 4)", "()", "(0,)"])}
    toks = ["{"]
    for k in keys:
        toks += [k, ":", vals.get(k, rng.choice(["1", "None", "'x'", "(1,)"])), ","]
    if rng.random() < 0.15 and toks[-1] == ",":
        toks.pop()
    toks.append("}")
    if rng.random() < 0.04:
        toks = [rng.choice(["[", "(", "{", "3", "'a'", "None", "True", "-3"])] + toks[: rng.randrange(1, len(toks))] + [rng.choice(["]", ")", "}", ""])]
    elif rng.random() < 0.03:
        toks = []
    return toks


def mutate(rng, toks):
    toks = list(toks)
    for _ in range(rng.choice([0, 0, 0, 0, 1, 1, 2])):
        r = rng.random()
        i = rng.randrange(0, len(toks) + 1)
        if r < 0.35 and toks:
            toks.pop(min(i, len(toks) - 1))
        elif r < 0.7:
            toks.insert(i, rng.choice(POOL))
        elif toks:
            toks[min(i, len(toks) - 1)] = rng.choice(POOL)
    return toks


def header_text(rng):
    text = join(rng, mutate(rng, base_tokens(rng)))
    if rng.random() < 0.05 and text:
        text = text[: rng.randrange(0, len(text) + 1)]
    if rng.random() < 0.08:
        text = " " * rng.randrange(1, 4) + text
    pad = rng.choice([0, 0, 1, 5, 30])
    nl = rng.choice(["\n", "\n", "\n", "", "\n\n"])
    if rng.random() < 0.01:
        pad = rng.choice([9980, 9990, 9995, 9998, 9999, 10000, 10001, 10010]) - len(text) - len(nl)
        pad = max(pad, 0)
    return text + " " * pad + nl


def classify(e):
    msg = str(e)
    if isinstance(e, tokenize.TokenError):
        return "ERR tokenerror"
    if isinstance(e, TypeError) and "not supported between" in msg:
        return "ERR keysort"
    if isinstance(e, TypeError) and "unhashable" in msg:
        return "ERR unhashable"
    if isinstance(e, UnicodeDecodeError):
        return "ERR decode"
    if isinstance(e, ValueError):
        for key, name in [("EOF: reading array header length", "eoflen"), ("EOF: reading array header,", "eofheader"),
                          ("Header info length", "toolarge"), ("Cannot parse header", "syntax"),
                          ("malformed node", "malformed"), ("Header is not a dictionary", "notdict"),
                          ("Header does not contain", "keys"), ("shape is not valid", "shape"),
                          ("fortran_order is not", "fortran"), ("descr is not a valid", "descr"),
                          ("Invalid version", "version")]:
            if key in msg:
                return "ERR " + name
    return "ERR OTHER %s %s" % (type(e).__name__, msg[:60])


def call(v, data):
    bio = io.BytesIO(data)
    try:
        if v == 1:
            shape, fo, dt = fmt.read_array_header_1_0(bio)
        elif v == 2:
            shape, fo, dt = fmt.read_array_header_2_0(bio)
        else:
            shape, fo, dt = fmt._read_array_header(bio, (v, 0))
    except Exception as e:  # classify every kind of failure
        return classify(e)
    return "OK %s %s %s" % (",".join(str(int(x)) for x in shape) or "_", fo, dt.str)


def literal_descr_ok(text, v):
    """False when the descriptor would be a list, tuple or dict, which the model does not cover."""
    for t in (text, None):
        if t is None:
            try:
                t = fmt._filter_header(text)
            except Exception:
                return True
        try:
            d = ast.literal_eval(t)
        except Exception:
            continue
        if isinstance(d, dict) and "descr" in d and isinstance(d["descr"], (list, tuple, dict, set)):
            return False
        return True
    return True


def gen_read(rng):
    while True:
        v = rng.choice([1, 1, 2, 2, 3, 3, 3, 0, 4]) if rng.random() < 0.04 else rng.choice([1, 2, 3])
        text = header_text(rng)
        if v <= 2:
            body = text.encode("latin1", errors="replace")
        else:
            body = text.encode("utf8")
        if not supported(text):
            continue
        if v in (1, 2, 3) and not literal_descr_ok(text, v):
            continue
        if v == 3 and rng.random() < 0.03 and body:
            b = bytearray(body)
            b[rng.randrange(len(b))] = rng.choice([0xff, 0xc0, 0x80, 0xe9, 0xc3])
            body = bytes(b)
        nb = 2 if v == 1 else 4
        n = len(body)
        r = rng.random()
        if r < 0.03:
            n += rng.choice([1, 2, 100])
        elif r < 0.06 and n > 0:
            n -= rng.randrange(1, n + 1)
        elif r < 0.08:
            n = rng.choice([0, 255, 256, 65535])
        field = (n % 2 ** (8 * nb)).to_bytes(nb, "little")
        data = field + body
        if rng.random() < 0.02:
            data = data[: rng.randrange(0, len(data) + 1)]
        return "npy_read %d %s" % (v, hx(data)), call(v, data)


def gen_open(rng):
    pre = b"\x93NUMPY"
    r = rng.random()
    if r < 0.5:
        data = pre + bytes([rng.choice([1, 2, 3, 3, 0, 4, 255]), rng.choice([0, 0, 0, 1, 255])])
    elif r < 0.7:
        data = bytes(rng.choice([0x93, 0x4e, 0x55, 0x4d, 0x50, 0x59, 0, 1, 2]) for _ in range(rng.randrange(0, 10)))
    elif r < 0.85:
        data = pre[: rng.randrange(0, 7)] + bytes(rng.randrange(0, 2) for _ in range(rng.randrange(0, 4)))
    else:
        b = bytearray(pre + bytes([1, 0]))
        b[rng.randrange(6)] ^= rng.choice([1, 0x20, 0x80])
        data = bytes(b)
    data += bytes(rng.randrange(256) for _ in range(rng.choice([0, 0, 3])))
    bio = io.BytesIO(data)
    try:
        v = fmt.read_magic(bio)
        fmt._check_version(v)
        out = "OK %d" % v[0]
    except ValueError as e:
        m = str(e)
        out = "ERR eoflen" if m.startswith("EOF") else "ERR syntax" if "magic string" in m else "ERR version"
    return "npy_open " + hx(data), out


def gen(rng):
    return gen_open(rng) if rng.random() < 0.05 else gen_read(rng)


if __name__ == "__main__":
    main(gen, exe="npdiff_npyformat")
