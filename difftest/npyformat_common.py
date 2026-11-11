"""Helpers shared by the NpyFormat differential tests."""
import io
import struct
import warnings

import numpy as np
from numpy.lib import _format_impl as fmt

warnings.simplefilter("ignore")


def hx(b):
    """Hex text for a bytes object, `_` for the empty one."""
    return b.hex() if b else "_"


def hx_text(s):
    return hx(s.encode("utf8"))


def ver_name(v):
    return "auto" if v is None else str(v[0])


# Characters used in descriptor strings: printable ASCII plus one latin1, one BMP and one CJK character.
DESCR_CHARS = [chr(c) for c in range(32, 127)] + ["é", "ā", "日"]
