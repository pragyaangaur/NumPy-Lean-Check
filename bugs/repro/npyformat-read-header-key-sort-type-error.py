import io
import struct

import numpy as np

text = b"{'a': 1, 1: 2}"
data = struct.pack("<H", len(text)) + text
try:
    np.lib.format.read_array_header_1_0(io.BytesIO(data))
    print("NOT REPRODUCED")
except ValueError:
    print("NOT REPRODUCED")
except TypeError:
    print("REPRODUCED")
