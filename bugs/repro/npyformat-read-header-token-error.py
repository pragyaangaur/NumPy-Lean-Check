import io
import struct

import numpy as np

text = b"{'descr': '<f8', 'fortran_order': False, 'shape': (3,), "
data = struct.pack("<H", len(text)) + text
try:
    np.lib.format.read_array_header_1_0(io.BytesIO(data))
    print("NOT REPRODUCED")
except ValueError:
    print("NOT REPRODUCED")
except Exception as e:
    print("REPRODUCED" if type(e).__name__ == "TokenError" else "NOT REPRODUCED")
