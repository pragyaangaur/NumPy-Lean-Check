import io

import numpy as np

# The descriptor |V0 has itemsize zero, so nothing is read and nothing is allocated whatever the shape says.
bio = io.BytesIO()
np.lib.format.write_array_header_1_0(bio, {"descr": "|V0", "fortran_order": False, "shape": (-4294967296, 4294967296)})
bio.seek(0)
try:
    a = np.lib.format.read_array(bio)
    print("REPRODUCED" if a.shape == (0, 4294967296) else "NOT REPRODUCED")
except ValueError:
    print("NOT REPRODUCED")
