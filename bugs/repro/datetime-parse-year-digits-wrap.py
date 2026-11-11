import numpy as np

nat = np.isnat(np.datetime64("9223372036854775808"))
zero = np.datetime64("18446744073709551616") == np.datetime64("0000")
print("REPRODUCED" if nat and zero else "NOT REPRODUCED")
