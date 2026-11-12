import numpy as np

r = np.strings.rstrip(np.array(["a \x00\n"]))[0]
t = np.strings.rstrip(np.array(["a \x00\n"], dtype=np.dtypes.StringDType()))[0]
print("REPRODUCED" if r == "a" and t == "a \x00" else "NOT REPRODUCED")
