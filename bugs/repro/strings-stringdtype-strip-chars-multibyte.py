import numpy as np

a = np.array(["aaa"], dtype=np.dtypes.StringDType())
r = np.strings.strip(a, "éa")[0]
print("REPRODUCED" if r == "aaa" and "aaa".strip("éa") == "" else "NOT REPRODUCED")
