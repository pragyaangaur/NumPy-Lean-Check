import itertools

import numpy as np

arrays = {"e": np.zeros(1, "e"), "S": np.array([b"abc"]), "O": np.array([None], object)}
results = {}
for order in itertools.permutations("eSO"):
    try:
        results[order] = str(np.concatenate([arrays[k] for k in order]).dtype)
    except TypeError:
        results[order] = "error"
try:
    rt = str(np.result_type(np.float16, "S3", object))
except TypeError:
    rt = "error"
others = [v for k, v in results.items() if k != ("e", "S", "O")]
bad = results[("e", "S", "O")] == "error" and rt == "error" and all(v == "object" for v in others)
print("REPRODUCED" if bad else "NOT REPRODUCED")
