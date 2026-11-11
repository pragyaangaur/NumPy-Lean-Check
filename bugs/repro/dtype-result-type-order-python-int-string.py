import numpy as np


def result(*args):
    try:
        return str(np.result_type(*args))
    except TypeError:
        return "error"


first = result(np.int8, "S3", 1)
second = result("S3", np.int8, 1)
print("REPRODUCED" if first == "|S4" and second == "error" else "NOT REPRODUCED")
