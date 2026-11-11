import numpy as np

wrong = int(np.digitize(np.array([2**53]), np.array([2**53 + 1, 2**53]))[0]) != 1
try:
    np.digitize(np.array([2**53]), np.array([2**53, 2**53 + 1, 2**53]))
    accepted = True
except ValueError:
    accepted = False
print("REPRODUCED" if wrong or accepted else "NOT REPRODUCED")
