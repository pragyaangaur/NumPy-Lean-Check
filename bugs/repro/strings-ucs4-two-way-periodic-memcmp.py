import numpy as np

hay = "a" * 2500
needle = "bb" + "a" * 98
u = int(np.strings.find(np.array([hay]), np.array([needle]))[0])
c = int(np.strings.count(np.array([hay]), np.array([needle]))[0])
print("REPRODUCED" if hay.find(needle) == -1 and (u != -1 or c != 0) else "NOT REPRODUCED")
