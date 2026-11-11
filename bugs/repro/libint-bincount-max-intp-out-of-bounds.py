import subprocess
import sys

# The child writes out of bounds, so it runs in its own process. It first prints the length of the result, which should be an error, and then repeats the write until the heap breaks.
code = """
import numpy as np
print(len(np.bincount(np.array([2**63 - 1]))), flush=True)
kept = [np.bincount(np.full(10**5, 2**63 - 1), minlength=n) for n in range(1, 50)]
kept2 = [np.ones(n) for n in range(1000)]
"""
proc = subprocess.run([sys.executable, "-c", code], capture_output=True, text=True, timeout=120)
first = proc.stdout.split("\n")[0].strip()
# Either the result is silently empty or the child was killed by a signal.
print("REPRODUCED" if first == "0" or proc.returncode < 0 else "NOT REPRODUCED")
