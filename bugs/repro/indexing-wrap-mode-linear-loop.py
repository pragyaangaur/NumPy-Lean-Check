import subprocess
import sys

code = "import numpy as np\nprint(np.take(np.arange(3), [2**62], mode='wrap'))\n"
try:
    subprocess.run([sys.executable, "-c", code], capture_output=True, timeout=10)
    slow = False
except subprocess.TimeoutExpired:
    slow = True
print("REPRODUCED" if slow else "NOT REPRODUCED")
