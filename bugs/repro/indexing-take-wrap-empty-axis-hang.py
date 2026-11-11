import subprocess
import sys

code = "import numpy as np\nnp.take(np.zeros((0, 0)), [0], axis=0, mode='wrap')\n"
try:
    subprocess.run([sys.executable, "-c", code], capture_output=True, timeout=10)
    hung = False
except subprocess.TimeoutExpired:
    hung = True
print("REPRODUCED" if hung else "NOT REPRODUCED")
