import subprocess
import sys

code = "import numpy as np\nnp.busday_count(np.datetime64(-2**63 + 1, 'D'), np.datetime64(2**63 - 1, 'D'))\n"
try:
    subprocess.run([sys.executable, "-c", code], capture_output=True, timeout=10)
    hung = False
except subprocess.TimeoutExpired:
    hung = True
print("REPRODUCED" if hung else "NOT REPRODUCED")
