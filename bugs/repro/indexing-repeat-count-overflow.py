import subprocess
import sys

code = "import numpy as np\nnp.repeat(np.arange(4), 2**62)\n"
proc = subprocess.run([sys.executable, "-c", code], capture_output=True, text=True, timeout=60)
# A negative return code means the child was killed by a signal, here SIGSEGV or SIGBUS.
print("REPRODUCED" if proc.returncode < 0 else "NOT REPRODUCED")
