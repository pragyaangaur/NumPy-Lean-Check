"""Run every reproducer in bugs/repro and report which bug records still reproduce."""
import glob
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PY = os.path.join(ROOT, ".venv", "bin", "python")


def main():
    records = sorted(glob.glob(os.path.join(ROOT, "bugs", "*.yaml")))
    ok, bad = 0, []
    for rec in records:
        name = os.path.basename(rec)[: -len(".yaml")]
        script = os.path.join(ROOT, "bugs", "repro", name + ".py")
        if not os.path.exists(script):
            bad.append((name, "no reproducer"))
            continue
        try:
            out = subprocess.run([PY, script], capture_output=True, text=True, timeout=120).stdout
        except subprocess.TimeoutExpired:
            bad.append((name, "timeout"))
            continue
        lines = out.strip().splitlines()
        if lines and lines[-1].strip() == "REPRODUCED":
            ok += 1
        else:
            bad.append((name, lines[-1] if lines else "no output"))
    for name, why in bad:
        print(f"FAIL {name}: {why}")
    print(f"{ok}/{len(records)} bug records reproduce")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
