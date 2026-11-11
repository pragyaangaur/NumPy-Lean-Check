"""Create the stub files for a new area and wire it into the lake project.

Usage: python3 scripts/new_area.py IntArith
"""
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN = os.path.join(ROOT, "lean")


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    if not os.path.exists(path):
        open(path, "w").write(text)


def main():
    area = sys.argv[1]
    low = area.lower()
    d = os.path.join(LEAN, "NumpyLean", area)
    write(os.path.join(d, "Model.lean"), f"import NumpyLean.Common.Intp\n\nnamespace NumpyLean.{area}\n\nend NumpyLean.{area}\n")
    write(os.path.join(d, "Props.lean"), f"import NumpyLean.{area}.Model\n\nnamespace NumpyLean.{area}\n\nend NumpyLean.{area}\n")
    write(os.path.join(d, "Diff.lean"), f"import NumpyLean.{area}.Model\nimport NumpyLean.Common.Wire\n\nnamespace NumpyLean.{area}\nopen NumpyLean.Wire\n\ndef handlers : List (String × Handler) := []\n\nend NumpyLean.{area}\n")
    write(os.path.join(LEAN, "exe", f"{area}.lean"), f"import NumpyLean.{area}.Diff\nimport NumpyLean.Common.Driver\n\ndef main : IO Unit := NumpyLean.runHandlers NumpyLean.{area}.handlers\n")
    lake = os.path.join(LEAN, "lakefile.toml")
    text = open(lake).read()
    if f'"npdiff_{low}"' not in text:
        open(lake, "a").write(f'\n[[lean_exe]]\nname = "npdiff_{low}"\nroot = "exe.{area}"\n')
    root = os.path.join(LEAN, "NumpyLean.lean")
    text = open(root).read()
    for part in ("Model", "Props", "Diff"):
        line = f"import NumpyLean.{area}.{part}\n"
        if line not in text:
            text += line
    open(root, "w").write(text)
    main_path = os.path.join(LEAN, "Main.lean")
    text = open(main_path).read()
    entry = f"NumpyLean.{area}.handlers"
    if entry not in text:
        text = text.replace("\n\ndef main : IO Unit", f" ++\n  {entry}\n\ndef main : IO Unit")
    open(main_path, "w").write(text)


if __name__ == "__main__":
    main()
