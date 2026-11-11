#!/bin/sh
# Fetch the pinned NumPy source into vendor/numpy and build the Python environment.
# Every model in lean/ cites file paths and line numbers from this exact tag.
set -eu
TAG=v2.5.4
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
mkdir -p "$ROOT/vendor"
if [ ! -d "$ROOT/vendor/numpy" ]; then
  git clone --depth 1 --branch "$TAG" https://github.com/numpy/numpy.git "$ROOT/vendor/numpy"
fi
if [ ! -d "$ROOT/.venv" ]; then
  python3 -m venv "$ROOT/.venv"
fi
"$ROOT/.venv/bin/pip" install --quiet -r "$ROOT/requirements.txt"
"$ROOT/.venv/bin/python" -c "import numpy; print('numpy', numpy.__version__)"
git -C "$ROOT/vendor/numpy" rev-parse HEAD
