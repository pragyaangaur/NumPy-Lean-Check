#!/bin/sh
# Commit exactly one path with one message. It retries when another process holds the git index lock.
# Usage: scripts/commit_file.sh <path> "<message>"
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
for i in 1 2 3 4 5 6 7 8 9 10; do
  if git add -- "$1" 2>/dev/null && git commit -q -m "$2" -- "$1" 2>/dev/null; then
    exit 0
  fi
  if git diff --quiet HEAD -- "$1" 2>/dev/null && git ls-files --error-unmatch "$1" >/dev/null 2>&1; then
    exit 0
  fi
  sleep 2
done
echo "commit failed for $1" >&2
exit 1
