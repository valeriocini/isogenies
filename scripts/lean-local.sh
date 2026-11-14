#!/bin/sh
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
if [ -z "${LEAN_BIN:-}" ]; then
  if [ -x "$ROOT/.runtime436/toolchain/bin/lean" ]; then
    LEAN_BIN="$ROOT/.runtime436/toolchain/bin/lean"
  else
    LEAN_BIN=lean
  fi
fi
TASK_LEAN_PATH="$ROOT/.lake/build/lib/lean"
for package in "$ROOT"/.lake/packages/*; do
  TASK_LEAN_PATH="$TASK_LEAN_PATH:$package/.lake/build/lib/lean"
done
export LEAN_PATH="$TASK_LEAN_PATH"
cd "$ROOT"
exec "$LEAN_BIN" "$@"
