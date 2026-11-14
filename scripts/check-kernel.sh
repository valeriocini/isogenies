#!/bin/sh
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$ROOT"
if [ -x "$ROOT/.runtime436/toolchain/bin/leanchecker" ]; then
  PATH="$ROOT/.runtime436/toolchain/bin:$PATH"
  LEAN_BIN="$ROOT/.runtime436/toolchain/bin/leanchecker"
else
  LEAN_BIN=leanchecker
fi
export PATH LEAN_BIN
exec sh scripts/lean-local.sh --fresh IsogenyAttack
