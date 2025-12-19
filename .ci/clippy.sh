#!/usr/bin/env bash
set -euo pipefail

# Clippy policy:
# - Default: allow general warnings (do NOT fail CI), but deny critical groups.
# - Strict mode: set CLIPPY_STRICT=1 or pass --strict to fail on ANY warning.

STRICT=${CLIPPY_STRICT:-1}
if [[ "${1:-}" == "--strict" ]]; then
  STRICT=1
fi

if [[ "$STRICT" == "1" ]]; then
  echo "[clippy] Running in STRICT mode (-D warnings)"
  cargo clippy --workspace --all-targets -- -D warnings || {
    echo "Clippy reported issues (strict mode)" >&2
    exit 1
  }
else
  echo "[clippy] Running in RELAXED mode (deny only critical groups)"
  # Deny only correctness & suspicious issues; keep others as warnings (non-fatal)
  cargo clippy --workspace --all-targets -- \
    -D clippy::correctness \
    -D clippy::suspicious || {
      echo "Clippy reported critical issues" >&2
      exit 1
    }
fi
