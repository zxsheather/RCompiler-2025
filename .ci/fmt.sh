#!/usr/bin/env bash
set -euo pipefail

if ! command -v cargo >/dev/null; then
  echo "cargo not found" >&2
  exit 1
fi

cargo fmt --all -- --check
