#!/usr/bin/env bash
set -euo pipefail

# Run unit tests
cargo test --workspace --all-features -- --show-output
