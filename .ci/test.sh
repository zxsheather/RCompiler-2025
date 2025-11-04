#!/usr/bin/env bash
set -euo pipefail

echo "Running unit tests..."
# Run unit tests
cargo test --workspace --all-features -- --show-output

echo ""
echo "Running semantic tests..."
# Run semantic tests
cargo run --release -- --semantic-test

echo ""
echo "Running IR tests..."
# Run IR tests
cargo run --release -- --ir-test
