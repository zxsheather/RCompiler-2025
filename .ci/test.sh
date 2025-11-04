#!/usr/bin/env bash
set -euo pipefail

echo "=== Running unit tests ==="
# Run unit tests
cargo test --workspace --all-features -- --show-output

echo ""
echo "=== Running semantic tests ==="
# Run semantic tests with timeout
if command -v timeout &> /dev/null; then
    timeout 300 cargo run --release -- --semantic-test
else
    # macOS doesn't have timeout by default, use gtimeout if available
    if command -v gtimeout &> /dev/null; then
        gtimeout 300 cargo run --release -- --semantic-test
    else
        cargo run --release -- --semantic-test
    fi
fi

echo ""
echo "=== Running IR tests ==="
# Run IR tests with timeout (10 minutes)
if command -v timeout &> /dev/null; then
    timeout 600 cargo run --release -- --ir-test
else
    # macOS doesn't have timeout by default, use gtimeout if available
    if command -v gtimeout &> /dev/null; then
        gtimeout 600 cargo run --release -- --ir-test
    else
        cargo run --release -- --ir-test
    fi
fi

echo ""
echo "=== All tests completed successfully ==="
