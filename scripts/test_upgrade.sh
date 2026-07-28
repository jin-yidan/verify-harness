#!/usr/bin/env bash
# Test building against the current Lean/Mathlib version.
# Usage: bash scripts/test_upgrade.sh
#
# This script verifies the full build pipeline works:
# 1. Prepare SLT dependency
# 2. Build trusted root with --wfail
# 3. Build draft root
# 4. Run manifest consistency checks
#
# For version upgrades, update lean-toolchain and lakefile.toml first,
# then run this script to verify compatibility.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"

echo "=== Lean/Mathlib Version Upgrade Test ==="
echo "Lean toolchain: $(cat lean-toolchain)"
echo ""

echo "Step 1: Prepare SLT dependency..."
bash scripts/prepare_slt.sh
echo ""

echo "Step 2: Build trusted root (--wfail)..."
lake build --wfail RLGeneralization
echo ""

echo "Step 3: Build draft root..."
lake build RLGeneralization.Draft
echo ""

echo "Step 4: Manifest consistency..."
bash scripts/check_manifest_consistency.sh
echo ""

echo "Step 5: Verified target checks..."
bash scripts/check_verified_target.sh
echo ""

echo "Step 6: Status consistency..."
python3 scripts/generate_status.py --check
echo ""

echo "Step 7: Dashboard..."
python3 scripts/dashboard.py --badge
echo ""

echo "=== All upgrade tests passed ==="
