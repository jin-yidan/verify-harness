#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
EXPECTED_REV="${EXPECTED_REV:-4aaea15591360ccfffa1befdf0e7162f5af17f60}"
SLT_DIR="${SLT_DIR:-$REPO_ROOT/.lake/packages/SLT}"
PATCH_FILE="${PATCH_FILE:-$REPO_ROOT/patches/slt-v4.28.patch}"

if [[ "$PATCH_FILE" != /* ]]; then
  PATCH_FILE="$REPO_ROOT/$PATCH_FILE"
fi

if [[ ! -d "$SLT_DIR/.git" ]]; then
  echo "missing SLT checkout at $SLT_DIR" >&2
  echo "run 'lake update SLT' first" >&2
  exit 1
fi

actual_rev="$(git -C "$SLT_DIR" rev-parse HEAD)"
if [[ "$actual_rev" != "$EXPECTED_REV" ]]; then
  echo "unexpected SLT revision: $actual_rev" >&2
  echo "expected pinned revision: $EXPECTED_REV" >&2
  exit 1
fi

if git -C "$SLT_DIR" apply --reverse --check "$PATCH_FILE" >/dev/null 2>&1; then
  echo "SLT compatibility patch already applied"
  exit 0
fi

if git -C "$SLT_DIR" apply --check "$PATCH_FILE" >/dev/null 2>&1; then
  git -C "$SLT_DIR" apply "$PATCH_FILE"
  echo "Applied SLT compatibility patch"
  exit 0
fi

echo "SLT compatibility patch does not apply cleanly" >&2
exit 1
