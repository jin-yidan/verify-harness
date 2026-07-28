#!/usr/bin/env bash
set -euo pipefail

ROOT_FILE="RLGeneralization.lean"
ROOT_OLEAN=".lake/build/lib/lean/RLGeneralization.olean"

if [[ ! -f "$ROOT_FILE" ]]; then
  echo "missing $ROOT_FILE" >&2
  exit 1
fi

MODULES=()
while IFS= read -r module; do
  [[ -n "$module" ]] || continue
  MODULES+=("$module")
done < <(sed -n 's/^import //p' "$ROOT_FILE")

if [[ ${#MODULES[@]} -eq 0 ]]; then
  echo "no imports found in $ROOT_FILE" >&2
  exit 1
fi

if [[ -d .lake/packages/SLT/.git ]]; then
  bash scripts/prepare_slt.sh
fi

FILES=()
for module in "${MODULES[@]}"; do
  path="$(printf '%s' "$module" | tr '.' '/').lean"
  if [[ ! -f "$path" ]]; then
    echo "imported module file missing: $path" >&2
    exit 1
  fi
  FILES+=("$path")
done

# Verify the root olean was produced by a prior build step.
if [[ ! -f "$ROOT_OLEAN" ]]; then
  echo "RLGeneralization.olean not found — run 'lake build RLGeneralization' first" >&2
  exit 1
fi

# Catch literal True placeholders (block-comment-aware, handles both → and ->).
TRUE_HITS=()
for f in "${FILES[@]}"; do
  while IFS= read -r hit; do
    [[ -n "$hit" ]] && TRUE_HITS+=("$hit")
  done < <(python3 -c "
import re, sys
text = open('$f').read()
# Strip block comments /- ... -/
depth = 0
stripped = []
for ln, line in enumerate(text.splitlines(), 1):
    out = []; i = 0
    while i < len(line):
        if depth == 0:
            if line[i:i+2] == '/-': depth += 1; i += 2
            else: out.append(line[i]); i += 1
        else:
            if line[i:i+2] == '/-': depth += 1; i += 2
            elif line[i:i+2] == '-/': depth -= 1; i += 2
            else: i += 1
    if depth == 0:
        stripped.append((ln, ''.join(out)))
for ln, line in stripped:
    s = line.strip()
    if s.startswith('--'): continue
    cp = line.find('--')
    code = line[:cp] if cp >= 0 else line
    # : True :=  or  True :=  at line start  or  →/-> True  or  True)
    if re.search(r':\s*True\s*:=', code) or re.search(r'^\s*True\s*:=', code) \
       or re.search(r'(→|->)\s*True\b', code) or re.search(r'^\s*True\s*\)', code):
        print(f'$f:{ln}:{s[:120]}')
" 2>/dev/null || true)
done
if [[ ${#TRUE_HITS[@]} -gt 0 ]]; then
  echo "verified target contains literal True placeholder(s):" >&2
  for hit in "${TRUE_HITS[@]}"; do
    echo "  $hit" >&2
  done
  exit 1
fi

if grep -Fn "This file is NOT imported into the verified target." "${FILES[@]}"; then
  echo "verified target imports a file that self-identifies as excluded" >&2
  exit 1
fi

if grep -En "oracle strategy|vacuous placeholder|The theorem takes the bound as a hypothesis and returns it" "${FILES[@]}"; then
  echo "verified target contains draft/stub markers" >&2
  exit 1
fi

# Scan for 'sorry' in EXACT-status modules only.
# Conditional modules may have sorry for deferred proofs (annotated [CONDITIONAL: ...]).
# We use verification_manifest.json to identify exact-module file paths.
EXACT_FILES=()
if [[ -f "verification_manifest.json" ]]; then
  while IFS= read -r module; do
    [[ -n "$module" ]] || continue
    path="$(printf '%s' "$module" | tr '.' '/').lean"
    if [[ -f "$path" ]]; then
      EXACT_FILES+=("$path")
    fi
  done < <(python3 -c "
import json, sys
try:
    m = json.load(open('verification_manifest.json'))
    for e in m['verified_target']['modules']:
        if e.get('status') == 'exact':
            print(e['module'])
except Exception as ex:
    print('warn: could not parse manifest: ' + str(ex), file=sys.stderr)
")
fi

if [[ ${#EXACT_FILES[@]} -gt 0 ]]; then
  SORRY_LINES=()
  for f in "${EXACT_FILES[@]}"; do
    while IFS= read -r line; do
      SORRY_LINES+=("$line")
    done < <(python3 -c "
import re, sys
text = open('$f').read()
# Strip block comments /- ... -/
depth = 0
stripped_lines = []
for line_num, line in enumerate(text.splitlines(), 1):
    out = []
    i = 0
    while i < len(line):
        if depth == 0:
            if line[i:i+2] == '/-':
                depth += 1; i += 2
            else:
                out.append(line[i]); i += 1
        else:
            if line[i:i+2] == '/-':
                depth += 1; i += 2
            elif line[i:i+2] == '-/':
                depth -= 1; i += 2
            else:
                i += 1
    if depth == 0:
        stripped_lines.append((line_num, ''.join(out)))
for line_num, line in stripped_lines:
    s = line.strip()
    if s.startswith('--'):
        continue
    comment_pos = line.find('--')
    m = re.search(r'\bsorry\b', line)
    if m and (comment_pos < 0 or m.start() < comment_pos):
        print(f'$f:{line_num}:{s}')
" 2>/dev/null || true)
  done
  if [[ ${#SORRY_LINES[@]} -gt 0 ]]; then
    echo "FAIL: sorry found in exact-status trusted-root modules:" >&2
    for line in "${SORRY_LINES[@]}"; do
      echo "  $line" >&2
    done
    exit 1
  fi
fi

# -------------------------------------------------------------------
# Check ALL trusted-root modules (exact + conditional) for unannotated sorry.
# Conditional modules may have sorry only within 10 lines of a [CONDITIONAL: ...] annotation.
# Block comments are excluded.
# -------------------------------------------------------------------
UNANNOTATED_SORRY=()
if [[ -f "verification_manifest.json" ]]; then
  while IFS= read -r result_line; do
    [[ -n "$result_line" ]] || continue
    UNANNOTATED_SORRY+=("$result_line")
  done < <(python3 -c "
import json, re, sys

manifest = json.load(open('verification_manifest.json'))
modules = manifest.get('verified_target', {}).get('modules', [])

def strip_block_comments(text):
    depth = 0
    result = []
    for line_num, line in enumerate(text.splitlines(), 1):
        out = []
        i = 0
        while i < len(line):
            if depth == 0:
                if line[i:i+2] == '/-':
                    depth += 1; i += 2
                else:
                    out.append(line[i]); i += 1
            else:
                if line[i:i+2] == '/-':
                    depth += 1; i += 2
                elif line[i:i+2] == '-/':
                    depth -= 1; i += 2
                else:
                    i += 1
        if depth == 0:
            result.append((line_num, ''.join(out)))
    return result

for entry in modules:
    mod = entry['module']
    status = entry.get('status', 'unknown')
    path = mod.replace('.', '/') + '.lean'
    try:
        text = open(path).read()
    except FileNotFoundError:
        continue

    stripped = strip_block_comments(text)
    # Build a dict of line_num -> stripped_line for annotation proximity check
    line_dict = {ln: l for ln, l in stripped}

    for line_num, line in stripped:
        s = line.strip()
        if s.startswith('--'):
            continue
        comment_pos = line.find('--')
        m = re.search(r'\bsorry\b', line)
        if not m:
            continue
        if comment_pos >= 0 and m.start() >= comment_pos:
            continue  # sorry is inside a line comment

        if status == 'exact':
            # Exact modules were already checked above; skip
            continue

        # For conditional modules: allow sorry if [CONDITIONAL: ...] is within 10 lines
        has_annotation = False
        for offset in range(-10, 11):
            nearby = line_dict.get(line_num + offset, '')
            if re.search(r'\[CONDITIONAL\b', nearby):
                has_annotation = True
                break
        if not has_annotation:
            print(f'{path}:{line_num}: {s[:120]}')
" 2>/dev/null || true)
fi

if [[ ${#UNANNOTATED_SORRY[@]} -gt 0 ]]; then
  echo "FAIL: unannotated sorry in trusted-root modules (no [CONDITIONAL: ...] within 10 lines):" >&2
  for line in "${UNANNOTATED_SORRY[@]}"; do
    echo "  $line" >&2
  done
  exit 1
fi

# -------------------------------------------------------------------
# Check that no draft modules are imported by the trusted root.
# This blocks both `import RLGeneralization.Draft` and direct imports
# of individual draft-target modules listed in the manifest.
# -------------------------------------------------------------------
DRAFT_IMPORTS=()

# Build a regex alternation of all draft module names from the manifest.
DRAFT_PATTERN='RLGeneralization\.Draft\b'
if [[ -f "verification_manifest.json" ]]; then
  while IFS= read -r draft_mod; do
    [[ -n "$draft_mod" ]] || continue
    escaped="$(printf '%s' "$draft_mod" | sed 's/\./\\./g')"
    DRAFT_PATTERN="${DRAFT_PATTERN}|${escaped}\\b"
  done < <(python3 -c "
import json, sys
try:
    m = json.load(open('verification_manifest.json'))
    for e in m.get('draft_target', {}).get('modules', []):
        print(e['module'])
except Exception as ex:
    print('warn: ' + str(ex), file=sys.stderr)
")
fi

for f in "${FILES[@]}"; do
  while IFS= read -r line; do
    DRAFT_IMPORTS+=("$line")
  done < <(grep -nE "^\s*import\s+($DRAFT_PATTERN)" "$f" 2>/dev/null || true)
done
# Also check the root file itself
while IFS= read -r line; do
  DRAFT_IMPORTS+=("$line")
done < <(grep -nE "^\s*import\s+($DRAFT_PATTERN)" "$ROOT_FILE" 2>/dev/null || true)

if [[ ${#DRAFT_IMPORTS[@]} -gt 0 ]]; then
  echo "FAIL: trusted-root modules import draft modules:" >&2
  for line in "${DRAFT_IMPORTS[@]}"; do
    echo "  $line" >&2
  done
  exit 1
fi

echo "verified target checks passed"
