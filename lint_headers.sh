#!/bin/bash
# Lint check: for each header, report which names from Code/ appear in theorem types.
# These are vocabulary candidates that should be in Defs/ for Stage 3 enforcement.
#
# Usage: ./lint_headers.sh

HEADER_DIR="DeanLean/Cpp"
CODE_DIR="DeanLean/Cpp/Code"

echo "=== Header vocabulary audit ==="
echo "Names from Code/ files referenced in header theorem types."
echo "These should be in Defs/ for Stage 3 enforcement."
echo ""

for header in "$HEADER_DIR"/*.lean; do
    module=$(basename "$header" .lean)
    codefile="$CODE_DIR/$module.lean"
    [ -f "$codefile" ] || continue

    # Extract public names defined in Code/
    code_names=$(grep -oP '(?:^def |^inductive |^structure |^class |^abbrev |^instance )(\S+)' "$codefile" | awk '{print $2}' | sort -u)

    # Extract names used in ProvenTheorem/TestedConjecture lines in header
    theorem_names=$(grep -A5 "ProvenTheorem\|TestedConjecture\|Signature" "$header" | grep -oP '\b[A-Z][a-zA-Z0-9_.]*\b' | sort -u)

    # Find intersection
    matches=""
    for name in $code_names; do
        short=$(echo "$name" | sed 's/.*\.//')
        if echo "$theorem_names" | grep -qw "$short"; then
            matches="$matches $short"
        fi
    done

    if [ -n "$matches" ]; then
        echo "  $module.lean → Code names in theorem types:$matches"
    else
        echo "  $module.lean → clean (no Code names in theorems)"
    fi
done
