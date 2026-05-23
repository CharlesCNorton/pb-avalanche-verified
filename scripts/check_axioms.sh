#!/usr/bin/env bash
# Audit-check guard for pb-avalanche-verified.
#
# Compiles theories/pb_avalanche_audit.v and extracts every axiom name
# appearing in any Print Assumptions block of its output. The set of
# observed axioms is then diffed against the expected manifest at
# scripts/expected_axioms.txt. A non-empty diff fails the script and
# the build target that calls it.
#
# Expected workflow:
#   make           # build everything
#   make audit-check  # run this script; succeeds iff axiom set is as expected
#
# Author: Charles C. Norton
# License: MIT

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_DIR="$(dirname "$SCRIPT_DIR")"
EXPECTED="$SCRIPT_DIR/expected_axioms.txt"

cd "$REPO_DIR"

# Compile the audit file and capture its stdout. The audit file's
# Print Assumptions calls emit either "Closed under the global
# context" (no axioms used) or "Axioms:" followed by a list.
RAW_OUTPUT="$(timeout 600 rocq compile -R theories PBAvalanche \
    theories/pb_avalanche_audit.v 2>&1)"

# Extract the names of axioms that appear. Each Coq axiom output has
# the form "AxiomName : <type>"; we filter for lines that look like
# axiom declarations under an "Axioms:" header.
OBSERVED="$(echo "$RAW_OUTPUT" \
    | grep -E '^[A-Za-z_][A-Za-z0-9_.]*\s+:' \
    | awk '{ print $1 }' \
    | sort -u)"

if [ ! -f "$EXPECTED" ]; then
    echo "ERROR: expected manifest not found at $EXPECTED"
    echo "Observed axiom set was:"
    echo "$OBSERVED"
    exit 1
fi

EXPECTED_SET="$(sort -u "$EXPECTED")"

if [ "$OBSERVED" = "$EXPECTED_SET" ]; then
    echo "OK: audit axiom set matches expected manifest."
    echo "    axioms:"
    echo "$OBSERVED" | sed 's/^/      /'
    exit 0
fi

echo "FAIL: axiom-set regression detected."
echo
echo "Diff (expected vs observed):"
diff <(echo "$EXPECTED_SET") <(echo "$OBSERVED") || true
exit 1
