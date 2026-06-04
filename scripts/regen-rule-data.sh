#!/usr/bin/env bash
# SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
# SPDX-License-Identifier: MIT
#
# Regenerate PhiConfluence/RuleData.lean from the PINNED phino rules on GitHub
# (objectionary/phino at the tag in .phino-version). The fidelity lock in
# scripts/gen-rule-data.py aborts if phino's rules drift from the locked interpretation.
# The CI build runs this before `lake build`, so the proof compiles against phino's rules.
#
# Usage: bash scripts/regen-rule-data.sh

set -euo pipefail
cd "$(dirname "$0")/.."

PHINO_REPO="${PHINO_REPO:-https://github.com/objectionary/phino}"
PHINO_VERSION="$(cat .phino-version)"
# phino's package/binary version is 4-part (0.0.0.74), but its git tags drop the
# leading component (0.0.74).
PHINO_TAG="${PHINO_VERSION#0.}"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

echo "cloning $PHINO_REPO at tag $PHINO_TAG (phino $PHINO_VERSION, pinned via .phino-version) ..."
git clone --depth 1 --branch "$PHINO_TAG" "$PHINO_REPO" "$tmp/phino" >/dev/null 2>&1

python3 scripts/gen-rule-data.py "$tmp/phino/resources" PhiConfluence/RuleData.lean
echo "done — PhiConfluence/RuleData.lean regenerated from phino $PHINO_VERSION"
