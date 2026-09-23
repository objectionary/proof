#!/usr/bin/env bash
# SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
# SPDX-License-Identifier: MIT
#
# Regenerate PhiConfluence/Rules.lean (display table) and PhiConfluence/RuleData.lean
# (structured data, guarded by the fidelity lock in scripts/gen-rule-data.py) from the
# PINNED phino rules on GitHub (objectionary/phino at the tag in .phino-version). The rule
# source is phino's repo — the same source the paper's Fig. 4 is generated from — not any
# local checkout. Pinning keeps regeneration deterministic; the phino-latest workflow
# reports when the pin falls behind phino's newest release.
#
# Usage: bash scripts/regen-rules.sh

set -euo pipefail
cd "$(dirname "$0")/.."

[ -f .phino-version ] || { echo "FATAL: .phino-version is missing, cannot tell which phino to use" >&2; exit 1; }
PHINO_REPO="${PHINO_REPO:-https://github.com/objectionary/phino}"
PHINO_VERSION="$(cat .phino-version)"
# phino's package/binary version is 4-part (0.0.0.74 — what --pin and the release
# artifacts use), but its git tags drop the leading component (0.0.74).
PHINO_TAG="${PHINO_VERSION#*.}"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

echo "cloning $PHINO_REPO at tag $PHINO_TAG (phino $PHINO_VERSION, pinned via .phino-version) ..."
git clone --depth 1 --branch "$PHINO_TAG" "$PHINO_REPO" "$tmp/phino" >/dev/null 2>&1

python3 scripts/gen-rules.py "$tmp/phino/resources" PhiConfluence/Rules.lean
python3 scripts/gen-rule-data.py "$tmp/phino/resources" PhiConfluence/RuleData.lean
echo "done — Rules.lean and RuleData.lean regenerated from phino $PHINO_VERSION"
