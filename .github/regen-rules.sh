#!/usr/bin/env bash
# SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
# SPDX-License-Identifier: MIT
#
# Regenerate PhiConfluence/Rules.lean (display table) and PhiConfluence/RuleData.lean
# (structured data, guarded by the fidelity lock in .github/gen-rule-data.py) from the
# PINNED phino rules on GitHub (objectionary/phino at the tag in .phino-version). The rule
# source is phino's repo — the same source the paper's Fig. 4 is generated from — not any
# local checkout. Both files are git-ignored, so run this before `lake build`. Pinning
# keeps regeneration deterministic; the phino-latest workflow reports when the pin falls
# behind phino's newest release.
#
# Usage: bash .github/regen-rules.sh

set -euo pipefail
cd "$(dirname "$0")/.."

[ -f .phino-version ] || { echo "FATAL: .phino-version is missing, cannot tell which phino to use" >&2; exit 1; }
PHINO_REPO="${PHINO_REPO:-https://github.com/objectionary/phino}"
PHINO_VERSION="$(cat .phino-version)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

echo "cloning $PHINO_REPO at tag $PHINO_VERSION, pinned via .phino-version ..."
git clone --depth 1 --branch "$PHINO_VERSION" "$PHINO_REPO" "$tmp/phino" >/dev/null 2>&1

python3 .github/gen-rules.py "$tmp/phino/resources/normalize" PhiConfluence/Rules.lean
python3 .github/gen-rule-data.py "$tmp/phino/resources/normalize" PhiConfluence/RuleData.lean
echo "done — Rules.lean and RuleData.lean regenerated from phino $PHINO_VERSION"
