#!/usr/bin/env bash
# SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
# SPDX-License-Identifier: MIT
#
# Regenerate PhiConfluence/Rules.lean from the PINNED phino rules on GitHub
# (objectionary/phino at the tag in .phino-version). The rule source is phino's repo —
# the same source the paper's Fig. 4 is generated from — not any local checkout. Pinning
# keeps regeneration deterministic: tracking master let phino drift break this in CI.
#
# Usage: bash scripts/regen-rules.sh

set -euo pipefail
cd "$(dirname "$0")/.."

PHINO_REPO="${PHINO_REPO:-https://github.com/objectionary/phino}"
PHINO_VERSION="$(cat .phino-version)"
# phino's package/binary version is 4-part (0.0.0.74 — what --pin and the release
# artifacts use), but its git tags drop the leading component (0.0.74).
PHINO_TAG="${PHINO_VERSION#0.}"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

echo "cloning $PHINO_REPO at tag $PHINO_TAG (phino $PHINO_VERSION, pinned via .phino-version) ..."
git clone --depth 1 --branch "$PHINO_TAG" "$PHINO_REPO" "$tmp/phino" >/dev/null 2>&1

python3 scripts/gen-rules.py "$tmp/phino/resources" PhiConfluence/Rules.lean
echo "done — PhiConfluence/Rules.lean regenerated from phino $PHINO_VERSION"
