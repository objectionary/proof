#!/usr/bin/env bash
# SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
# SPDX-License-Identifier: MIT
#
# Regenerate PhiConfluence/Rules.lean from the LATEST phino rules on GitHub
# (objectionary/phino master). The rule source is phino's repo — the same source the
# paper's Fig. 4 is generated from — not any local checkout.
#
# Usage: bash scripts/regen-rules.sh

set -euo pipefail
cd "$(dirname "$0")/.."

PHINO_REPO="${PHINO_REPO:-https://github.com/objectionary/phino}"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

echo "cloning $PHINO_REPO (master = latest) ..."
git clone --depth 1 "$PHINO_REPO" "$tmp/phino" >/dev/null 2>&1

python3 scripts/gen-rules.py "$tmp/phino/resources" PhiConfluence/Rules.lean
echo "done — PhiConfluence/Rules.lean regenerated from phino master"
