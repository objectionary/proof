#!/usr/bin/env bash
# SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
# SPDX-License-Identifier: MIT
#
# Regenerate PhiConfluence/Rules.lean (display table) and PhiConfluence/RuleData.lean
# (structured data, guarded by the fidelity lock in .github/gen-rule-data.py) from the
# PINNED phino rules on GitHub (objectionary/phino at the tag in .phino-version). The rule
# source is phino's repo — the same source the paper's Fig. 4 is generated from — not any
# local checkout. Both files are git-ignored, so run this before `lake build`. The tag is
# checked against the commit in .phino-commit, since a git tag can be moved. Pinning keeps
# regeneration deterministic; the phino-latest workflow reports when the pin falls behind
# phino's newest release.
#
# Usage: bash .github/regen-rules.sh

set -euo pipefail
cd "$(dirname "$0")/.."

[ -f .phino-version ] || { echo "FATAL: .phino-version is missing, cannot tell which phino to use" >&2; exit 1; }
[ -f .phino-commit ] || { echo "FATAL: .phino-commit is missing, cannot verify the phino tag" >&2; exit 1; }
PHINO_REPO="${PHINO_REPO:-https://github.com/objectionary/phino}"
PHINO_VERSION="$(cat .phino-version)"
# phino's package/binary version is 4-part (0.0.0.74 — what --pin and the release
# artifacts use), but its git tags drop the leading component (0.0.74).
PHINO_TAG="${PHINO_VERSION#*.}"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

echo "cloning $PHINO_REPO at tag $PHINO_TAG (phino $PHINO_VERSION, pinned via .phino-version) ..."
git clone --depth 1 --branch "$PHINO_TAG" "$PHINO_REPO" "$tmp/phino" >/dev/null 2>&1
commit="$(git -C "$tmp/phino" rev-parse HEAD)"
[ "$commit" = "$(cat .phino-commit)" ] || { echo "FATAL: phino tag $PHINO_TAG points to $commit, not to the commit in .phino-commit" >&2; exit 1; }

python3 .github/gen-rules.py "$tmp/phino/resources" PhiConfluence/Rules.lean
python3 .github/gen-rule-data.py "$tmp/phino/resources" PhiConfluence/RuleData.lean
echo "done — Rules.lean and RuleData.lean regenerated from phino $PHINO_VERSION"
