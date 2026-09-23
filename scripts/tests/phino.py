# SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
# SPDX-License-Identifier: MIT
"""
A directory of phino normalization rules, as phino 0.0.74 ships them in resources/*.yaml,
which a test can change rule by rule before writing it to disk for a generator to read.
"""
import os
import subprocess
import sys

import yaml

ORIGINAL = {
    "alpha": {
        "name": "alpha",
        "pattern": "⟦𝐵1, 𝜏1 ↦ ∅, 𝐵2⟧(𝜏2 ↦ 𝑒)",
        "result": "⟦𝐵1, 𝜏1 ↦ ∅, 𝐵2⟧(𝜏1 ↦ 𝑒)",
        "when": {"eq": [{"index": "𝜏2"}, {"domain": "𝐵1"}]},
    },
    "copy": {
        "name": "copy",
        "pattern": "⟦ 𝐵1, 𝜏 ↦ ∅, 𝐵2 ⟧(𝜏 ↦ 𝑒)",
        "result": "⟦ 𝐵1, 𝜏 ↦ 𝑒, 𝐵2 ⟧",
        "when": {"and": [{"xi-free": "𝑒"}, {"nf": "𝑒"}]},
    },
    "dc": {"name": "dc", "pattern": "⊥(𝜏 ↦ 𝑒)", "result": "⊥"},
    "dd": {"name": "dd", "pattern": "⊥.𝜏", "result": "⊥"},
    "dot": {
        "name": "dot",
        "pattern": "⟦𝐵1, 𝜏 ↦ 𝑒1, 𝐵2⟧.𝜏",
        "result": "𝑒2(ρ ↦ ⟦𝐵1, 𝜏 ↦ 𝑒1, 𝐵2⟧)",
        "when": {"nf": "𝑒1"},
        "where": [
            {"meta": "𝑒2", "function": "contextualize", "args": ["𝑒1", "⟦𝐵1, 𝜏 ↦ 𝑒1, 𝐵2⟧"]},
        ],
    },
    "miss": {
        "name": "miss",
        "pattern": "⟦𝐵⟧(𝜏 ↦ 𝑒)",
        "result": "⊥",
        "when": {"and": [{"not": {"in": ["𝜏", "𝐵"]}}, {"not": {"alpha": "𝜏"}}]},
    },
    "null": {"name": "null", "pattern": "⟦𝐵1, 𝜏 ↦ ∅, 𝐵2⟧.𝜏", "result": "⊥"},
    "over": {
        "name": "over",
        "pattern": "⟦𝐵1, 𝜏 ↦ 𝑒1, 𝐵2⟧(𝜏 ↦ 𝑒2)",
        "result": "⊥",
        "when": {"not": {"eq": ["𝜏", "ρ"]}},
    },
    "phi": {
        "name": "phi",
        "pattern": "⟦𝐵⟧.𝜏",
        "result": "⟦𝐵⟧.φ.𝜏",
        "when": {"and": [{"in": ["φ", "𝐵"]}, {"not": {"in": ["𝜏", "𝐵"]}}]},
    },
    "stay": {"name": "stay", "pattern": "⟦𝐵1, ρ ↦ 𝑒1, 𝐵2⟧(ρ ↦ 𝑒2)", "result": "⟦𝐵1, ρ ↦ 𝑒1, 𝐵2⟧"},
    "stop": {
        "name": "stop",
        "pattern": "⟦𝐵⟧.𝜏",
        "result": "⊥",
        "when": {
            "and": [
                {"not": {"in": ["𝜏", "𝐵"]}},
                {"not": {"in": ["φ", "𝐵"]}},
                {"not": {"in": ["λ", "𝐵"]}},
            ],
        },
    },
}


class Rules:
    """
    Phino's rule files as an immutable map from file stem to YAML document, which
    derives changed copies of itself and runs a generator script against its files.
    """

    def __init__(self, docs=None):
        self.docs = dict(ORIGINAL if docs is None else docs)

    def changed(self, stem, key, value):
        return Rules({**self.docs, stem: {**self.docs[stem], key: value}})

    def stripped(self, stem, key):
        return Rules({**self.docs, stem: {k: v for k, v in self.docs[stem].items() if k != key}})

    def without(self, stem):
        return Rules({k: v for k, v in self.docs.items() if k != stem})

    def plus(self, stem, doc):
        return Rules({**self.docs, stem: doc})

    def run(self, script, tmp):
        res = tmp / "resources"
        res.mkdir()
        for stem, doc in self.docs.items():
            (res / f"{stem}.yaml").write_text(yaml.safe_dump(doc, allow_unicode=True), encoding="utf-8")
        return subprocess.run(
            [sys.executable, os.path.join(os.path.dirname(os.path.dirname(__file__)), script), str(res), str(tmp / "Out.lean")],
            capture_output=True,
            text=True,
            timeout=60,
            check=False,
        )
