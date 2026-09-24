# SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
# SPDX-License-Identifier: MIT
"""
A directory of phino normalization rules, as phino 0.0.139 ships them in resources/normalize/*.yaml,
which a test can change rule by rule before writing it to disk for a generator to read.
"""

import os
import subprocess
import sys

import yaml

ASSETLESS = {"or": [{"disjoint": [["λ"], ["𝐵1", "𝐵2"]]}, {"disjoint": [["Δ"], ["𝐵1", "𝐵2"]]}]}

ORIGINAL = {
    "alpha": {
        "name": "alpha",
        "pattern": "⟦𝐵1, 𝜏1 ↦ ∅, 𝐵2⟧(α𝑖1 ↦ 𝑒1)",
        "result": "⟦𝐵1, 𝜏1 ↦ ∅, 𝐵2⟧(𝜏1 ↦ 𝑒1)",
        "when": {"and": [{"eq": ["𝑖1", {"domain": "𝐵1"}]}, {"not": {"eq": ["𝜏1", "ρ"]}}]},
    },
    "amiss": {
        "name": "amiss",
        "pattern": "⟦𝐵1⟧(α𝑖1 ↦ 𝑒)",
        "result": "⊥",
        "when": {"not": {"gt": [{"domain": "𝐵1"}, "𝑖1"]}},
    },
    "copy": {"name": "copy", "pattern": "⟦ 𝐵1, 𝜏1 ↦ ∅, 𝐵2 ⟧(𝜏1 ↦ 𝑘1)", "result": "⟦ 𝐵1, 𝜏1 ↦ 𝑘1, 𝐵2 ⟧"},
    "dc": {"name": "dc", "pattern": "⊥(𝜏 ↦ 𝑒)", "result": "⊥"},
    "dca": {"name": "dca", "pattern": "⊥(α𝑖 ↦ 𝑒)", "result": "⊥"},
    "dd": {"name": "dd", "pattern": "⊥.𝜏", "result": "⊥"},
    "dl": {
        "name": "dl",
        "pattern": "⟦𝐵1, λ ⤍ 𝑓, 𝐵2⟧",
        "result": "⊥",
        "when": {"or": [{"in": ["Δ", "𝐵1"]}, {"in": ["Δ", "𝐵2"]}]},
    },
    "dot": {
        "name": "dot",
        "pattern": "⟦𝐵1, 𝜏1 ↦ 𝑛1, 𝐵2⟧.𝜏1",
        "e-match": "𝑒1",
        "when": {"and": [{"not": {"eq": ["⟦𝐵1, 𝜏1 ↦ 𝑛1, 𝐵2⟧", "𝑒1"]}}, ASSETLESS]},
        "result": "𝑒2(ρ ↦ ⟦𝐵1, 𝜏1 ↦ 𝑛1, 𝐵2⟧)",
        "where": [{"meta": "𝑒2", "function": "contextualize", "args": ["𝑛1", "⟦𝐵1, 𝐵2⟧"]}],
    },
    "dotg": {
        "name": "dotg",
        "pattern": "⟦𝐵1, 𝜏1 ↦ 𝑛1, 𝐵2⟧.𝜏1",
        "e-match": "𝑒1",
        "when": {"and": [{"eq": ["⟦𝐵1, 𝜏1 ↦ 𝑛1, 𝐵2⟧", "𝑒1"]}, ASSETLESS]},
        "result": "𝑒2(ρ ↦ Φ)",
        "where": [{"meta": "𝑒2", "function": "contextualize", "args": ["𝑛1", "⟦𝐵1, 𝐵2⟧"]}],
    },
    "miss": {
        "name": "miss",
        "pattern": "⟦𝐵1⟧(𝜏1 ↦ 𝑒)",
        "result": "⊥",
        "when": {"and": [{"not": {"in": ["𝜏1", "𝐵1"]}}, {"not": {"eq": ["𝜏1", "ρ"]}}]},
    },
    "null": {"name": "null", "pattern": "⟦𝐵1, 𝜏1 ↦ ∅, 𝐵2⟧.𝜏1", "result": "⊥"},
    "over": {
        "name": "over",
        "pattern": "⟦𝐵1, 𝜏1 ↦ 𝑒1, 𝐵2⟧(𝜏1 ↦ 𝑒2)",
        "result": "⊥",
        "when": {"not": {"eq": ["𝜏1", "ρ"]}},
    },
    "overa": {
        "name": "overa",
        "pattern": "⟦𝐵1, 𝜏1 ↦ 𝑒1, 𝐵2⟧(α𝑖1 ↦ 𝑒2)",
        "result": "⊥",
        "when": {"and": [{"eq": ["𝑖1", {"domain": "𝐵1"}]}, {"not": {"eq": ["𝜏1", "ρ"]}}]},
    },
    "skip": {"name": "skip", "pattern": "⟦𝐵1⟧(ρ ↦ 𝑒1)", "result": "⟦𝐵1⟧", "when": {"not": {"in": ["ρ", "𝐵1"]}}},
    "stay": {"name": "stay", "pattern": "⟦𝐵1, ρ ↦ 𝑒1, 𝐵2⟧(ρ ↦ 𝑒2)", "result": "⟦𝐵1, ρ ↦ 𝑒1, 𝐵2⟧"},
    "stop": {
        "name": "stop",
        "pattern": "⟦𝐵1⟧.𝜏1",
        "result": "⊥",
        "when": {
            "and": [
                {"not": {"in": ["𝜏1", "𝐵1"]}},
                {"not": {"in": ["φ", "𝐵1"]}},
                {"not": {"in": ["λ", "𝐵1"]}},
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
            [sys.executable, os.path.join(os.path.dirname(__file__), script), str(res), str(tmp / "Out.lean")],
            capture_output=True,
            text=True,
            timeout=60,
            check=False,
        )
