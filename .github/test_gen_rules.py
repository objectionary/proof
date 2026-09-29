# SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
# SPDX-License-Identifier: MIT
from hamcrest import assert_that, contains_string, equal_to
from phino import Rules


def test_renders_the_condition_of_every_rule(tmp_path):
    Rules().run("gen-rules.py", tmp_path)
    assert_that(
        (tmp_path / "Out.lean").read_text(encoding="utf-8"),
        contains_string('cond := "¬(𝜏1 ∈ 𝐵1) and ¬(𝜏1 = ρ)"'),
        "Did not render the condition of the miss rule",
    )


def test_renders_the_domain_of_a_binding(tmp_path):
    Rules().run("gen-rules.py", tmp_path)
    assert_that(
        (tmp_path / "Out.lean").read_text(encoding="utf-8"),
        contains_string('cond := "𝑖1 = domain(𝐵1) and ¬(𝜏1 = ρ)"'),
        "Did not render the domain in the condition of the alpha rule",
    )


def test_renders_an_ordering_of_numbers(tmp_path):
    Rules().run("gen-rules.py", tmp_path)
    assert_that(
        (tmp_path / "Out.lean").read_text(encoding="utf-8"),
        contains_string('cond := "¬(domain(𝐵1) > 𝑖1)"'),
        "Did not render the ordering in the condition of the amiss rule",
    )


def test_renders_a_membership_in_joined_bindings(tmp_path):
    Rules().run("gen-rules.py", tmp_path)
    assert_that(
        (tmp_path / "Out.lean").read_text(encoding="utf-8"),
        contains_string('cond := "Δ ∈ [𝐵1, 𝐵2]"'),
        "Did not render the joined bindings in the condition of the dl rule",
    )


def test_renders_a_negated_subset_of_joined_bindings(tmp_path):
    Rules().run("gen-rules.py", tmp_path)
    assert_that(
        (tmp_path / "Out.lean").read_text(encoding="utf-8"),
        contains_string('cond := "¬([Δ, λ] ⊆ [𝐵1, 𝐵2])"'),
        "Did not render the subset guard in the condition of the dot rule",
    )


def test_renders_disjoint_bindings(tmp_path):
    Rules().run("gen-rules.py", tmp_path)
    assert_that(
        (tmp_path / "Out.lean").read_text(encoding="utf-8"),
        contains_string('cond := "[𝜏1, φ, λ] ∩ [𝐵1] = ∅"'),
        "Did not render the disjoint guard in the condition of the stop rule",
    )


def test_renders_two_functions_of_one_rule(tmp_path):
    Rules().run("gen-rules.py", tmp_path)
    assert_that(
        (tmp_path / "Out.lean").read_text(encoding="utf-8"),
        contains_string('wher := "𝑒1 := contextualize(𝑛1, ⟦𝐵1, 𝐵2⟧) and 𝑒2 := named(⟦𝐵1, 𝜏1 ↦ 𝑛1, 𝐵2⟧)"'),
        "Did not render both functions of the dot rule",
    )


def test_aborts_when_the_directory_holds_no_rules(tmp_path):
    assert_that(
        Rules({}).run("gen-rules.py", tmp_path).returncode,
        equal_to(1),
        "Did not fail on a directory without rules",
    )
