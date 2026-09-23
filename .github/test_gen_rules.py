# SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
# SPDX-License-Identifier: MIT
from hamcrest import assert_that, contains_string, equal_to
from phino import Rules


def test_renders_the_condition_of_every_rule(tmp_path):
    Rules().run("gen-rules.py", tmp_path)
    assert_that(
        (tmp_path / "Out.lean").read_text(encoding="utf-8"),
        contains_string('cond := "¬(𝜏 ∈ 𝐵) and ¬(φ ∈ 𝐵) and ¬(λ ∈ 𝐵)"'),
        "Did not render the condition of the stop rule",
    )


def test_renders_the_domain_of_a_binding(tmp_path):
    Rules().run("gen-rules.py", tmp_path)
    assert_that(
        (tmp_path / "Out.lean").read_text(encoding="utf-8"),
        contains_string('cond := "index(𝜏2) = domain(𝐵1)"'),
        "Did not render the domain in the condition of the alpha rule",
    )


def test_aborts_when_the_directory_holds_no_rules(tmp_path):
    assert_that(
        Rules({}).run("gen-rules.py", tmp_path).returncode,
        equal_to(1),
        "Did not fail on a directory without rules",
    )


def test_strips_the_xi_free_condition_of_copy(tmp_path):
    Rules().run("gen-rules.py", tmp_path)
    assert_that(
        (tmp_path / "Out.lean").read_text(encoding="utf-8"),
        contains_string('cond := "nf(𝑒)", wher := ""'),
        "Did not strip the xi-free condition of the copy rule",
    )
