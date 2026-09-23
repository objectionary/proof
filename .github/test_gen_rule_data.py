# SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
# SPDX-License-Identifier: MIT
import random
import string

from hamcrest import assert_that, contains_string, equal_to, is_not
from phino import Rules


def noise():
    return "".join(random.choices(string.ascii_letters + "𝜏𝑒⟦⟧↦", k=random.randint(3, 12)))


def test_writes_every_locked_rule_when_phino_matches_the_lock(tmp_path):
    Rules().run("gen-rule-data.py", tmp_path)
    assert_that(
        (tmp_path / "Out.lean").read_text(encoding="utf-8"),
        contains_string('{ name := "stop", shape := .dispatchForm, conds := [.slotAbsent, .phiAbsent, .noLambda], rhs := .bot }'),
        "Did not emit the locked tags of the stop rule",
    )


def test_aborts_when_a_rule_result_drifts(tmp_path):
    assert_that(
        Rules().changed("stay", "result", noise()).run("gen-rule-data.py", tmp_path).stderr,
        contains_string("FIDELITY-LOCK BREACH for rule 'stay'"),
        "Did not report a breach when the result of stay drifted",
    )


def test_aborts_when_a_rule_condition_drifts(tmp_path):
    assert_that(
        Rules().changed("dot", "when", {"nf": noise()}).run("gen-rule-data.py", tmp_path).stderr,
        contains_string("FIDELITY-LOCK BREACH for rule 'dot'"),
        "Did not report a breach when the condition of dot drifted",
    )


def test_aborts_when_phino_adds_a_rule(tmp_path):
    name = noise()
    assert_that(
        Rules().plus("extra", {"name": name, "pattern": "⊥", "result": "⊥"}).run("gen-rule-data.py", tmp_path).stderr,
        contains_string(f"UNLOCKED rule '{name}'"),
        "Did not report a rule that phino added",
    )


def test_aborts_when_phino_removes_a_rule(tmp_path):
    assert_that(
        Rules().without("miss").run("gen-rule-data.py", tmp_path).stderr,
        contains_string("['miss']"),
        "Did not report a rule that phino removed",
    )


def test_aborts_when_two_files_define_one_rule(tmp_path):
    assert_that(
        Rules().plus("twin", Rules().docs["dd"]).run("gen-rule-data.py", tmp_path).stderr,
        contains_string("duplicate rule name 'dd'"),
        "Did not report a rule defined twice",
    )


def test_names_the_file_when_a_rule_lacks_its_result(tmp_path):
    assert_that(
        Rules().stripped("copy", "result").run("gen-rule-data.py", tmp_path).stderr,
        contains_string("copy.yaml"),
        "Did not name the rule file that lacks a result",
    )


def test_prints_no_traceback_when_a_rule_lacks_its_pattern(tmp_path):
    assert_that(
        Rules().stripped("null", "pattern").run("gen-rule-data.py", tmp_path).stderr,
        is_not(contains_string("Traceback")),
        "Crashed with a traceback on a rule without a pattern",
    )


def test_exits_with_failure_when_the_lock_breaks(tmp_path):
    assert_that(
        Rules().changed("dc", "pattern", noise()).run("gen-rule-data.py", tmp_path).returncode,
        equal_to(1),
        "Did not exit with failure on a broken lock",
    )
