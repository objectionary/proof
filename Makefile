# SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
# SPDX-License-Identifier: MIT

SHELL := bash
.SHELLFLAGS := -e -o pipefail -c
.ONESHELL:
.PHONY: all test build axioms difftest clean

RULES := PhiConfluence/Rules.lean PhiConfluence/RuleData.lean
MATHLIB := .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean

all: test build axioms
	count=$$(cat $$(find PhiConfluence -name '*.lean') | grep -cE '^[[:space:]]*(private |protected )?(theorem|lemma)[[:space:]]')
	echo "👍🏻 CONFLUENCE IS PROVEN BY $$count THEOREMS, ALL CHECKED BY LEAN"

test:
	python3 -m pytest -p no:cacheprovider .github

$(MATHLIB): lake-manifest.json
	lake exe cache get
	touch $@

$(RULES) &: .phino-version .github/regen-rules.sh .github/gen-rules.py .github/gen-rule-data.py .github/phino_render.py
	bash .github/regen-rules.sh

build: $(MATHLIB) $(RULES)
	lake build
	lake build demo difftest

axioms: build
	if grep -REn '\bsorry\b|\badmit\b|^[[:space:]]*axiom[[:space:]]' PhiConfluence Main.lean Difftest.lean; then
	  echo "found sorry, admit or axiom in project sources" >&2
	  exit 1
	fi
	out=$$(lake env lean .github/axioms.lean 2>&1)
	echo "$$out"
	if grep -qiE 'sorryAx|Classical\.choice|native_decide|ofReduceBool|ofReduceNat' <<< "$$out"; then
	  echo "a headline theorem depends on a forbidden axiom" >&2
	  exit 1
	fi

difftest: $(RULES)
	bash .github/difftest.sh

clean:
	rm -f $(RULES)
