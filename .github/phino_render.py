# SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
# SPDX-License-Identifier: MIT
"""
The one rendering of phino's rule YAML into display strings, shared by gen-rules.py
(the display table) and gen-rule-data.py (the fidelity lock), so the lock asserts
against exactly the strings the display table shows. Only the display table passes
`strip_xi=True`, which drops phino's `xi-free` side-conditions the way `phino explain`
does for the paper's figure; the lock keeps them, since `Step.copy` carries `xiFree`.
"""
import glob
import os

import yaml


def rterm(x):
    return str(x)


def rcmp(x):
    if isinstance(x, dict):
        k = next(iter(x))
        v = x[k]
        if k == "index":
            return f"index({rterm(v)})"
        if k == "length":
            return f"|{rterm(v)}|"
        return f"{k}({rterm(v)})"
    return rterm(x)


def rcond(w, strip_xi=False):
    if w is None:
        return ""
    if not isinstance(w, dict):
        return rterm(w)
    k = next(iter(w))
    v = w[k]
    if k == "and":
        return " and ".join(p for p in (rcond(x, strip_xi) for x in v) if p)
    if k == "or":
        return " or ".join(p for p in (rcond(x, strip_xi) for x in v) if p)
    if k == "not":
        return "¬(" + rcond(v, strip_xi) + ")"
    if k == "in":
        return f"{rterm(v[0])} ∈ {rterm(v[1])}"
    if k == "nf":
        return f"nf({rterm(v)})"
    if k == "xi-free" and strip_xi:
        return ""
    if k == "alpha":
        return f"α-attr({rterm(v)})"
    if k == "eq":
        return f"{rcmp(v[0])} = {rcmp(v[1])}"
    return f"{k}({rterm(v)})"


def rwhere(ws):
    parts = []
    for w in ws or []:
        meta = w.get("meta")
        fn = w.get("function")
        args = w.get("args", [])
        parts.append(f"{meta} := {fn}({', '.join(rterm(a) for a in args)})")
    return " and ".join(parts)


def rules(res_dir, strip_xi=False):
    """Every rule in `res_dir` rendered to name/pattern/result/cond/wher, failing on none."""
    paths = sorted(glob.glob(os.path.join(res_dir, "*.yaml")))
    if not paths:
        raise SystemExit(f"no phino rules (*.yaml) found in {res_dir}")
    out = []
    for path in paths:
        with open(path, encoding="utf-8") as f:
            d = yaml.safe_load(f)
        absent = [k for k in ("name", "pattern", "result") if not isinstance(d, dict) or k not in d]
        if absent:
            raise SystemExit(f"phino rule file {path} lacks the keys {absent}")
        out.append({
            "name": str(d["name"]),
            "pattern": str(d["pattern"]),
            "result": str(d["result"]),
            "cond": rcond(d.get("when"), strip_xi),
            "wher": rwhere(d.get("where")),
        })
    return out
