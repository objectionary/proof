-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

import PhiConfluence.Attributes

/-!
# Structural normal form `nf`

`nf e` is the structural, decidable characterization of "`e` is irreducible" — the paper's
normal form `𝓝`, and the guard `dot`/`copy` read (`nf 𝑒₁`). It mirrors phino's `isNF`
(`src/Rule.hs` = "no normalization rule matches anywhere in `e`"), spelled out structurally so
it computes and so the proofs can case on it.

It is defined for the **full eleven-rule** calculus from the start — a dispatch on an *attached*
slot is a `dot`-redex and an application on a *void* slot a `copy`-redex, so both are **not** `nf`
even though `dot`/`copy` are not in `Step`/`Par` yet (they land in M4.3c/M4.4). Defining the final
predicate once keeps the guard paper-faithful and avoids redefining `nf` as rules arrive. The
correspondence `nf ↔ ¬Reducible` (`nf_iff`) is therefore deferred to M4.4, when `Step` is complete;
the load-bearing facts proved now (`nf_par_eq`, `nf_devel` in `Parallel.lean`) hold regardless,
because the eleven-rule `nf` is *stricter* than the current reducibility.

`dispatchNF`/`appNF` decide whether a dispatch/application has a redex **at the root** (they only
inspect the subject and the attribute); `nf`/`nfB` add the recursive "no redex in any subterm".
-/

namespace PhiConfluence

/-- A dispatch `e.a` has no root redex (`dd`/`null`/`dot`/`phi`/`stop` do not fire at the top). -/
def dispatchNF : Term → Attr → Bool
  | .bot, _ => false
  | .form bs, a =>
      match lookup bs a with
      | .attached _ => false
      | .void => false
      | .absent =>
          match lookup bs .phi with
          | .absent => hasLambda bs
          | _ => false
  | _, _ => true

/-- Spine-`ξ`-freeness: the term has no scope locator `ξ` along its application/dispatch spine
(formations are opaque — a `ξ` inside a nested formation does not count). Matches phino's `_xi`,
and is `copy`'s guard: `copy` fires only on a `ξ`-free argument. -/
def xiFree : Term → Bool
  | .xi => false
  | .glob => true
  | .bot => false
  | .form _ => true
  | .dispatch e _ => xiFree e
  | .app e _ arg => xiFree e && xiFree arg

/-- An application `e.a(arg)` has no root redex (`dc`/`stay`/`over`/`copy`/`alpha`/`miss` do not
fire at the top). The `void` case is `copy`-aware: a void slot keyed by a non-positional attribute
applied to a `ξ`-free argument is a `copy`-redex (hence NOT normal), so it is normal exactly when
the argument is *not* `ξ`-free; a void slot keyed by a positional `αᵢ` is the `alpha` rule's
critical pair (never `copy`), so it stays a redex. (`αᵢ` is never a key in a *well-formed* term, so
on `WF` terms this is exactly "`copy`-redex iff `ξ`-free arg" — the guard distinction only matters
for the unconditional `nf_par_eq` on malformed terms.) -/
def appNF : Term → Attr → Term → Bool
  | .bot, _, _ => false
  | .form bs, a, arg =>
      match lookup bs a with
      | .attached _ => false
      | .void => match a with | .alpha _ => false | _ => !xiFree arg
      | .absent =>
          match a with
          | .alpha i => match voidAtOrdinal bs i with | some _ => false | _ => true
          | _ => false
  | _, _, _ => true

mutual

/-- Structural normal form: no reduction rule fires anywhere in the term. -/
def nf : Term → Bool
  | .bot => true | .glob => true | .xi => true
  | .form bs => nfB bs
  | .dispatch e a => nf e && dispatchNF e a
  | .app e a arg => nf e && nf arg && appNF e a arg

/-- Structural normal form of a binding list (every attached value is `nf`). -/
def nfB : List Binding → Bool
  | [] => true
  | .attached _ v :: r => nf v && nfB r
  | .void _ :: r => nfB r
  | .delta _ :: r => nfB r
  | .lambda _ :: r => nfB r

end

end PhiConfluence
