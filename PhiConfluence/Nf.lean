-- SPDX-FileCopyrightText: Copyright (c) 2026 Objectionary.com
-- SPDX-License-Identifier: MIT

import PhiConfluence.Attributes

/-!
# Structural normal form `nf`

`nf e` is the structural, decidable characterization of "`e` is irreducible" — the paper's
normal form `𝓝`, and the guard `dot`/`copy` read (`nf 𝑒₁`). It mirrors phino's `isNF`
(`src/Rule.hs` = "no normalization rule matches anywhere in `e`"), spelled out structurally so
it computes and so the proofs can case on it. `nf_iff` (`Parallel.lean`) proves it equals
irreducibility on well-formed terms.

`dispatchNF`/`appNF` decide whether a dispatch/application has a redex **at the root** (they only
inspect the subject and the attribute); `nf`/`nfB` add the recursive "no redex in any subterm",
and `nf` of a formation also rejects the `dl` redex, a formation holding both `λ` and `Δ`.
-/

namespace PhiConfluence

/-- A dispatch `e.a` has no root redex (`dd`/`null`/`dot`/`stop` do not fire at the top).
A missing `a` on a formation with `φ` is normal: phino has no rule for it. -/
def dispatchNF : Term → Attr → Bool
  | .bot, _ => false
  | .form bs, a =>
      match lookup bs a with
      | .attached _ => false
      | .void => false
      | .absent =>
          match lookup bs .phi with
          | .absent => hasLambda bs
          | _ => true
  | _, _ => true

/-- Spine-`ξ`-freeness: the term has no scope locator `ξ` along its application/dispatch spine
(formations are opaque — a `ξ` inside a nested formation does not count). Matches phino's
`xiFree` in `_absolute`, including `⊥`, and is half of `copy`'s `𝑘` guard. -/
def xiFree : Term → Bool
  | .xi => false
  | .glob => true
  | .bot => true
  | .form _ => true
  | .dispatch e _ => xiFree e
  | .app e _ arg => xiFree e && xiFree arg

/-- An application `e.a(arg)` has no root redex (`dc`/`stay`/`over`/`copy`/`miss` and the
positional `alpha`/`overa`/`amiss` do not fire at the top). A positional `αᵢ` applied to a
formation always has a redex, since the three positional rules split every ordinal. A void
slot keyed by a non-positional attribute is a `copy`-redex exactly when the argument is
`ξ`-free (its normality is checked by `nf` itself). -/
def appNF : Term → Attr → Term → Bool
  | .bot, _, _ => false
  | .form _, .alpha _, _ => false
  | .form bs, a, arg =>
      match lookup bs a with
      | .attached _ => false
      | .void => !xiFree arg
      | .absent => false
  | _, _, _ => true

mutual

/-- Structural normal form: no reduction rule fires anywhere in the term. -/
def nf : Term → Bool
  | .bot => true | .glob => true | .xi => true
  | .form bs => nfB bs && !(hasLambda bs && hasDelta bs)
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
