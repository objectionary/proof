-- SPDX-FileCopyrightText: Copyright (c) 2024-2025 Yegor Bugayenko
-- SPDX-License-Identifier: MIT

import Minimal.ARS
import Minimal.Term

open Term

set_option autoImplicit false

/-! ### Defition of regular reduction `⇝` -/

/-- Evaluation [KS22, Fig. 1] -/
inductive Reduce : Term → Term → Type where
  | congOBJ
    : { t : Term }
    → { t' : Term }
    → (b : Attr)
    → { lst : List Attr }
    → (l : Bindings lst)
    → Reduce t t'
    → IsAttached b t l
    → Reduce (obj l) (obj (insert_φ l b (some t')))
  | congDOT : ∀ t t' a, Reduce t t' → Reduce (dot t a) (dot t' a)
  | congAPPₗ : ∀ t t' u a, Reduce t t' → Reduce (app t a u) (app t' a u)
  | congAPPᵣ : ∀ t u u' a, Reduce u u' → Reduce (app t a u) (app t a u')
  | dot_c
    : { t : Term }
    → (t_c : Term)
    → (c : Attr)
    → { lst : List Attr }
    → (l : Bindings lst)
    → t = obj l
    → lookup l c = some (some t_c)
    → Reduce (dot t c) (substitute (0, t) t_c)
  | dot_cφ
    : { t : Term }
    → (c : Attr)
    → { lst : List Attr }
    → (l : Bindings lst)
    → t = obj l
    → lookup l c = none
    → "φ" ∈ lst
    → Reduce (dot t c) (dot (dot t "φ") c)
  | app_c
    : (t u : Term)
    → (c : Attr)
    → { lst : List Attr }
    → (l : Bindings lst)
    → t = obj l
    → lookup l c = some none
    → Reduce (app t c u) (obj (insert_φ l c (some (incLocators u))))


def RedMany := ReflTransGen Reduce

infix:20 " ⇝ " => Reduce
infix:20 " ⇝* " => RedMany
