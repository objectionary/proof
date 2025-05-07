-- SPDX-FileCopyrightText: Copyright (c) 2024-2025 Yegor Bugayenko
-- SPDX-License-Identifier: MIT

import Extended.Record

set_option autoImplicit false
set_option linter.all true
set_option linter.missingDocs false

/-! ### Defition of φ-calculus terms -/

@[reducible]
def Attr := String
@[reducible]
def Attrs := List String


universe u

inductive Term : Type where
  | dot : Term → Attr → Term          -- t.α
  | app : {attrs : Attrs} → Term → Record Term attrs → Term    -- t(α ↦ u,  ...)
  | obj : {attrs : Attrs} → Option Term → Record (Option Term) attrs → Term  -- ⟦ α → ... ⟧
  | glob : Term                       -- Φ
  | this : Term                       -- ξ
  | termination : Term                -- ⊥
open Term

@[reducible]
def Bindings lst := Record (Option Term) lst

-- S(t, b) as in `1.20 Substitution`
mutual
def substitute : Term → Term → Term
  | this, b => b
  | glob, _ => glob
  | termination, _ => termination
  | obj none record, b => obj (some b) record
  | obj (some t) record, _ => obj (some t) record
  | app t record, b => app (substitute t b) (substituteRecord record b)
  | dot t a, b => dot (substitute t b) a

def substituteRecord
  {keys : List Attr}
  (record : Record Term keys)
  (b : Term)
  : Record Term keys
  := match record with
    | Record.nil => Record.nil
    | Record.cons key not_in t tail =>
        Record.cons key not_in (substitute t b) (substituteRecord tail b)

end


inductive LookupRes where
  | absent   : LookupRes
  | void     : LookupRes
  | attached : Term → LookupRes

def lookup
  {attrs : Attrs}
  (ρ : Option Term)
  (bnds : Bindings attrs)
  (attr : Attr)
  : LookupRes
  := if attr == "ρ"
    then match ρ with
      | none => LookupRes.void
      | some t => LookupRes.attached t
    else match Record.lookup bnds attr with
      | none => LookupRes.absent
      | some none => LookupRes.void
      | some (some t) => LookupRes.attached t

theorem LookupRes.absent_means_notin
  {attrs : Attrs}
  {bnds : Bindings attrs}
  {attr : Attr}
  {ρ : Option Term}
  (neq : attr ≠ "ρ")
  (attr_absent : lookup ρ bnds attr = .absent)
  : attr ∉ attrs
  := by
    simp [lookup, neq] at attr_absent
    admit

-- def LookupRes.lookup_absent_preserve
--   {attrs : Attrs}
--   {bnds1 bnds2 : Bindings attrs}
--   {attr : Attr}
--   {ρ1 ρ2 : Option Term}
--   (attr_absent : lookup ρ1 bnds1 attr = .absent)
--   : lookup ρ2 bnds2 attr = .absent
--   := dite (attr = "ρ")
--     (λ eq => by
--       simp [lookup, eq] at attr_absent
--       split at attr_absent
--       . contradiction
--       . contradiction
--     )
--     (λ neq => by
--       simp [lookup, neq]
--     )

def insert
  {attrs : Attrs}
  (ρ : Option Term)
  (bnds : Bindings attrs)
  (attr : Attr)
  (t : Term)
  : Term
  := if attr == "ρ"
    then obj (some t) bnds
    else obj ρ (Record.insert bnds attr (some t))
