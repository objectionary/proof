-- SPDX-FileCopyrightText: Copyright (c) 2024-2025 Yegor Bugayenko
-- SPDX-License-Identifier: MIT

set_option autoImplicit false

universe u v
variable {α : Type u}

-- Unique-keyed record { k₁: v₁, k₂: v₂, ... }
inductive Record (α : Type u) : List String → Type u where
  | nil : Record α []
  | cons
    : {keys : List String}
    → (key : String)
    → key ∉ keys
    → α
    → Record α keys
    → Record α (key :: keys)

-- value ∈ record
inductive Mem : {keys : List String} → Record α keys → (a : α) → Prop where
  | head
    : {keys : List String}
    → {a : α}
    → {as : Record α keys}
    → (key : String)
    → (not_in : key ∉ keys)
    → Mem (Record.cons key not_in a as) a
  | tail
    : {keys : List String}
    → {a b : α}
    → {as : Record α keys}
    → (key : String)
    → (not_in : key ∉ keys)
    → Mem as a
    → Mem (Record.cons key not_in b as) a

instance {keys : List String} : Membership α (Record α keys) where
  mem := Mem

inductive Contains : {keys : List String} → Record α keys → (key : String) → (a : α) → Type u
  | head
    : {keys : List String}
    → {a : α}
    → {as : Record α keys}
    → (key : String)
    → (not_in : key ∉ keys)
    → Contains (Record.cons key not_in a as) key a
  | tail
    : {keys : List String}
    → {a b : α}
    → {as : Record α keys}
    → (key' key : String)
    → (not_in : key' ∉ keys)
    → Contains as key a
    → Contains (Record.cons key' not_in b as) key a

theorem contains_to_mem
  {key : String}
  {a : α}
  {keys : List String}
  {record : Record α keys}
  : Contains record key a → a ∈ record
  | Contains.head _key _ => Mem.head _ _
  | Contains.tail _ _ _ tail => Mem.tail _ _ (contains_to_mem tail)

-- def mem_to_contains
--   {a : α}
--   {keys : List String}
--   {record : Record α keys}
--   : a ∈ record → Σ key: String, Contains record key a
--   := λ a_is_in => match record with
--     | Record.nil => by contradiction
--     | Record.cons key not_in b tail => sorry--by
--       -- match a_is_in with
--         -- | Mem.head _ _ => exact ⟨_, Contains.head _ _⟩
--         -- | Mem.tail _ _ _ => exact ⟨_, Contains.tail _ _ _ _⟩
