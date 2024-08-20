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
inductive Mem : {keys : List String} → (a : α) → Record α keys → Prop where
  | head
    : {keys : List String}
    → {a : α}
    → {as : Record α keys}
    → (key : String)
    → (not_in : key ∉ keys)
    → Mem a (Record.cons key not_in a as)
  | tail
    : {keys : List String}
    → {a b : α}
    → {as : Record α keys}
    → (key : String)
    → (not_in : key ∉ keys)
    → Mem a as
    → Mem a (Record.cons key not_in b as)

instance {keys : List String} : Membership α (Record α keys) where
  mem := Mem

-- (key, value) ∈ record
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
    → (cur_key key : String)
    → key ≠ cur_key
    → (not_in : cur_key ∉ keys)
    → Contains as key a
    → Contains (Record.cons cur_key not_in b as) key a

theorem contains_to_mem
  {key : String}
  {a : α}
  {keys : List String}
  {record : Record α keys}
  : Contains record key a → a ∈ record
  | Contains.head _key _ => Mem.head _ _
  | Contains.tail _ _ _ _ tail => Mem.tail _ _ (contains_to_mem tail)

namespace Record

def lookup
  {keys : List String}
  (record : Record α keys)
  (key : String)
  : Option α
  := match keys with
    | [] => none
    | k :: _ => match record with
      | Record.cons _ _ a tail => if key == k then some a else lookup tail key

def insert
  {keys : List String}
  (record : Record α keys)
  (key : String)
  (a : α)
  : Record α keys
  := match keys with
    | [] => Record.nil
    | k :: _ => match record with
      | Record.cons _ not_in a' tail => if key == k
        then Record.cons k not_in a tail
        else Record.cons k not_in a' (insert tail key a)

theorem consequtive_insert
  {keys : List String}
  {record : Record α keys}
  {key : String}
  {a b : α}
  : insert (insert record key a) key b
    = insert record key b
  := match record with
    | nil => by rfl
    | cons cur_key not_in elem _ => by
      simp [insert]
      exact dite
        (key = cur_key)
        (λ eq => by simp [insert, eq])
        (λ neq => by
          simp [insert, neq]
          exact consequtive_insert
        )

def contains_after_insert
  {keys : List String}
  {record : Record α keys}
  {key : String}
  {a b : α}
  (contains : Contains record key a)
  : Contains (insert record key b) key b
  := match contains with
    | .head _ _ => by
      simp [insert]
      exact .head _ _
    | .tail cur_key _ neq _ contains_tail => by
      simp [insert, neq]
      exact .tail _ _ neq _ (contains_after_insert contains_tail)

theorem insert_contains_step
  {keys : List String}
  {record : Record α keys}
  {key cur_key : String}
  {neq : key ≠ cur_key}
  {a b : α}
  {not_in : cur_key ∉ keys}
  : insert (.cons cur_key not_in a record) key b
      = .cons cur_key not_in a (insert record key b)
  := by simp [insert, neq]

theorem insert_contains
  {keys : List String}
  {record : Record α keys}
  {key : String}
  {a : α}
  : Contains record key a
  → Record.insert record key a = record
    | Contains.head _ _ => by simp [insert]
    | Contains.tail _ _ neq _ contains => by
        simp [insert, neq]
        exact insert_contains contains

end Record
