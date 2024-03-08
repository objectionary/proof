-- code adopted from Mathlib.Logic.Relation

set_option autoImplicit false

universe u
variable {α : Type u}
variable {r : α → α → Type u}
variable {a b c : α}

local infix:50 " ⇝ " => r

def Reflexive := ∀ x, x ⇝ x

def Transitive := ∀ x y z, x ⇝ y → y ⇝ z → x ⇝ z

inductive ReflTransGen (r : α → α → Type u) : α → α → Type u
  | refl {a : α} : ReflTransGen r a a
  | head {a b c : α} : r a b → ReflTransGen r b c → ReflTransGen r a c

def RTClos.trans {a b c : α} (hab : ReflTransGen r a b) (hbc : ReflTransGen r b c) : ReflTransGen r a c :=
  match hab with
  | .refl => by assumption
  | .head x tail => (trans tail hbc).head x
