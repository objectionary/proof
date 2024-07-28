import Minimal.ARS
import Minimal.Term

open Term

set_option autoImplicit false

/-! ### Defition of parallel reduction `⇛` -/

mutual
  -- | tᵢ => tᵢ' for all i with ⟦ ... αᵢ ↦ tᵢ ... ⟧
  --   α's are given by `lst`
  inductive Premise : { lst : List Attr } → (l1 : Bindings lst) → (l2 : Bindings lst) → Type where
    | nil : Premise .nil .nil
    | consVoid
      : (a : Attr)
      → { lst : List Attr }
      → { l1 : Bindings lst }
      → { l2 : Bindings lst }
      → { not_in : a ∉ lst }
      → Premise l1 l2
      → Premise (.cons a not_in none l1) (.cons a not_in none l2)
    | consAttached
      : (a : Attr)
      → (t1 : Term)
      → (t2 : Term)
      → PReduce t1 t2
      → { lst : List Attr }
      → { l1 : Bindings lst }
      → { l2 : Bindings lst }
      → { not_in : a ∉ lst }
      → Premise l1 l2
      → Premise (.cons a not_in (some t1) l1) (.cons a not_in (some t2) l2)

  /-- Parallel reduction [KS22, Fig. 2] -/
  inductive PReduce : Term → Term → Type where
    | pcongOBJ
      : { lst : List Attr }
      → (l : Bindings lst)
      → (newAttrs : Bindings lst)
      → Premise l newAttrs
      → PReduce (obj l) (obj newAttrs)
    | pcong_ρ : ∀ n, PReduce (loc n) (loc n)
    | pcongDOT : ∀ t t' a, PReduce t t' → PReduce (dot t a) (dot t' a)
    | pcongAPP : ∀ t t' u u' a, PReduce t t' → PReduce u u' → PReduce (app t a u) (app t' a u')
    | pdot_c
      : { t t' : Term }
      → (t_c : Term)
      → (c : Attr)
      → { lst : List Attr }
      → (l : Bindings lst)
      → PReduce t t'
      → t' = obj l
      → lookup l c = some (some t_c)
      → PReduce (dot t c) (substitute (0, t') t_c)
    | pdot_cφ
      : { t t' : Term }
      → (c : Attr)
      → { lst : List Attr }
      → (l : Bindings lst)
      → PReduce t t'
      → t' = obj l
      → lookup l c = none
      → "φ" ∈ lst
      → PReduce (dot t c) (dot (dot t' "φ") c)
    | papp_c
      : { t t' u u' : Term }
      → (c : Attr)
      → { lst : List Attr }
      → (l : Bindings lst)
      → PReduce t t'
      → PReduce u u'
      → t' = obj l
      → lookup l c = some none
      → PReduce (app t c u) (obj (insert_φ l c (some (incLocators u'))))
end

def ParMany := ReflTransGen PReduce

infix:20 " ⇛ " => PReduce
infix:20 " ⇛* " => ParMany

def get_premise
  { attrs : List Attr }
  { bnds bnds' : Bindings attrs }
  (preduce : obj bnds ⇛ obj bnds')
  : Premise bnds bnds'
  := match preduce with
    | PReduce.pcongOBJ _ _ premise => premise
