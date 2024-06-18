import Minimal.Term
import Minimal.Reduction.Parallel.AuxilaryProperties
import Minimal.Reduction.Parallel.Definition
import Minimal.Reduction.Parallel.Substitution

open Term

set_option autoImplicit false

mutual
/-- Complete Development [KS22, Definition 3.6] -/
@[simp]
def complete_development : Term → Term
  | loc n => loc n
  | dot t a => match (complete_development t) with
    | @obj attrs bnds => match (lookup bnds a) with
      | some (some t_a) => (substitute (0, (obj bnds)) t_a)
      | some none => dot (obj bnds) a
      | none => if ("φ" ∈ attrs) then dot (dot (obj bnds) "φ") a else dot (obj bnds) a
    | t' => dot t' a
  | app t a u => match (complete_development t) with
    | @obj attrs bnds => match (lookup bnds a) with
      | some none => obj (insert_φ bnds a (some (incLocators (complete_development u))))
      | _ => app (obj bnds) a (complete_development u)
    | _ => app (complete_development t) a (complete_development u)
  | obj bnds => obj (complete_developmentLst bnds)
@[simp]
def complete_developmentLst {lst : List Attr} : Bindings lst → Bindings lst
  | Bindings.nil => Bindings.nil
  | Bindings.cons a lst none tail => Bindings.cons a lst none (complete_developmentLst tail)
  | Bindings.cons a lst (some t) tail => Bindings.cons a lst (some (complete_development t)) (complete_developmentLst tail)
end

mutual
/-- Term reduces (`⇛`) to its complete development [KS22, Proposition 3.7] -/
def term_to_development
  (t : Term)
  : t ⇛ complete_development t
  := match t with
    | loc n => by simp [complete_development]; exact prefl (loc n)
    | dot t a => by
        simp [complete_development]
        split
        . rename_i cd_is_obj
          rename_i l
          rename_i attrs
          split
          . rename_i lookup_attached
            rename_i u
            have goal := PReduce.pdot_c u a l (term_to_development t) cd_is_obj lookup_attached
            simp [cd_is_obj] at goal
            exact goal
          . have goal := PReduce.pcongDOT t (complete_development t) a (term_to_development t)
            simp [cd_is_obj] at goal
            exact goal
          . rename_i lookup_none
            exact dite ("φ" ∈ attrs)
              (λ φ_in => by
                simp [φ_in]
                have temp := term_to_development t
                simp [cd_is_obj] at temp
                exact PReduce.pdot_cφ a l temp rfl lookup_none φ_in
              )
              (λ not_in => by
                simp [not_in]
                have goal := PReduce.pcongDOT t (complete_development t) a (term_to_development t)
                simp [cd_is_obj] at goal
                exact goal
              )
        . rename_i cd_not_obj
          exact PReduce.pcongDOT t (complete_development t) a (term_to_development t)
    | app t a u => by
        simp [complete_development]
        split
        . rename_i cd_is_obj
          rename_i l
          split
          . rename_i lookup_void
            exact PReduce.papp_c a l (term_to_development t) (term_to_development u) cd_is_obj lookup_void
          . rename_i lookup_not_void
            have goal := PReduce.pcongAPP
              t
              (complete_development t)
              u
              (complete_development u)
              a
              (term_to_development t)
              (term_to_development u)
            simp [cd_is_obj] at goal
            exact goal
        . exact PReduce.pcongAPP
            t
            (complete_development t)
            u
            (complete_development u)
            a
            (term_to_development t)
            (term_to_development u)

    | obj bnds => by
        simp [complete_development]
        exact PReduce.pcongOBJ
          bnds
          (complete_developmentLst bnds)
          (term_to_development_Lst bnds)

def term_to_development_Lst
  { lst : List Attr}
  ( l : Bindings lst)
  : Premise l (complete_developmentLst l)
  := by match l with
  | Bindings.nil => simp ; exact Premise.nil
  | Bindings.cons _ _ none premise_tail =>
    simp
    apply Premise.consVoid
    exact term_to_development_Lst premise_tail
  | Bindings.cons _ _ (some t) premise_tail =>
    simp
    apply Premise.consAttached
    . exact term_to_development t
    . exact term_to_development_Lst premise_tail
end


/-- Half Diamond [KS22, Proposition 3.8] -/
def half_diamond
  { t t' : Term }
  (preduce : PReduce t t')
  : PReduce t' (complete_development t)
  := match preduce with
    | .pcongOBJ l newAttrs premise => by
        simp [complete_development]
        let rec make_premise
          { lst : List Attr }
          { l l' : Bindings lst }
          (premise : Premise l l')
          : Premise l' (complete_developmentLst l)
          := match lst with
            | [] => match l, l' with
              | Bindings.nil, Bindings.nil => Premise.nil
            | a :: as => match premise with
              | Premise.consVoid _ premise_tail => by
                  simp [complete_development]
                  exact Premise.consVoid a (make_premise premise_tail)
              | Premise.consAttached _ t1 t2 preduce premise_tail => by
                  simp [complete_development]
                  exact Premise.consAttached
                    a
                    t2
                    (complete_development t1)
                    (half_diamond preduce)
                    (make_premise premise_tail)
        exact PReduce.pcongOBJ newAttrs (complete_developmentLst l) (make_premise premise)
    | .pcong_ρ n => by
        simp [complete_development]
        exact prefl (loc n)
    | .pcongDOT lt lt' a preduce => by
        simp [complete_development]
        split
        . rename_i cd_is_obj
          rename_i l
          rename_i attrs
          have assumption_preduce := half_diamond preduce
          simp [cd_is_obj] at assumption_preduce
          split
          . rename_i lookup_attached
            rename_i u
            exact PReduce.pdot_c u a l assumption_preduce rfl lookup_attached
          . exact PReduce.pcongDOT lt' (obj l) a assumption_preduce
          . rename_i lookup_none
            exact dite ("φ" ∈ attrs)
              (λ φ_in => by
                simp [φ_in]
                exact PReduce.pdot_cφ a l assumption_preduce rfl lookup_none φ_in
              )
              (λ not_in => by
                simp [not_in]
                exact PReduce.pcongDOT lt' (obj l) a assumption_preduce
              )
        . rename_i cd_not_obj
          exact PReduce.pcongDOT lt' (complete_development lt) a (half_diamond preduce)
    | .pcongAPP lt lt' lu lu' a preduce_lt preduce_lu => by
        simp [complete_development]
        split
        . rename_i cd_is_obj
          rename_i l
          rename_i attrs
          have assumption_preduce_lt := half_diamond preduce_lt
          have assumption_preduce_lu := half_diamond preduce_lu
          simp [cd_is_obj] at assumption_preduce_lt
          split
          . rename_i lookup_void
            exact PReduce.papp_c a l assumption_preduce_lt (assumption_preduce_lu) rfl lookup_void
          . rename_i lookup_void
            exact PReduce.pcongAPP lt' (obj l) lu' (complete_development lu) a assumption_preduce_lt assumption_preduce_lu
        . rename_i cd_not_obj
          exact PReduce.pcongAPP
            lt'
            (complete_development lt)
            lu'
            (complete_development lu)
            a
            (half_diamond preduce_lt)
            (half_diamond preduce_lu)
    | @PReduce.pdot_c lt lt' t_c c _ l preduce eq lookup_eq => by
        let pred
          : lt' ⇛ complete_development lt
          := half_diamond preduce
        generalize h : complete_development lt = foo
        simp [eq, h] at pred
        cases pred with
          | pcongOBJ l newAttrs premise =>
          simp [complete_development, h]
          let ⟨u, PProd.mk lookup_attached tc_to_u⟩ := lookup_attached_premise lookup_eq premise
          simp [lookup_attached, eq]
          let min_free_locs
            : le_nat_option_nat 0 (min_free_loc 0 (obj newAttrs))
            := by
              simp [le_nat_option_nat]
              split
              . exact Nat.zero_le _
              . simp
          exact substitution_lemma 0 tc_to_u (.pcongOBJ l newAttrs premise) min_free_locs

    | @PReduce.pdot_cφ lt lt' c lst l preduce eq lookup_none is_attr => by
        let pred
          : lt' ⇛ complete_development lt
          := half_diamond preduce
        generalize h : complete_development lt = foo
        simp [eq, h] at pred
        cases pred with
          | @pcongOBJ _ _ newAttrs premise =>
              simp [complete_development, h]
              let lookup_none
                := lookup_none_preserve lookup_none newAttrs
              simp [lookup_none, is_attr]
              let preduce := (PReduce.pcongOBJ _ _ premise)
              simp [<-eq] at preduce
              exact .pcongDOT _ _ c (.pcongDOT _ _ "φ" preduce)
    | @PReduce.papp_c lt lt' lu lu' c _ l preduce_t preduce_u eq lookup_eq => by
        let preduce_t' := half_diamond preduce_t
        let preduce_u' := half_diamond preduce_u
        generalize h : complete_development lt = foo
        simp [eq, h] at preduce_t'
        cases preduce_t' with
          | pcongOBJ _ newAttrs premise =>
              simp [complete_development, h]
              let lookup_void
                := lookup_void_premise lookup_eq premise
              simp [lookup_void]
              exact .pcongOBJ
                _
                _
                (singlePremiseInsert (preduce_incLocatorsFrom 0 preduce_u') premise)

def takahashi_preduce : Takahashi PReduce
  := ⟨complete_development, half_diamond⟩

def diamond_preduce : DiamondProperty PReduce
  := takahashi_implies_diamond takahashi_preduce

def confluence_preduce : Confluence PReduce
  := diamond_implies_confluence diamond_preduce
