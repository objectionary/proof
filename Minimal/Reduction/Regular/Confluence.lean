import Minimal.ARS
import Minimal.Term
import Minimal.Reduction.Regular.Definition
import Minimal.Reduction.Parallel.AuxilaryProperties
import Minimal.Reduction.Parallel.Confluence
import Minimal.Reduction.Parallel.Definition
import Minimal.Utils

open Term

set_option autoImplicit false

/-! ### Equivalence of `⇛` and `⇝` -/

/-- Equivalence of `⇛` and `⇝` [KS22, Proposition 3.4 (1)] -/
def reg_to_par {t t' : Term} : (t ⇝ t') → (t ⇛ t')
  | .congOBJ b l red isAttached =>
      .pcongOBJ
        l
        (insert_φ l b (some _))
        (singlePremise l b _ _ isAttached (reg_to_par red))
  | .congDOT t t' a red =>
      .pcongDOT t t' a (reg_to_par red)
  | .congAPPₗ t t' u a red =>
      .pcongAPP t t' u u a (reg_to_par red) (prefl u)
  | .congAPPᵣ t u u' a red =>
      .pcongAPP t t u u' a (prefl t) (reg_to_par red)
  | @Reduce.dot_c t t_c c _ l eq lookup_eq =>
      .pdot_c t_c c l (prefl t) eq lookup_eq
  | @Reduce.dot_cφ t c _ l eq lookup_c isAttr_φ =>
      .pdot_cφ c l (prefl t) eq lookup_c isAttr_φ
  | Reduce.app_c t u c l eq lookup_eq =>
      PReduce.papp_c c l (prefl t) (prefl u) eq lookup_eq

/-- Transitivity of `⇝*` [KS22, Lemma A.3] -/
def red_trans { t t' t'' : Term } (fi : t ⇝* t') (se : t' ⇝* t'') : (t ⇝* t'')
  := ReflTransGen.trans fi se

def consBindingsRedMany
  { lst : List Attr}
  (a : Attr)
  { not_in_a : a ∉ lst }
  (u_a  : Option Term)
  { l1 l2 : Bindings lst }
  (reds : (obj l1) ⇝* (obj l2))
  : obj (Bindings.cons a not_in_a u_a l1) ⇝*
    obj (Bindings.cons a not_in_a u_a l2)
  := by
    generalize h : obj l1 = t1
    generalize h' : obj l2 = t2
    rw [h, h'] at reds
    induction reds generalizing l1 l2 with
    | refl =>
      subst h ; simp at h' ; simp [h'] ; exact .refl
    | head =>
      subst h h'
      rename_i t_i red redmany ih
      match red with
      | Reduce.congOBJ attr _ inner_red isAttached =>
        rename_i ti1 ti2
        have tail_cons := @ih (insert_φ l1 attr (some ti2)) l2 rfl rfl
        have neq := (notEqByListMem (isAttachedIsIn isAttached) not_in_a)
        have isAttached_cons : IsAttached attr ti1 (Bindings.cons a not_in_a u_a l1) :=
        IsAttached.next_attached attr ti1 l1 a neq not_in_a u_a isAttached
        have head_cons := Reduce.congOBJ attr _ inner_red isAttached_cons
        simp [insert_φ, neq.symm] at head_cons
        exact ReflTransGen.head head_cons tail_cons

/-- Congruence for `⇝*` in OBJ [KS22, Lemma A.4 (1)] -/
def congOBJClos
  { t t' : Term }
  { b : Attr }
  { lst : List Attr }
  { l : Bindings lst }
  : (t ⇝* t')
  → IsAttached b t l
  → (obj l ⇝* obj (insert_φ l b (some t')))
  := λ red_tt' isAttached => match red_tt' with
    | ReflTransGen.refl => Eq.ndrec (ReflTransGen.refl) (congrArg obj (Eq.symm (Insert.insertAttached isAttached)))
    | ReflTransGen.head red redMany => by
      rename_i t_i
      have ind_hypothesis : obj (insert_φ l b (some t_i)) ⇝* obj (insert_φ (insert_φ l b (some t_i)) b (some t'))
        := (congOBJClos redMany (Insert.insert_new_isAttached isAttached))
      exact (ReflTransGen.head
        (Reduce.congOBJ b l red isAttached)
        (Eq.ndrec ind_hypothesis
        (congrArg obj (Insert.insertTwice l b t' t_i))))

/-- Congruence for `⇝*` in DOT [KS22, Lemma A.4 (2)] -/
def congDotClos
  { t t' : Term }
  { a : Attr }
  : (t ⇝* t') → ((dot t a) ⇝* (dot t' a))
  | ReflTransGen.refl => ReflTransGen.refl
  | ReflTransGen.head lm mn_many => by
    rename_i m
    exact (ReflTransGen.head (Reduce.congDOT t m a lm) (congDotClos mn_many))

/-- Congruence for `⇝*` in APPₗ [KS22, Lemma A.4 (3)] -/
def congAPPₗClos
  { t t' u : Term }
  { a : Attr }
  : (t ⇝* t') → ((app t a u) ⇝* (app t' a u))
  | ReflTransGen.refl => ReflTransGen.refl
  | ReflTransGen.head lm mn_many => by
    rename_i m
    exact (ReflTransGen.head (Reduce.congAPPₗ t m u a lm) (congAPPₗClos mn_many))

/-- Congruence for `⇝*` in APPᵣ [KS22, Lemma A.4 (4)] -/
def congAPPᵣClos
  { t u u' : Term }
  { a : Attr }
  : (u ⇝* u') → ((app t a u) ⇝* (app t a u'))
  | ReflTransGen.refl => ReflTransGen.refl
  | ReflTransGen.head lm mn_many => by
    rename_i m
    exact ReflTransGen.head (Reduce.congAPPᵣ t u m a lm) (congAPPᵣClos mn_many)

/-- Equivalence of `⇛` and `⇝` [KS22, Proposition 3.4 (3)] -/
def par_to_redMany {t t' : Term} : (t ⇛ t') → (t ⇝* t')
  | @PReduce.pcongOBJ lst l l' premise =>
    let rec fold_premise
      { lst : List Attr }
      { al al' : Bindings lst }
      (premise : Premise al al')
      : (obj al) ⇝* (obj al')
      := match lst with
        | [] => match al, al' with
          | Bindings.nil, Bindings.nil => ReflTransGen.refl
        | a :: as => match al, al' with
          | Bindings.cons _ not_in u tail, Bindings.cons _ _ u' tail' => match premise with
            | Premise.consVoid _ premiseTail => consBindingsRedMany a none (fold_premise premiseTail)
            | @Premise.consAttached _ t1 t2 preduce _ l1 l2 not_in premiseTail => by
                suffices temp : obj (insert_φ (Bindings.cons a not_in (some t1) l1) a (some t2)) ⇝*
                  obj (Bindings.cons a _ (some t2) l2) from
                  (red_trans
                    (congOBJClos (par_to_redMany preduce) (IsAttached.zeroth_attached a _ t1 l1))
                    (temp))
                simp [insert_φ]
                exact consBindingsRedMany a (some t2) (fold_premise premiseTail)
    fold_premise premise
  | .pcong_ρ n => ReflTransGen.refl
  | .pcongDOT t t' a prtt' => congDotClos (par_to_redMany prtt')
  | .pcongAPP t t' u u' a prtt' pruu' => red_trans
    (congAPPₗClos (par_to_redMany prtt'))
    (congAPPᵣClos (par_to_redMany pruu'))
  | PReduce.pdot_c t_c c l preduce eq lookup_eq =>
    let tc_t'c_many := congDotClos (par_to_redMany preduce)
    let tc_dispatch := Reduce.dot_c t_c c l eq lookup_eq
    let tc_dispatch_clos := ReflTransGen.head tc_dispatch ReflTransGen.refl
    red_trans tc_t'c_many tc_dispatch_clos
  | PReduce.pdot_cφ c l preduce eq lookup_eq isAttr =>
    let tc_t'c_many := congDotClos (par_to_redMany preduce)
    let tφc_dispatch := Reduce.dot_cφ c l eq lookup_eq isAttr
    let tφc_dispatch_clos := ReflTransGen.head tφc_dispatch ReflTransGen.refl
    red_trans tc_t'c_many tφc_dispatch_clos
  | @PReduce.papp_c t t' u u' c lst l prtt' pruu' path_t'_obj_lst path_lst_c_void =>
    let tu_t'u_many := congAPPₗClos (par_to_redMany prtt')
    let t'u_t'u'_many := congAPPᵣClos (par_to_redMany pruu')
    let tu_t'u'_many := red_trans tu_t'u_many t'u_t'u'_many
    let tu_app := Reduce.app_c t' u' c l path_t'_obj_lst path_lst_c_void
    let tu_app_clos := ReflTransGen.head tu_app ReflTransGen.refl
    red_trans tu_t'u'_many tu_app_clos

/-- Equivalence of `⇛` and `⇝` [KS22, Proposition 3.4 (4)] -/
def parMany_to_redMany {t t' : Term} : (t ⇛* t') → (t ⇝* t')
  | ReflTransGen.refl => ReflTransGen.refl
  | ReflTransGen.head red reds => red_trans (par_to_redMany red) (parMany_to_redMany reds)

/-- Equivalence of `⇛` and `⇝` [KS22, Proposition 3.4 (2)] -/
def redMany_to_parMany {t t' : Term} : (t ⇝* t') → (t ⇛* t')
  | ReflTransGen.refl => ReflTransGen.refl
  | ReflTransGen.head red reds => ReflTransGen.head (reg_to_par red) (redMany_to_parMany reds)


/-! ### Confluence of `⇝` -/

def weakEquivRegPar : WeakEquivalence PReduce Reduce
  := ⟨parMany_to_redMany, redMany_to_parMany⟩

def confluence_reduce : Confluence Reduce
  := weak_equiv_keeps_confluence weakEquivRegPar confluence_preduce
