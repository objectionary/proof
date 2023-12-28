set_option autoImplicit false

@[reducible]
def Attr := String

mutual
  inductive OptionalAttr where
    | attached : Term → OptionalAttr
    | void : OptionalAttr

  inductive Term : Type where
    | loc : Nat → Term
    | dot : Term → Attr → Term
    | app : Term → Attr → Term → Term
    | obj : (List (Attr × OptionalAttr)) → Term
end
open OptionalAttr
open Term

def mapObj : (Term → Term) → (List (Attr × OptionalAttr)) → (List (Attr × OptionalAttr))
  := λ f o =>
  let f' := λ (attr_name, attr_body) =>
      match attr_body with
        | void => (attr_name, void)
        | attached x => (attr_name, attached (f x))
  (f' <$> o)

partial def incLocatorsFrom : Nat → Term → Term
  := λ k term => match term with
    | loc n => if n ≥ k then loc (n+1) else loc n
    | dot t a => dot (incLocatorsFrom k t) a
    | app t a u => app (incLocatorsFrom k t) a (incLocatorsFrom k u)
    | obj o => (obj (mapObj (incLocatorsFrom (k+1)) o))


partial def incLocators : Term → Term
  := incLocatorsFrom 0


partial def substituteLocator : Int × Term → Term → Term
  := λ (k, v) term => match term with
    | obj o => obj (mapObj (substituteLocator (k + 1, incLocators v)) o)
    | dot t a => dot (substituteLocator (k, v) t) a
    | app t a u => app (substituteLocator (k, v) t) a (substituteLocator (k, v) u)
    | loc n =>
      if (n < k) then (loc n)
      else if (n == k) then v
      else loc (n-1)

-- def checkUniqueAttributes : (List (Attr × OptionalAttr)) → Bool
--   | _ => true

def lookup : (List (Attr × OptionalAttr)) → Attr → Option OptionalAttr
  := λ l a => match l with
    | [] => none
    | List.cons (name, term) tail =>
        if (name == a) then term
        else lookup tail a

def insert : (List (Attr × OptionalAttr)) → Attr → OptionalAttr → (List (Attr × OptionalAttr))
  := λ l a u => match l with
    | [] => []
    | List.cons (name, term) tail =>
        if (name == a) then List.cons (name, u) tail
        else List.cons (name, term) (insert tail a u)


partial def whnf : Term → Term
  | loc n => loc n
  | obj o => obj o
  | app t a u => match (whnf t) with
    | obj o => match lookup o a with
      | none => app (obj o) a u
      | some (attached _) => app (obj o) a u
      | some void => obj (insert o a (attached (incLocators u)))
    | t' => app t' a u
  | dot t a => match (whnf t) with
    | obj o => match lookup o a with
      | some (attached u) => whnf (substituteLocator (0, obj o) u)
      | some void => dot (obj o) a
      | none => match lookup o "φ" with
        | some _ => dot (dot (obj o) "φ") a
        | none => dot (obj o) a
    | t' => dot t' a

partial def nf : Term → Term
  | loc n => loc n
  | obj o => obj (mapObj nf o)
  | app t a u => match (whnf t) with
    | obj o => match lookup o a with
      | none => app (nf (obj o)) a (nf u)
      | some (attached _) => app (nf (obj o)) a (nf u)
      | some void => nf (obj (insert o a (attached (incLocators u))))
    | t' => app (nf t') a (nf u)
  | dot t a => match (whnf t) with
    | obj o => match lookup o a with
      | some (attached u) => nf (substituteLocator (0, obj o) u)
      | some void => dot (nf (obj o)) a
      | none => match lookup o "φ" with
        | some _ => nf (dot (dot (obj o) "φ") a)
        | none => dot (nf (obj o)) a
    | t' => dot (nf t') a
