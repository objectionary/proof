set_option autoImplicit false

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


def mapObj : (Term -> Term) -> (List (Attr × OptionalAttr)) -> (List (Attr × OptionalAttr))
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


partial def incLocators : Term -> Term
  := incLocatorsFrom 0


partial def substituteLocator : Int × Term -> Term -> Term
  := λ (k, v) term => match term with
    | obj o => obj (mapObj (substituteLocator (k + 1, incLocators v)) o)
    | dot t a => dot (substituteLocator (k, v) t) a
    | app t a u => app (substituteLocator (k, v) t) a (substituteLocator (k, v) u)
    | loc n =>
      if (n < k) then (loc n)
      else if (n == k) then v
      else loc (n-1)


-- partial def whnf : Term → Term
--   | loc n => loc n
--   | obj o => obj o
--   | app t a u => match (whnf t) with
--     | obj o => __
--     | t' => app t' a u

-- partial def nf : Term → Term
-- | loc n => loc n
-- | ...
