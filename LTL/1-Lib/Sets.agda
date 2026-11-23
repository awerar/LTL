{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.1-Lib.Sets -- what the searches over lists run on, at any element type:
-- an order on Nat to measure lists by, the search for a member failing a test,
-- and the facts that a filter removing something shrinks its list and that a
-- list is empty or has a member.  Plain membership lemmas are in
-- LTL.1-Lib.Prelude; the part that needs an equality test on the elements is
-- LTL.1-Lib.Nodes.

module LTL.1-Lib.Sets where

open import LTL.1-Lib.Prelude public

------------------------------------------------------------------------
-- Order on Nat, named as in the standard library.  Only barOfList
-- (LTL.1-Lib.Nodes) uses it, to bound the length of a list.

infix 4 _≤_

data _≤_ : Nat -> Nat -> Set where
  z≤n : {n : Nat}            -> zero ≤ n
  s≤s : {n m : Nat} -> n ≤ m -> suc n ≤ suc m

≤-refl : (n : Nat) -> n ≤ n
≤-refl zero    = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-step : {n m : Nat} -> n ≤ m -> n ≤ suc m
≤-step z≤n     = z≤n
≤-step (s≤s l) = s≤s (≤-step l)

≤-trans : {a b c : Nat} -> a ≤ b -> b ≤ c -> a ≤ c
≤-trans z≤n     l       = z≤n
≤-trans (s≤s k) (s≤s l) = s≤s (≤-trans k l)

≤-pred : {a b : Nat} -> suc a ≤ suc b -> a ≤ b
≤-pred (s≤s l) = l

------------------------------------------------------------------------
-- Searching a list for a member that fails a boolean test.  This is the case
-- split every removing search makes: either some member fails and is removed,
-- or all pass and the search stops.

data FindResult {A : Set} (p : A -> Bool) (xs : List A) : Set where
  found   : (x : A) -> x ∈ xs -> p x ≡ false -> FindResult p xs
  allTrue : (∀ⁱ[ x ∈ xs ] p x ≡ true)         -> FindResult p xs

emptyAll : {A : Set} (p : A -> Bool) -> ∀ⁱ[ x ∈ [] ] p x ≡ true
emptyAll p ()

consAll : {A : Set} {p : A -> Bool} {y : A} {ys : List A}
       -> p y ≡ true -> (∀ⁱ[ x ∈ ys ] p x ≡ true)
       -> ∀ⁱ[ x ∈ y ∷ ys ] p x ≡ true
consAll e f here      = e
consAll e f (there m) = f m

findCons : {A : Set} {p : A -> Bool} {y : A} {ys : List A} (b : Bool)
        -> p y ≡ b -> FindResult p ys -> FindResult p (y ∷ ys)
findCons true  e (found x m q) = found x (there m) q
findCons true  e (allTrue f)   = allTrue (consAll e f)
findCons false e r             = found _ here e

findFalse : {A : Set} (p : A -> Bool) (xs : List A) -> FindResult p xs
findFalse p []       = allTrue (emptyAll p)
findFalse p (y ∷ ys) = findCons (p y) refl (findFalse p ys)

------------------------------------------------------------------------
-- filter against length: a filter that removes a member shrinks the list

filter-le : {A : Set} (p : A -> Bool) (xs : List A)
         -> length (filter p xs) ≤ length xs
filter-le p []       = z≤n
filter-le p (y ∷ ys) = aux (p y)
  where
    aux : (b : Bool)
       -> length (filterCons b y (filter p ys)) ≤ suc (length ys)
    aux true  = s≤s    (filter-le p ys)
    aux false = ≤-step (filter-le p ys)

filter-lt : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
         -> x ∈ xs -> p x ≡ false
         -> suc (length (filter p xs)) ≤ length xs
filter-lt p []       ()       e
filter-lt p (y ∷ ys) here     e =
  subst (λ b -> suc (length (filterCons b y (filter p ys))) ≤
                suc (length ys))
        (sym e) (s≤s (filter-le p ys))
filter-lt p (y ∷ ys) (there m) e = aux (p y)
  where
    aux : (b : Bool)
       -> suc (length (filterCons b y (filter p ys))) ≤ suc (length ys)
    aux true  = s≤s    (filter-lt p ys m e)
    aux false = ≤-step (filter-lt p ys m e)

length-≤0-mem : {A : Set} (xs : List A) {x : A}
             -> length xs ≤ zero -> x ∈ xs -> Empty
length-≤0-mem []       l  ()
length-≤0-mem (y ∷ ys) () m

------------------------------------------------------------------------
-- null

null-mem : {A : Set} (xs : List A) {x : A}
        -> null xs ≡ true -> x ∈ xs -> Empty
null-mem []       e  ()
null-mem (y ∷ ys) () m

null-false : {A : Set} (xs : List A) -> null xs ≡ false
          -> Σ[ x ∈ A ] x ∈ xs
null-false []       ()
null-false (y ∷ ys) e = y , here

-- null (xs ++ ys) is false when null xs is
null-++-false-introˡ : {A : Set} (xs ys : List A) -> null xs ≡ false
                    -> null (xs ++ ys) ≡ false
null-++-false-introˡ []       ys ()
null-++-false-introˡ (x ∷ xs) ys e = refl

------------------------------------------------------------------------
-- The kinds of step in a certificate of LTL.1-Lib.FairGraph, one per constructor
-- of Cert.  Declared here, outside that module, so that the type does not
-- depend on its edge test.

data CertStep : Set where
  removedSink removedBlock emptied : CertStep
