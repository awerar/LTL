{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.1-Lib.Sets -- what the searches over lists run on, at any element type:
-- an order on Nat to measure lists by, deciding whether every member passes a
-- test (decideAll, with a counterexample if not), and the facts that a filter
-- removing something shrinks its list and that a list is empty or has a
-- member.  Plain membership lemmas are in LTL.1-Lib.Prelude; the part that
-- needs an equality test on the elements is LTL.1-Lib.DecEq.

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
-- Deciding whether every member of a list passes a boolean test, with a
-- counterexample when one fails.  This is the case split every removing search
-- makes: a counterexample is removed and the search goes on, or all pass and
-- the search stops with that fact, the one its callers go on to use.

data AllDecision {A : Set} (p : A -> Bool) (xs : List A) : Set where
  counterexample : (x : A) -> x ∈ xs -> p x ≡ false -> AllDecision p xs
  allTrue        : (∀ⁱ[ x ∈ xs ] p x ≡ true)         -> AllDecision p xs

emptyAll : {A : Set} (p : A -> Bool) -> ∀ⁱ[ x ∈ [] ] p x ≡ true
emptyAll p ()

consAll : {A : Set} {p : A -> Bool} {y : A} {ys : List A}
       -> p y ≡ true -> (∀ⁱ[ x ∈ ys ] p x ≡ true)
       -> ∀ⁱ[ x ∈ y ∷ ys ] p x ≡ true
consAll e f here      = e
consAll e f (there m) = f m

decideAllCons : {A : Set} {p : A -> Bool} {y : A} {ys : List A} (b : Bool)
             -> p y ≡ b -> AllDecision p ys -> AllDecision p (y ∷ ys)
decideAllCons true  e (counterexample x m q) = counterexample x (there m) q
decideAllCons true  e (allTrue f)            = allTrue (consAll e f)
decideAllCons false e r                      = counterexample _ here e

decideAll : {A : Set} (p : A -> Bool) (xs : List A) -> AllDecision p xs
decideAll p []       = allTrue (emptyAll p)
decideAll p (y ∷ ys) = decideAllCons (p y) refl (decideAll p ys)

------------------------------------------------------------------------
-- filter against length: a filter that removes a member shrinks the list

filter-≤ : {A : Set} (p : A -> Bool) (xs : List A)
        -> length (filter p xs) ≤ length xs
filter-≤ p []       = z≤n
filter-≤ p (y ∷ ys) = aux (p y)
  where
    aux : (b : Bool)
       -> length (if b then (y ∷ filter p ys) else filter p ys) ≤ suc (length ys)
    aux true  = s≤s    (filter-≤ p ys)
    aux false = ≤-step (filter-≤ p ys)

filter-< : {A : Set} (p : A -> Bool) (xs : List A)
        -> ∃[ x ∈ xs ] p x ≡ false
        -> suc (length (filter p xs)) ≤ length xs
filter-< p []       (x , ()      , e)
filter-< p (y ∷ ys) (x , here    , e) =
  subst (λ b -> suc (length (if b then (y ∷ filter p ys) else filter p ys))
                ≤ suc (length ys))
        (sym e) (s≤s (filter-≤ p ys))
filter-< p (y ∷ ys) (x , there m , e) = aux (p y)
  where
    aux : (b : Bool)
       -> suc (length (if b then (y ∷ filter p ys) else filter p ys)) ≤ suc (length ys)
    aux true  = s≤s    (filter-< p ys (x , m , e))
    aux false = ≤-step (filter-< p ys (x , m , e))

length-≤0-∈ : {A : Set} (xs : List A) {x : A}
           -> length xs ≤ zero -> x ∈ xs -> Empty
length-≤0-∈ []       l  ()
length-≤0-∈ (y ∷ ys) () m

------------------------------------------------------------------------
-- null

null-∈ : {A : Set} (xs : List A) {x : A}
      -> null xs ≡ true -> x ∈ xs -> Empty
null-∈ []       e  ()
null-∈ (y ∷ ys) () m

null-false : {A : Set} (xs : List A) -> null xs ≡ false
          -> Σ[ x ∈ A ] x ∈ xs
null-false []       ()
null-false (y ∷ ys) e = y , here

-- null (xs ++ ys) is false when null xs is
null-++-false-introˡ : {A : Set} (xs ys : List A) -> null xs ≡ false
                    -> null (xs ++ ys) ≡ false
null-++-false-introˡ []       ys ()
null-++-false-introˡ (x ∷ xs) ys e = refl
