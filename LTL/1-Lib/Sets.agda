{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.1-Lib.Sets -- lists as finite sets over any element type: the searching,
-- filtering and counting lemmas the searches run on.  The part that needs an
-- equality test on the elements is LTL.1-Lib.Nodes.

module LTL.1-Lib.Sets where

open import LTL.1-Lib.Prelude public

------------------------------------------------------------------------
-- Order on Nat.  Only barOfList (LTL.1-Lib.Nodes) uses it, to bound the length
-- of a list.

infix 4 _≤_

data _≤_ : Nat -> Nat -> Set where
  leZero : {n : Nat}            -> zero ≤ n
  leSuc  : {n m : Nat} -> n ≤ m -> suc n ≤ suc m

leRefl : (n : Nat) -> n ≤ n
leRefl zero    = leZero
leRefl (suc n) = leSuc (leRefl n)

leStep : {n m : Nat} -> n ≤ m -> n ≤ suc m
leStep leZero    = leZero
leStep (leSuc l) = leSuc (leStep l)

leTrans : {a b c : Nat} -> a ≤ b -> b ≤ c -> a ≤ c
leTrans leZero    l         = leZero
leTrans (leSuc k) (leSuc l) = leSuc (leTrans k l)

lePred : {a b : Nat} -> suc a ≤ suc b -> a ≤ b
lePred (leSuc l) = l

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
-- filter against membership

filterCons-case : {A : Set} {x y : A} (b : Bool) (ys : List A)
               -> x ∈ filterCons b y ys -> x ≡ y ⊎ x ∈ ys
filterCons-case true  ys here      = inl refl
filterCons-case true  ys (there m) = inr m
filterCons-case false ys m         = inr m

filter-sub : {A : Set} (p : A -> Bool) (xs : List A)
          -> ∀ⁱ[ x ∈ filter p xs ] x ∈ xs
filter-sub p []       ()
filter-sub p (y ∷ ys) m =
  sumElim (λ e  -> subst (λ z -> z ∈ y ∷ ys) (sym e) here)
          (λ m' -> there (filter-sub p ys m'))
          (filterCons-case (p y) (filter p ys) m)

filterCons-prop : {A : Set} {p : A -> Bool} {x y : A} (b : Bool) -> p y ≡ b
               -> (ys : List A) -> x ∈ filterCons b y ys
               -> (x ∈ ys -> p x ≡ true) -> p x ≡ true
filterCons-prop true  e ys here      k = e
filterCons-prop true  e ys (there m) k = k m
filterCons-prop false e ys m         k = k m

filter-prop : {A : Set} (p : A -> Bool) (xs : List A)
           -> ∀ⁱ[ x ∈ filter p xs ] p x ≡ true
filter-prop p []       ()
filter-prop p (y ∷ ys) m =
  filterCons-prop (p y) refl (filter p ys) m (filter-prop p ys)

------------------------------------------------------------------------
-- filter against length

filter-le : {A : Set} (p : A -> Bool) (xs : List A)
         -> length (filter p xs) ≤ length xs
filter-le p []       = leZero
filter-le p (y ∷ ys) = aux (p y)
  where
    aux : (b : Bool)
       -> length (filterCons b y (filter p ys)) ≤ suc (length ys)
    aux true  = leSuc  (filter-le p ys)
    aux false = leStep (filter-le p ys)

filter-lt : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
         -> x ∈ xs -> p x ≡ false
         -> suc (length (filter p xs)) ≤ length xs
filter-lt p []       ()       e
filter-lt p (y ∷ ys) here     e =
  subst (λ b -> suc (length (filterCons b y (filter p ys))) ≤
                suc (length ys))
        (sym e) (leSuc (filter-le p ys))
filter-lt p (y ∷ ys) (there m) e = aux (p y)
  where
    aux : (b : Bool)
       -> suc (length (filterCons b y (filter p ys))) ≤ suc (length ys)
    aux true  = leSuc  (filter-lt p ys m e)
    aux false = leStep (filter-lt p ys m e)

leZeroNil : {A : Set} (xs : List A) {x : A}
         -> length xs ≤ zero -> x ∈ xs -> Empty
leZeroNil []       l  ()
leZeroNil (y ∷ ys) () m

null-mem : {A : Set} (xs : List A) {x : A}
        -> null xs ≡ true -> x ∈ xs -> Empty
null-mem []       e  ()
null-mem (y ∷ ys) () m

------------------------------------------------------------------------
-- any

any-true : {A : Set} (p : A -> Bool) (xs : List A) -> any p xs ≡ true
        -> ∃[ x ∈ xs ] p x ≡ true
any-true p []       ()
any-true p (y ∷ ys) e =
  sumElim (λ e1 -> y , here , e1)
          (λ e2 -> there-∃ (any-true p ys e2))
          (∨ᵇ-true (p y) (any p ys) e)

any-intro : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
         -> x ∈ xs -> p x ≡ true -> any p xs ≡ true
any-intro p []       ()        e
any-intro p (y ∷ ys) here      e = ∨ᵇ-introˡ (p y) (any p ys) e
any-intro p (y ∷ ys) (there m) e =
  ∨ᵇ-introʳ (p y) (any p ys) (any-intro p ys m e)

any-false : {A : Set} (p : A -> Bool) (xs : List A) -> any p xs ≡ false
         -> ∀ⁱ[ x ∈ xs ] p x ≡ false
any-false p []       e  ()
any-false p (y ∷ ys) e here      = ∨ᵇ-falseˡ (p y) (any p ys) e
any-false p (y ∷ ys) e (there m) =
  any-false p ys (∨ᵇ-falseʳ (p y) (any p ys) e) m

------------------------------------------------------------------------
-- null

null-false : {A : Set} (xs : List A) -> null xs ≡ false
          -> Σ[ x ∈ A ] x ∈ xs
null-false []       ()
null-false (y ∷ ys) e = y , here

appNotNull : {A : Set} (xs ys : List A) -> null xs ≡ false
          -> null (xs ++ ys) ≡ false
appNotNull []       ys ()
appNotNull (x ∷ xs) ys e = refl

------------------------------------------------------------------------
-- map against membership

map-mem-inv : {A B : Set} (f : A -> B) (xs : List A)
           -> ∀ⁱ[ y ∈ map f xs ] ∃[ x ∈ xs ] y ≡ f x
map-mem-inv f []       ()
map-mem-inv f (x ∷ xs) here      = x , here , refl
map-mem-inv f (x ∷ xs) (there m) = there-∃ (map-mem-inv f xs m)

------------------------------------------------------------------------
-- The kinds of step in a certificate of LTL.1-Lib.FairGraph, one per constructor
-- of Cert.  Declared here, outside that module, so that the type does not
-- depend on its edge test.

data CertStep : Set where
  removedSink removedBlock emptied : CertStep
