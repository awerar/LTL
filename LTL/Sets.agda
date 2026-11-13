{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Sets -- lists as finite sets, over any element type: the infrastructure
-- the searches of Phases 5, 6 and 8 run on.  It was the first half of LTL.Gfp
-- until Phase 8, and it mentioned valuations until the graph layer (LTL.Graph)
-- was made generic over its node type.  Now it imports only the prelude: the
-- searching, filtering and counting lemmas below never needed more than an
-- element type.  The part that needs an equality TEST on the elements -- ∈ᵛ and
-- the hypothesis names Closed, NoneSat, HoldsOutside -- is LTL.Nodes, which is
-- parameterised by one.
--
-- _≤_ survives only inside barOfList (LTL.Nodes), which is the bridge from a
-- Kuratowski finite list to an inductively finite predicate (LTL.Bar).
-- Nothing else in the development counts any more.

module LTL.Sets where

open import LTL.Prelude public

------------------------------------------------------------------------
-- Order on Nat.
--
-- Only needed to say that filter shortens a list, which is what makes the
-- iteration below terminate.

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
-- Boolean glue

orFalseL : (a b : Bool) -> a ∨ᵇ b ≡ false -> a ≡ false
orFalseL true  b ()
orFalseL false b e = refl

orFalseR : (a b : Bool) -> a ∨ᵇ b ≡ false -> b ≡ false
orFalseR true  b ()
orFalseR false b e = e

------------------------------------------------------------------------
-- Searching a list for a member that fails a boolean test.
--
-- This is the one case analysis the removing iteration performs: either some
-- state of W_i has a successor outside W_i, and the round removes it, or none
-- has and W_i is already closed.

data FindResult {A : Set} (p : A -> Bool) (xs : List A) : Set where
  found   : (x : A) -> x ∈ xs -> p x ≡ false -> FindResult p xs
  allTrue : ({x : A} -> x ∈ xs -> p x ≡ true)  -> FindResult p xs

emptyAll : {A : Set} (p : A -> Bool) {x : A} -> x ∈ [] -> p x ≡ true
emptyAll p ()

consAll : {A : Set} {p : A -> Bool} {y : A} {ys : List A}
       -> p y ≡ true -> ({x : A} -> x ∈ ys -> p x ≡ true)
       -> {x : A} -> x ∈ y ∷ ys -> p x ≡ true
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

filter-sub : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
          -> x ∈ filter p xs -> x ∈ xs
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

filter-prop : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
           -> x ∈ filter p xs -> p x ≡ true
filter-prop p []       ()
filter-prop p (y ∷ ys) m =
  filterCons-prop (p y) refl (filter p ys) m (filter-prop p ys)

------------------------------------------------------------------------
-- filter against length.  This is the whole termination argument.

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
        -> Σ[ x ∈ A ] x ∈ xs × p x ≡ true
any-true {A} p []       ()
any-true {A} p (y ∷ ys) e =
  sumElim (λ e1 -> y , here , e1)
          (λ e2 -> shift (any-true p ys e2))
          (orTrue (p y) (any p ys) e)
  where
    shift : (Σ[ x ∈ A ] x ∈ ys × p x ≡ true)
         -> Σ[ x ∈ A ] x ∈ y ∷ ys × p x ≡ true
    shift (x , m , q) = x , there m , q

any-intro : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
         -> x ∈ xs -> p x ≡ true -> any p xs ≡ true
any-intro p []       ()        e
any-intro p (y ∷ ys) here      e = orL (p y) (any p ys) e
any-intro p (y ∷ ys) (there m) e = orR (p y) (any p ys) (any-intro p ys m e)

any-false : {A : Set} (p : A -> Bool) (xs : List A) -> any p xs ≡ false
         -> {x : A} -> x ∈ xs -> p x ≡ false
any-false p []       e  ()
any-false p (y ∷ ys) e here      = orFalseL (p y) (any p ys) e
any-false p (y ∷ ys) e (there m) =
  any-false p ys (orFalseR (p y) (any p ys) e) m

------------------------------------------------------------------------
-- all

all-false : {A : Set} (p : A -> Bool) (xs : List A) -> all p xs ≡ false
         -> Σ[ x ∈ A ] x ∈ xs × p x ≡ false
all-false {A} p []       ()
all-false {A} p (y ∷ ys) e =
  sumElim (λ e1 -> y , here , e1)
          (λ e2 -> shift (all-false p ys e2))
          (andFalse (p y) (all p ys) e)
  where
    shift : (Σ[ x ∈ A ] x ∈ ys × p x ≡ false)
         -> Σ[ x ∈ A ] x ∈ y ∷ ys × p x ≡ false
    shift (x , m , q) = x , there m , q

null-false : {A : Set} (xs : List A) -> null xs ≡ false
          -> Σ[ x ∈ A ] x ∈ xs
null-false []       ()
null-false (y ∷ ys) e = y , here

------------------------------------------------------------------------
-- map against membership

map-mem-inv : {A B : Set} (f : A -> B) (xs : List A) {y : B}
           -> y ∈ map f xs -> Σ[ x ∈ A ] x ∈ xs × y ≡ f x
map-mem-inv f []       ()
map-mem-inv f (x ∷ xs) here      = x , here , refl
map-mem-inv f (x ∷ xs) (there m) = shift (map-mem-inv f xs m)
  where
    shift : (Σ[ z ∈ _ ] z ∈ xs × _) -> Σ[ z ∈ _ ] z ∈ x ∷ xs × _
    shift (z , mz , ez) = z , there mz , ez
