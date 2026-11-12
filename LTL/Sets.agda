{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Sets -- the list and set infrastructure the searches of Phases 5, 6 and
-- 8 run on.  It was the first half of LTL.Gfp until Phase 8; LTL.Bar has to sit
-- between the infrastructure and the greatest fixed point, since Bar needs
-- filter and ∈ᵛ while the shrinking iteration of LTL.Gfp is now defined by
-- recursion on a Bar.
--
-- _≤_ survives only inside barOfList, which is the bridge from a Kuratowski
-- finite list to an inductively finite predicate (LTL.Bar).  Nothing else in
-- the development counts any more.

module LTL.Sets where

open import LTL.Reach public

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

filterCons_case : {A : Set} {x y : A} (b : Bool) (ys : List A)
               -> x ∈ filterCons b y ys -> x ≡ y ⊎ x ∈ ys
filterCons_case true  ys here      = inl refl
filterCons_case true  ys (there m) = inr m
filterCons_case false ys m         = inr m

filter_sub : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
          -> x ∈ filter p xs -> x ∈ xs
filter_sub p []       ()
filter_sub p (y ∷ ys) m =
  sumElim (λ e  -> subst (λ z -> z ∈ y ∷ ys) (sym e) here)
          (λ m' -> there (filter_sub p ys m'))
          (filterCons_case (p y) (filter p ys) m)

filterCons_prop : {A : Set} {p : A -> Bool} {x y : A} (b : Bool) -> p y ≡ b
               -> (ys : List A) -> x ∈ filterCons b y ys
               -> (x ∈ ys -> p x ≡ true) -> p x ≡ true
filterCons_prop true  e ys here      k = e
filterCons_prop true  e ys (there m) k = k m
filterCons_prop false e ys m         k = k m

filter_prop : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
           -> x ∈ filter p xs -> p x ≡ true
filter_prop p []       ()
filter_prop p (y ∷ ys) m =
  filterCons_prop (p y) refl (filter p ys) m (filter_prop p ys)

------------------------------------------------------------------------
-- filter against length.  This is the whole termination argument.

filter_le : {A : Set} (p : A -> Bool) (xs : List A)
         -> length (filter p xs) ≤ length xs
filter_le p []       = leZero
filter_le p (y ∷ ys) = aux (p y)
  where
    aux : (b : Bool)
       -> length (filterCons b y (filter p ys)) ≤ suc (length ys)
    aux true  = leSuc  (filter_le p ys)
    aux false = leStep (filter_le p ys)

filter_lt : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
         -> x ∈ xs -> p x ≡ false
         -> suc (length (filter p xs)) ≤ length xs
filter_lt p []       ()       e
filter_lt p (y ∷ ys) here     e =
  subst (λ b -> suc (length (filterCons b y (filter p ys))) ≤
                suc (length ys))
        (sym e) (leSuc (filter_le p ys))
filter_lt p (y ∷ ys) (there m) e = aux (p y)
  where
    aux : (b : Bool)
       -> suc (length (filterCons b y (filter p ys))) ≤ suc (length ys)
    aux true  = leSuc  (filter_lt p ys m e)
    aux false = leStep (filter_lt p ys m e)

leZeroNil : {A : Set} (xs : List A) {x : A}
         -> length xs ≤ zero -> x ∈ xs -> Empty
leZeroNil []       l  ()
leZeroNil (y ∷ ys) () m

null_mem : {A : Set} (xs : List A) {x : A}
        -> null xs ≡ true -> x ∈ xs -> Empty
null_mem []       e  ()
null_mem (y ∷ ys) () m

------------------------------------------------------------------------
-- any

any_true : {A : Set} (p : A -> Bool) (xs : List A) -> any p xs ≡ true
        -> Σ[ x ∈ A ] x ∈ xs × p x ≡ true
any_true {A} p []       ()
any_true {A} p (y ∷ ys) e =
  sumElim (λ e1 -> y , here , e1)
          (λ e2 -> shift (any_true p ys e2))
          (orTrue (p y) (any p ys) e)
  where
    shift : (Σ[ x ∈ A ] x ∈ ys × p x ≡ true)
         -> Σ[ x ∈ A ] x ∈ y ∷ ys × p x ≡ true
    shift (x , m , q) = x , there m , q

any_intro : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
         -> x ∈ xs -> p x ≡ true -> any p xs ≡ true
any_intro p []       ()        e
any_intro p (y ∷ ys) here      e = orL (p y) (any p ys) e
any_intro p (y ∷ ys) (there m) e = orR (p y) (any p ys) (any_intro p ys m e)

any_false : {A : Set} (p : A -> Bool) (xs : List A) -> any p xs ≡ false
         -> {x : A} -> x ∈ xs -> p x ≡ false
any_false p []       e  ()
any_false p (y ∷ ys) e here      = orFalseL (p y) (any p ys) e
any_false p (y ∷ ys) e (there m) =
  any_false p ys (orFalseR (p y) (any p ys) e) m

------------------------------------------------------------------------
-- all

all_false : {A : Set} (p : A -> Bool) (xs : List A) -> all p xs ≡ false
         -> Σ[ x ∈ A ] x ∈ xs × p x ≡ false
all_false {A} p []       ()
all_false {A} p (y ∷ ys) e =
  sumElim (λ e1 -> y , here , e1)
          (λ e2 -> shift (all_false p ys e2))
          (andFalse (p y) (all p ys) e)
  where
    shift : (Σ[ x ∈ A ] x ∈ ys × p x ≡ false)
         -> Σ[ x ∈ A ] x ∈ y ∷ ys × p x ≡ false
    shift (x , m , q) = x , there m , q

null_false : {A : Set} (xs : List A) -> null xs ≡ false
          -> Σ[ x ∈ A ] x ∈ xs
null_false []       ()
null_false (y ∷ ys) e = y , here

------------------------------------------------------------------------
-- Reading a successor list

succsMem : (P : Formula) (us : List Val) (v : Val) {w : Val}
        -> w ∈ succs P us v -> w ∈ us × step P v w ≡ true
succsMem P us v m =
  filter_sub (step P v) us m , filter_prop (step P v) us m

succsIn : (P : Formula) (us : List Val) (v : Val) {w : Val}
       -> w ∈ us -> step P v w ≡ true -> w ∈ succs P us v
succsIn P us v mw st = filter_true (step P v) us mw st

------------------------------------------------------------------------
-- Valuations as a set

eqCons : {b c : Bool} {v w : Val} -> b ≡ c -> v ≡ w -> b ∷ v ≡ c ∷ w
eqCons refl refl = refl

≡ᵛ-sound : (v w : Val) -> v ≡ᵛ w ≡ true -> v ≡ w
≡ᵛ-sound []      []      e = refl
≡ᵛ-sound []      (c ∷ w) ()
≡ᵛ-sound (b ∷ v) []      ()
≡ᵛ-sound (b ∷ v) (c ∷ w) e =
  eqCons (⇔ᵇ-sound b c (andTrueL (b ⇔ᵇ c) (v ≡ᵛ w) e))
         (≡ᵛ-sound v w (andTrueR (b ⇔ᵇ c) (v ≡ᵛ w) e))

∈ᵛ-sound : (v : Val) (us : List Val) -> v ∈ᵛ us ≡ true -> v ∈ us
∈ᵛ-sound v []       ()
∈ᵛ-sound v (u ∷ us) e =
  sumElim (λ e1 -> subst (λ z -> v ∈ z ∷ us) (≡ᵛ-sound v u e1) here)
          (λ e2 -> there (∈ᵛ-sound v us e2))
          (orTrue (v ≡ᵛ u) (any (v ≡ᵛ_) us) e)

∈ᵛ-complete : (v : Val) (us : List Val) -> v ∈ us -> v ∈ᵛ us ≡ true
∈ᵛ-complete v []       ()
∈ᵛ-complete v (u ∷ us) here     =
  orL (v ≡ᵛ v) (any (v ≡ᵛ_) us) (≡ᵛ-refl v)
∈ᵛ-complete v (u ∷ us) (there m) =
  orR (v ≡ᵛ u) (any (v ≡ᵛ_) us) (∈ᵛ-complete v us m)

∈ᵛ-false : (v : Val) (us : List Val) -> v ∈ᵛ us ≡ false -> v ∈ us -> Empty
∈ᵛ-false v us e m = true≢false (trans (sym (∈ᵛ-complete v us m)) e)
