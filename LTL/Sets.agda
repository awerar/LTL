{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Sets -- the list and set infrastructure the searches of Phases 5, 6 and
-- 8 run on.  It was the first half of LTL.Gfp until Phase 8; LTL.Bar has to sit
-- between the infrastructure and the greatest fixed point, since Bar needs
-- filterL and memB while the shrinking iteration of LTL.Gfp is now defined by
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
-- Only needed to say that filterL shortens a list, which is what makes the
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

notTrue : (b : Bool) -> ¬ᵇ b ≡ true -> b ≡ false
notTrue true  ()
notTrue false e = refl

notFalse : (b : Bool) -> ¬ᵇ b ≡ false -> b ≡ true
notFalse true  e = refl
notFalse false ()

⇒TrueB : (a b : Bool) -> a ⇒ᵇ b ≡ true -> a ≡ true -> b ≡ true
⇒TrueB true  b e q  = e
⇒TrueB false b e ()

⇒IntroB : (a b : Bool) -> (a ≡ true -> b ≡ true) -> a ⇒ᵇ b ≡ true
⇒IntroB true  b f = f refl
⇒IntroB false b f = refl

------------------------------------------------------------------------
-- Searching a list for a member that fails a boolean test.
--
-- This is the one case analysis the removing iteration performs: either some
-- state of W_i has a successor outside W_i, and the round removes it, or none
-- has and W_i is already closed.

data FindResult {A : Set} (p : A -> Bool) (xs : List A) : Set where
  found : (x : A) -> x ∈ xs -> p x ≡ false -> FindResult p xs
  allT  : ({x : A} -> x ∈ xs -> p x ≡ true)  -> FindResult p xs

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
findCons true  e (allT f)      = allT (consAll e f)
findCons false e r             = found _ here e

findFalse : {A : Set} (p : A -> Bool) (xs : List A) -> FindResult p xs
findFalse p []       = allT (emptyAll p)
findFalse p (y ∷ ys) = findCons (p y) refl (findFalse p ys)

------------------------------------------------------------------------
-- filterL against membership

filterCons_case : {A : Set} {x y : A} (b : Bool) (ys : List A)
               -> x ∈ filterCons b y ys -> x ≡ y ⊎ x ∈ ys
filterCons_case true  ys here      = inl refl
filterCons_case true  ys (there m) = inr m
filterCons_case false ys m         = inr m

filter_sub : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
          -> x ∈ filterL p xs -> x ∈ xs
filter_sub p []       ()
filter_sub p (y ∷ ys) m =
  sumElim (λ e  -> subst (λ z -> z ∈ y ∷ ys) (sym e) here)
          (λ m' -> there (filter_sub p ys m'))
          (filterCons_case (p y) (filterL p ys) m)

filter_true : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
           -> x ∈ xs -> p x ≡ true -> x ∈ filterL p xs
filter_true p []       ()        e
filter_true p (y ∷ ys) here      e = filterCons_hd (p y) y (filterL p ys) e
filter_true p (y ∷ ys) (there m) e =
  filterCons_mem (p y) y (filterL p ys) (filter_true p ys m e)

filterCons_prop : {A : Set} {p : A -> Bool} {x y : A} (b : Bool) -> p y ≡ b
               -> (ys : List A) -> x ∈ filterCons b y ys
               -> (x ∈ ys -> p x ≡ true) -> p x ≡ true
filterCons_prop true  e ys here      k = e
filterCons_prop true  e ys (there m) k = k m
filterCons_prop false e ys m         k = k m

filter_prop : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
           -> x ∈ filterL p xs -> p x ≡ true
filter_prop p []       ()
filter_prop p (y ∷ ys) m =
  filterCons_prop (p y) refl (filterL p ys) m (filter_prop p ys)

------------------------------------------------------------------------
-- filterL against length.  This is the whole termination argument.

filterL_le : {A : Set} (p : A -> Bool) (xs : List A)
          -> length (filterL p xs) ≤ length xs
filterL_le p []       = leZero
filterL_le p (y ∷ ys) = aux (p y)
  where
    aux : (b : Bool)
       -> length (filterCons b y (filterL p ys)) ≤ suc (length ys)
    aux true  = leSuc  (filterL_le p ys)
    aux false = leStep (filterL_le p ys)

filterL_lt : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
          -> x ∈ xs -> p x ≡ false
          -> suc (length (filterL p xs)) ≤ length xs
filterL_lt p []       ()       e
filterL_lt p (y ∷ ys) here     e =
  subst (λ b -> suc (length (filterCons b y (filterL p ys))) ≤
                suc (length ys))
        (sym e) (leSuc (filterL_le p ys))
filterL_lt p (y ∷ ys) (there m) e = aux (p y)
  where
    aux : (b : Bool)
       -> suc (length (filterCons b y (filterL p ys))) ≤ suc (length ys)
    aux true  = leSuc  (filterL_lt p ys m e)
    aux false = leStep (filterL_lt p ys m e)

leZeroNil : {A : Set} (xs : List A) {x : A}
         -> length xs ≤ zero -> x ∈ xs -> Empty
leZeroNil []       l  ()
leZeroNil (y ∷ ys) () m

nullB_mem : {A : Set} (xs : List A) {x : A}
         -> nullB xs ≡ true -> x ∈ xs -> Empty
nullB_mem []       e  ()
nullB_mem (y ∷ ys) () m

------------------------------------------------------------------------
-- anyL

anyL_true : {A : Set} (p : A -> Bool) (xs : List A) -> anyL p xs ≡ true
         -> Σ[ x ∈ A ] x ∈ xs × p x ≡ true
anyL_true {A} p []       ()
anyL_true {A} p (y ∷ ys) e =
  sumElim (λ e1 -> y , here , e1)
          (λ e2 -> shift (anyL_true p ys e2))
          (orTrue (p y) (anyL p ys) e)
  where
    shift : (Σ[ x ∈ A ] x ∈ ys × p x ≡ true)
         -> Σ[ x ∈ A ] x ∈ y ∷ ys × p x ≡ true
    shift (x , m , q) = x , there m , q

anyL_intro : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
          -> x ∈ xs -> p x ≡ true -> anyL p xs ≡ true
anyL_intro p []       ()        e
anyL_intro p (y ∷ ys) here      e = orL (p y) (anyL p ys) e
anyL_intro p (y ∷ ys) (there m) e = orR (p y) (anyL p ys) (anyL_intro p ys m e)

anyL_false : {A : Set} (p : A -> Bool) (xs : List A) -> anyL p xs ≡ false
          -> {x : A} -> x ∈ xs -> p x ≡ false
anyL_false p []       e  ()
anyL_false p (y ∷ ys) e here      = orFalseL (p y) (anyL p ys) e
anyL_false p (y ∷ ys) e (there m) =
  anyL_false p ys (orFalseR (p y) (anyL p ys) e) m

------------------------------------------------------------------------
-- allB

allB_false : {A : Set} (p : A -> Bool) (xs : List A) -> allB p xs ≡ false
          -> Σ[ x ∈ A ] x ∈ xs × p x ≡ false
allB_false {A} p []       ()
allB_false {A} p (y ∷ ys) e =
  sumElim (λ e1 -> y , here , e1)
          (λ e2 -> shift (allB_false p ys e2))
          (andFalse (p y) (allB p ys) e)
  where
    shift : (Σ[ x ∈ A ] x ∈ ys × p x ≡ false)
         -> Σ[ x ∈ A ] x ∈ y ∷ ys × p x ≡ false
    shift (x , m , q) = x , there m , q

nullB_false : {A : Set} (xs : List A) -> nullB xs ≡ false
           -> Σ[ x ∈ A ] x ∈ xs
nullB_false []       ()
nullB_false (y ∷ ys) e = y , here

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

valEq_sound : (v w : Val) -> valEq v w ≡ true -> v ≡ w
valEq_sound []      []      e = refl
valEq_sound []      (c ∷ w) ()
valEq_sound (b ∷ v) []      ()
valEq_sound (b ∷ v) (c ∷ w) e =
  eqCons (boolEq_sound b c (andTrueL (b ⇔ᵇ c) (valEq v w) e))
         (valEq_sound v w (andTrueR (b ⇔ᵇ c) (valEq v w) e))

memB_sound : (v : Val) (us : List Val) -> memB v us ≡ true -> v ∈ us
memB_sound v []       ()
memB_sound v (u ∷ us) e =
  sumElim (λ e1 -> subst (λ z -> v ∈ z ∷ us) (valEq_sound v u e1) here)
          (λ e2 -> there (memB_sound v us e2))
          (orTrue (valEq v u) (anyL (valEq v) us) e)

memB_complete : (v : Val) (us : List Val) -> v ∈ us -> memB v us ≡ true
memB_complete v []       ()
memB_complete v (u ∷ us) here     =
  orL (valEq v v) (anyL (valEq v) us) (valEq_refl v)
memB_complete v (u ∷ us) (there m) =
  orR (valEq v u) (anyL (valEq v) us) (memB_complete v us m)

memB_false : (v : Val) (us : List Val) -> memB v us ≡ false -> v ∈ us -> Empty
memB_false v us e m = tfAbs (trans (sym (memB_complete v us m)) e)
