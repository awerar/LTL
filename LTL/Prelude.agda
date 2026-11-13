{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Prelude -- the small amount of infrastructure beyond LTL.Base that the
-- development needs: boolean connectives with their elimination lemmas,
-- soundness/reflexivity of ≡ⁿ, sums, Σ-types and products, lists with
-- membership, and the index/nth round-trip of FORMALISATION-PLAN.md G2.
--
-- The notation is that of Agda's standard library: A ⊎ B, Σ[ x ∈ A ] B,
-- A × B (with pairs  a , b), x ∷ xs, xs ++ ys, x ∈ xs (constructors here and
-- there), m < n.  The boolean connectives carry a superscript b (∧ᵇ, ∨ᵇ, ¬ᵇ,
-- ⇒ᵇ, ⇔ᵇ), because the plain symbols are the LTL connectives of LTL.Formula.

module LTL.Prelude where

open import LTL.Base public

------------------------------------------------------------------------
-- Boolean connectives
--
-- They bind looser than application and tighter than ≡, so
-- a ∧ᵇ ¬ᵇ b ≡ true  is  (a ∧ᵇ (¬ᵇ b)) ≡ true.

infix  10 ¬ᵇ_
infixr 9 _∧ᵇ_
infixr 8 _∨ᵇ_
infixr 7 _⇒ᵇ_
infix  6 _⇔ᵇ_

_∧ᵇ_ : Bool -> Bool -> Bool
true  ∧ᵇ b = b
false ∧ᵇ b = false

andTrueL : (a b : Bool) -> a ∧ᵇ b ≡ true -> a ≡ true
andTrueL true  b p = refl
andTrueL false b ()

andTrueR : (a b : Bool) -> a ∧ᵇ b ≡ true -> b ≡ true
andTrueR true  b p = p
andTrueR false b ()

andIntro : (a b : Bool) -> a ≡ true -> b ≡ true -> a ∧ᵇ b ≡ true
andIntro true  b p q = q
andIntro false b () q

¬ᵇ_ : Bool -> Bool
¬ᵇ true  = false
¬ᵇ false = true

_⇒ᵇ_ : Bool -> Bool -> Bool
true  ⇒ᵇ b = b
false ⇒ᵇ b = true

_∨ᵇ_ : Bool -> Bool -> Bool
true  ∨ᵇ b = true
false ∨ᵇ b = b

_⇔ᵇ_ : Bool -> Bool -> Bool
true  ⇔ᵇ b = b
false ⇔ᵇ b = ¬ᵇ b

------------------------------------------------------------------------
-- ≡ⁿ

≡ⁿ-refl : (n : Nat) -> n ≡ⁿ n ≡ true
≡ⁿ-refl zero    = refl
≡ⁿ-refl (suc n) = ≡ⁿ-refl n

≡ⁿ-sound : (n m : Nat) -> n ≡ⁿ m ≡ true -> n ≡ m
≡ⁿ-sound zero    zero    p = refl
≡ⁿ-sound zero    (suc m) ()
≡ⁿ-sound (suc n) zero    ()
≡ⁿ-sound (suc n) (suc m) p = cong suc (≡ⁿ-sound n m p)

sucInj : {n m : Nat} -> suc n ≡ suc m -> n ≡ m
sucInj refl = refl

------------------------------------------------------------------------
-- Sums

infixr 1 _⊎_

data _⊎_ (A B : Set) : Set where
  inl : A -> A ⊎ B
  inr : B -> A ⊎ B

sumElim : {A B C : Set} -> (A -> C) -> (B -> C) -> A ⊎ B -> C
sumElim f g (inl a) = f a
sumElim f g (inr b) = g b

-- Does a sum hold its left alternative?  (decide's results are proofs on the
-- left, so LTL.Decide calls this isProof.)

isInl : {A B : Set} -> A ⊎ B -> Bool
isInl (inl _) = true
isInl (inr _) = false

------------------------------------------------------------------------
-- Strict order on Nat, needed to index into sub P

infix 4 _<_

data _<_ : Nat -> Nat -> Set where
  ltZero : {n : Nat}             -> zero < suc n
  ltSuc  : {n m : Nat} -> n < m  -> suc n < suc m

-- Two facts about <

ltNSucN : (n : Nat) -> n < suc n
ltNSucN zero    = ltZero
ltNSucN (suc n) = ltSuc (ltNSucN n)

ltWeak : {i n : Nat} -> i < n -> i < suc n
ltWeak ltZero    = ltZero
ltWeak (ltSuc l) = ltSuc (ltWeak l)

------------------------------------------------------------------------
-- Σ-types and products
--
-- Σ[ x ∈ A ] B  is  Σ A (λ x -> B): a witness x : A together with a proof
-- of B.  The ∈ there is part of the notation, not list membership.  A × B is
-- the non-dependent case, so one pair constructor  _,_  serves both.  Σ is a
-- data type rather than a record, so there is no eta rule for pairs.

infixr 4 _,_
infixr 2 _×_
infix  2 Σ-syntax

data Σ (A : Set) (B : A -> Set) : Set where
  _,_ : (x : A) -> B x -> Σ A B

Σ-syntax : (A : Set) -> (A -> Set) -> Set
Σ-syntax = Σ

syntax Σ-syntax A (λ x -> B) = Σ[ x ∈ A ] B

_×_ : Set -> Set -> Set
A × B = Σ A (λ _ -> B)

fst : {A : Set} {B : A -> Set} -> Σ A B -> A
fst (a , b) = a

snd : {A : Set} {B : A -> Set} -> (p : Σ A B) -> B (fst p)
snd (a , b) = b

------------------------------------------------------------------------
-- Reading a false boolean backwards

andFalse : (a b : Bool) -> a ∧ᵇ b ≡ false -> a ≡ false ⊎ b ≡ false
andFalse true  b e = inr e
andFalse false b e = inl refl

-- ¬ᵇ (a ∧ᵇ b) is true and a is true, so b is false
nandTrueL : (a b : Bool) -> ¬ᵇ (a ∧ᵇ b) ≡ true -> a ≡ true -> b ≡ false
nandTrueL true  true  () e
nandTrueL true  false q  e = refl
nandTrueL false b     q  ()

-- a ∧ᵇ b is false when b is
andFalseIntroR : (a b : Bool) -> b ≡ false -> a ∧ᵇ b ≡ false
andFalseIntroR true  b eb = eb
andFalseIntroR false b eb = refl

-- a ∧ᵇ b is false and a is true, so b is false
andFalseTrueL : (a b : Bool) -> a ∧ᵇ b ≡ false -> a ≡ true -> b ≡ false
andFalseTrueL true  b eab ea = eab
andFalseTrueL false b eab ()

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

¬ᵇ-involutive : (b : Bool) -> ¬ᵇ ¬ᵇ b ≡ b
¬ᵇ-involutive true  = refl
¬ᵇ-involutive false = refl

⇔ᵇ-sound : (a b : Bool) -> a ⇔ᵇ b ≡ true -> a ≡ b
⇔ᵇ-sound true  true  e = refl
⇔ᵇ-sound true  false ()
⇔ᵇ-sound false true  ()
⇔ᵇ-sound false false e = refl

⇔ᵇ-false : (a b : Bool) -> a ⇔ᵇ b ≡ false -> a ≡ ¬ᵇ b
⇔ᵇ-false true  true  ()
⇔ᵇ-false true  false e = refl
⇔ᵇ-false false true  e = refl
⇔ᵇ-false false false ()

⇒ᵇ-false : (a b : Bool) -> a ⇒ᵇ b ≡ false -> a ≡ true × b ≡ false
⇒ᵇ-false true  true  ()
⇒ᵇ-false true  false e = refl , refl
⇒ᵇ-false false b     ()

------------------------------------------------------------------------
-- Disjunction, read in both directions.
--
-- These four sat in LTL.Sets until LTL.Skel needed them: the tautology test of
-- (PC) is below Deriv, and Sets was then far above it.

orTrue : (a b : Bool) -> a ∨ᵇ b ≡ true -> a ≡ true ⊎ b ≡ true
orTrue true  b e = inl refl
orTrue false b e = inr e

orL : (a b : Bool) -> a ≡ true -> a ∨ᵇ b ≡ true
orL true  b e  = refl
orL false b ()

orR : (a b : Bool) -> b ≡ true -> a ∨ᵇ b ≡ true
orR true  b e = refl
orR false b e = e

true≢false : true ≡ false -> Empty
true≢false ()

------------------------------------------------------------------------
-- Lists

infixr 5 _∷_ _++_

data List (A : Set) : Set where
  []  : List A
  _∷_ : A -> List A -> List A

_++_ : {A : Set} -> List A -> List A -> List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

length : {A : Set} -> List A -> Nat
length []       = zero
length (x ∷ xs) = suc (length xs)

map : {A B : Set} -> (A -> B) -> List A -> List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

-- filterCons takes the boolean as an explicit argument rather than using
-- "with", so that later proofs can case on it directly instead of having to
-- reproduce a with-abstraction.

filterCons : {A : Set} -> Bool -> A -> List A -> List A
filterCons true  x ys = x ∷ ys
filterCons false x ys = ys

filter : {A : Set} -> (A -> Bool) -> List A -> List A
filter p []       = []
filter p (x ∷ xs) = filterCons (p x) x (filter p xs)

any : {A : Set} -> (A -> Bool) -> List A -> Bool
any p []       = false
any p (x ∷ xs) = p x ∨ᵇ any p xs

null : {A : Set} -> List A -> Bool
null []       = true
null (x ∷ xs) = false

concat : {A : Set} -> List (List A) -> List A
concat []         = []
concat (xs ∷ xss) = xs ++ concat xss

++-identityʳ : {A : Set} (xs : List A) -> xs ++ [] ≡ xs
++-identityʳ []       = refl
++-identityʳ (x ∷ xs) = cong (λ zs -> x ∷ zs) (++-identityʳ xs)

------------------------------------------------------------------------
-- Membership

infix 4 _∈_

data _∈_ {A : Set} (x : A) : List A -> Set where
  here  : {xs : List A}              -> x ∈ x ∷ xs
  there : {y : A} {xs : List A} -> x ∈ xs -> x ∈ y ∷ xs

-- Inclusion of lists as sets.  The element is explicit, as in the lemmas that
-- use it (LTL.Extract).

infix 4 _⊆_

_⊆_ : {A : Set} -> List A -> List A -> Set
xs ⊆ ys = (x : _) -> x ∈ xs -> x ∈ ys

memAppL : {A : Set} {x : A} (xs ys : List A) -> x ∈ xs -> x ∈ xs ++ ys
memAppL []       ys ()
memAppL (z ∷ xs) ys here      = here
memAppL (z ∷ xs) ys (there h) = there (memAppL xs ys h)

memAppR : {A : Set} {x : A} (xs ys : List A) -> x ∈ ys -> x ∈ xs ++ ys
memAppR []       ys h = h
memAppR (z ∷ xs) ys h = there (memAppR xs ys h)

filterCons-mem : {A : Set} {x : A} (b : Bool) (y : A) (ys : List A)
              -> x ∈ ys -> x ∈ filterCons b y ys
filterCons-mem true  y ys h = there h
filterCons-mem false y ys h = h

filterCons-hd : {A : Set} (b : Bool) (y : A) (ys : List A)
             -> b ≡ true -> y ∈ filterCons b y ys
filterCons-hd true  y ys e = here
filterCons-hd false y ys ()

filter-true : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
           -> x ∈ xs -> p x ≡ true -> x ∈ filter p xs
filter-true p []       ()        e
filter-true p (y ∷ ys) here      e = filterCons-hd (p y) y (filter p ys) e
filter-true p (y ∷ ys) (there m) e =
  filterCons-mem (p y) y (filter p ys) (filter-true p ys m e)

memMap : {A B : Set} (f : A -> B) {x : A} {xs : List A}
      -> x ∈ xs -> f x ∈ map f xs
memMap f here      = here
memMap f (there h) = there (memMap f h)

map-append : {A B : Set} (f : A -> B) (xs ys : List A)
          -> map f (xs ++ ys) ≡ map f xs ++ map f ys
map-append f []       ys = refl
map-append f (x ∷ xs) ys = cong (λ zs -> f x ∷ zs) (map-append f xs ys)

map-map : {A B C : Set} (f : B -> C) (g : A -> B) (xs : List A)
       -> map f (map g xs) ≡ map (λ x -> f (g x)) xs
map-map f g []       = refl
map-map f g (x ∷ xs) = cong (λ zs -> f (g x) ∷ zs) (map-map f g xs)

memAppCase : {A : Set} {x : A} (xs ys : List A)
          -> x ∈ xs ++ ys -> x ∈ xs ⊎ x ∈ ys
memAppCase []       ys h         = inr h
memAppCase (z ∷ xs) ys here      = inl here
memAppCase (z ∷ xs) ys (there h) =
  sumElim (λ k -> inl (there k)) (λ k -> inr k) (memAppCase xs ys h)

------------------------------------------------------------------------
-- The index / nth round-trip.
--
-- Every projection of a conjunct out of  chi v  goes through this pair, so it
-- is proved once, here, in both directions.

index : {A : Set} {x : A} {xs : List A} -> x ∈ xs -> Nat
index here      = zero
index (there h) = suc (index h)

nth : {A : Set} -> List A -> Nat -> A -> A
nth []       n       d = d
nth (x ∷ xs) zero    d = x
nth (x ∷ xs) (suc n) d = nth xs n d

index-nth : {A : Set} {x : A} {xs : List A} (h : x ∈ xs) (d : A)
         -> nth xs (index h) d ≡ x
index-nth here      d = refl
index-nth (there h) d = index-nth h d

index-length : {A : Set} {x : A} {xs : List A} (h : x ∈ xs)
            -> index h < length xs
index-length here      = ltZero
index-length (there h) = ltSuc (index-length h)

nth-mem : {A : Set} (xs : List A) (i : Nat) -> i < length xs -> (d : A)
       -> nth xs i d ∈ xs
nth-mem []       i       ()        d
nth-mem (x ∷ xs) zero    lt        d = here
nth-mem (x ∷ xs) (suc i) (ltSuc l) d = there (nth-mem xs i l d)

ltSucCase : (i n : Nat) -> i < suc n -> i ≡ n ⊎ i < n
ltSucCase zero    zero     lt        = inl refl
ltSucCase zero    (suc n)  lt        = inr ltZero
ltSucCase (suc j) zero     (ltSuc ())
ltSucCase (suc j) (suc n)  (ltSuc l) =
  sumElim (λ e -> inl (cong suc e)) (λ l' -> inr (ltSuc l')) (ltSucCase j n l)

------------------------------------------------------------------------
-- Conjunction over a list.  It sat in LTL.Skel; LTL.Sets needs it and imports
-- only the prelude.

all : {A : Set} -> (A -> Bool) -> List A -> Bool
all p []       = true
all p (x ∷ xs) = p x ∧ᵇ all p xs

all-at : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
      -> x ∈ xs -> all p xs ≡ true -> p x ≡ true
all-at p []       ()        e
all-at p (y ∷ ys) here      e = andTrueL (p y) (all p ys) e
all-at p (y ∷ ys) (there m) e = all-at p ys m (andTrueR (p y) (all p ys) e)

all-atFalse : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
           -> x ∈ xs -> p x ≡ false -> all p xs ≡ false
all-atFalse p []       ()        e
all-atFalse p (y ∷ ys) here      e = cong (λ c -> c ∧ᵇ all p ys) e
all-atFalse p (y ∷ ys) (there m) e =
  andFalseIntroR (p y) (all p ys) (all-atFalse p ys m e)

all-intro : {A : Set} (p : A -> Bool) (xs : List A)
         -> ({x : A} -> x ∈ xs -> p x ≡ true) -> all p xs ≡ true
all-intro p []       f = refl
all-intro p (y ∷ ys) f =
  andIntro (p y) (all p ys) (f here) (all-intro p ys (λ m -> f (there m)))
