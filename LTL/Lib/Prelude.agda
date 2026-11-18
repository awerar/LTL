{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Lib.Prelude -- the small amount of infrastructure beyond LTL.Lib.Base that the
-- development needs: boolean connectives and their lemmas,
-- soundness/reflexivity of ≡ⁿ, sums, Σ-types and products, lists with
-- membership, and the index/nth round-trip of FORMALISATION-PLAN.md G2.
--
-- The notation is that of Agda's standard library: A ⊎ B, Σ[ x ∈ A ] B,
-- A × B (with pairs  a , b), x ∷ xs, xs ++ ys, x ∈ xs (constructors here and
-- there), m < n.  The boolean connectives carry a superscript b (∧ᵇ, ∨ᵇ, ¬ᵇ,
-- ⇒ᵇ, ⇔ᵇ), because the plain symbols are the LTL connectives of LTL.Syntax.Formula.

module LTL.Lib.Prelude where

open import LTL.Lib.Base public

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

+-identityʳ : (m : Nat) -> m + zero ≡ m
+-identityʳ zero    = refl
+-identityʳ (suc m) = cong suc (+-identityʳ m)

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
-- left, so LTL.Procedures.Decide calls this isProof.)

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
-- Boolean lemmas
--
-- Named after the connective they are about, in the hyphen style of the
-- standard library: ∧ᵇ-trueˡ reads the left conjunct off a true conjunction,
-- ∨ᵇ-introʳ proves a disjunction from its right disjunct, ⇒ᵇ-mp is modus ponens
-- for ⇒ᵇ.  A -false lemma reads a connective that is false; a -cancel lemma
-- uses one known argument to get the other.

true≢false : true ≡ false -> Empty
true≢false ()

-- A Boolean that cannot be true is false.
refuteTrue : (b : Bool) -> (b ≡ true -> Empty) -> b ≡ false
refuteTrue true  no = emptyElim (no refl)
refuteTrue false no = refl

-- Conjunction

∧ᵇ-trueˡ : (a b : Bool) -> a ∧ᵇ b ≡ true -> a ≡ true
∧ᵇ-trueˡ true  b p = refl
∧ᵇ-trueˡ false b ()

∧ᵇ-trueʳ : (a b : Bool) -> a ∧ᵇ b ≡ true -> b ≡ true
∧ᵇ-trueʳ true  b p = p
∧ᵇ-trueʳ false b ()

∧ᵇ-split : (a b : Bool) -> a ∧ᵇ b ≡ true -> a ≡ true × b ≡ true
∧ᵇ-split true  b p = refl , p
∧ᵇ-split false b ()

∧ᵇ-intro : (a b : Bool) -> a ≡ true -> b ≡ true -> a ∧ᵇ b ≡ true
∧ᵇ-intro true  b p q = q
∧ᵇ-intro false b () q

∧ᵇ-false : (a b : Bool) -> a ∧ᵇ b ≡ false -> a ≡ false ⊎ b ≡ false
∧ᵇ-false true  b e = inr e
∧ᵇ-false false b e = inl refl

-- a ∧ᵇ b is false when b is
∧ᵇ-false-introʳ : (a b : Bool) -> b ≡ false -> a ∧ᵇ b ≡ false
∧ᵇ-false-introʳ true  b eb = eb
∧ᵇ-false-introʳ false b eb = refl

-- a ∧ᵇ b is false and a is true, so b is false
∧ᵇ-false-cancelˡ : (a b : Bool) -> a ∧ᵇ b ≡ false -> a ≡ true -> b ≡ false
∧ᵇ-false-cancelˡ true  b eab ea = eab
∧ᵇ-false-cancelˡ false b eab ()

-- ¬ᵇ (a ∧ᵇ b) is true and a is true, so b is false
¬ᵇ∧ᵇ-cancelˡ : (a b : Bool) -> ¬ᵇ (a ∧ᵇ b) ≡ true -> a ≡ true -> b ≡ false
¬ᵇ∧ᵇ-cancelˡ true  true  () e
¬ᵇ∧ᵇ-cancelˡ true  false q  e = refl
¬ᵇ∧ᵇ-cancelˡ false b     q  ()

-- De Morgan, in the direction the searches use
¬ᵇ-∧ᵇ : (a b : Bool) -> ¬ᵇ (a ∧ᵇ b) ≡ true -> ¬ᵇ a ∨ᵇ ¬ᵇ b ≡ true
¬ᵇ-∧ᵇ true  true  ()
¬ᵇ-∧ᵇ true  false e = refl
¬ᵇ-∧ᵇ false b     e = refl

-- Disjunction

∨ᵇ-true : (a b : Bool) -> a ∨ᵇ b ≡ true -> a ≡ true ⊎ b ≡ true
∨ᵇ-true true  b e = inl refl
∨ᵇ-true false b e = inr e

∨ᵇ-introˡ : (a b : Bool) -> a ≡ true -> a ∨ᵇ b ≡ true
∨ᵇ-introˡ true  b e  = refl
∨ᵇ-introˡ false b ()

∨ᵇ-introʳ : (a b : Bool) -> b ≡ true -> a ∨ᵇ b ≡ true
∨ᵇ-introʳ true  b e = refl
∨ᵇ-introʳ false b e = e

∨ᵇ-falseˡ : (a b : Bool) -> a ∨ᵇ b ≡ false -> a ≡ false
∨ᵇ-falseˡ true  b ()
∨ᵇ-falseˡ false b e = refl

∨ᵇ-falseʳ : (a b : Bool) -> a ∨ᵇ b ≡ false -> b ≡ false
∨ᵇ-falseʳ true  b ()
∨ᵇ-falseʳ false b e = e

∨ᵇ-false-intro : (a b : Bool) -> a ≡ false -> b ≡ false -> a ∨ᵇ b ≡ false
∨ᵇ-false-intro a b ea eb = trans (cong (λ c -> c ∨ᵇ b) ea) eb

-- Negation

¬ᵇ-true : (b : Bool) -> ¬ᵇ b ≡ true -> b ≡ false
¬ᵇ-true true  ()
¬ᵇ-true false e = refl

¬ᵇ-false : (b : Bool) -> ¬ᵇ b ≡ false -> b ≡ true
¬ᵇ-false true  e = refl
¬ᵇ-false false ()

¬ᵇ-involutive : (b : Bool) -> ¬ᵇ ¬ᵇ b ≡ b
¬ᵇ-involutive true  = refl
¬ᵇ-involutive false = refl

¬ᵇ¬ᵇ-true : (x : Bool) -> ¬ᵇ ¬ᵇ x ≡ true -> x ≡ true
¬ᵇ¬ᵇ-true true  e = refl
¬ᵇ¬ᵇ-true false ()

¬ᵇ-clash : (x : Bool) -> x ≡ true -> ¬ᵇ x ≡ true -> Empty
¬ᵇ-clash true  ex ()
¬ᵇ-clash false () en

-- Implication

⇒ᵇ-refl : (b : Bool) -> b ⇒ᵇ b ≡ true
⇒ᵇ-refl true  = refl
⇒ᵇ-refl false = refl

⇒ᵇ-mp : (a b : Bool) -> a ⇒ᵇ b ≡ true -> a ≡ true -> b ≡ true
⇒ᵇ-mp true  b e q  = e
⇒ᵇ-mp false b e ()

⇒ᵇ-intro : (a b : Bool) -> (a ≡ true -> b ≡ true) -> a ⇒ᵇ b ≡ true
⇒ᵇ-intro true  b f = f refl
⇒ᵇ-intro false b f = refl

⇒ᵇ-const : (x y : Bool) -> y ≡ true -> x ⇒ᵇ y ≡ true
⇒ᵇ-const true  y e = e
⇒ᵇ-const false y e = refl

⇒ᵇ-false : (a b : Bool) -> a ⇒ᵇ b ≡ false -> a ≡ true × b ≡ false
⇒ᵇ-false true  true  ()
⇒ᵇ-false true  false e = refl , refl
⇒ᵇ-false false b     ()

⇒ᵇ-contra : (x y : Bool) -> (y ≡ true -> x ≡ true) -> ¬ᵇ x ⇒ᵇ ¬ᵇ y ≡ true
⇒ᵇ-contra true  y     h = refl
⇒ᵇ-contra false true  h = emptyElim (true≢false (sym (h refl)))
⇒ᵇ-contra false false h = refl

-- Equivalence

⇔ᵇ-refl : (b : Bool) -> b ⇔ᵇ b ≡ true
⇔ᵇ-refl true  = refl
⇔ᵇ-refl false = refl

⇔ᵇ-complete : (x y : Bool) -> x ≡ y -> x ⇔ᵇ y ≡ true
⇔ᵇ-complete x y refl = ⇔ᵇ-refl x

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

------------------------------------------------------------------------
-- Lists

-- Agda.Builtin.List's, which is also the List of LTL.Trusted (a Period there
-- is a List Instant); it declares _∷_ infixr 5 itself.

open import Agda.Builtin.List public using (List; []; _∷_)

infixr 5 _++_

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

-- A witness found in ys is a witness in y ∷ ys.

there-Σ : {A : Set} {P : A -> Set} {y : A} {ys : List A}
       -> Σ[ x ∈ A ] x ∈ ys × P x -> Σ[ x ∈ A ] x ∈ y ∷ ys × P x
there-Σ (x , m , p) = x , there m , p

-- Inclusion of lists as sets.  The element is explicit, as in the lemmas that
-- use it (LTL.Elimination.Extract).

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

map-length : {A B : Set} (f : A -> B) (xs : List A)
          -> length (map f xs) ≡ length xs
map-length f []       = refl
map-length f (x ∷ xs) = cong suc (map-length f xs)

nth-map : {A B : Set} (f : A -> B) (xs : List A) (i : Nat) -> i < length xs
       -> (d : A) (e : B) -> nth (map f xs) i e ≡ f (nth xs i d)
nth-map f []       i       ()        d e
nth-map f (x ∷ xs) zero    lt        d e = refl
nth-map f (x ∷ xs) (suc i) (ltSuc l) d e = nth-map f xs i l d e

ltSucCase : (i n : Nat) -> i < suc n -> i ≡ n ⊎ i < n
ltSucCase zero    zero     lt        = inl refl
ltSucCase zero    (suc n)  lt        = inr ltZero
ltSucCase (suc j) zero     (ltSuc ())
ltSucCase (suc j) (suc n)  (ltSuc l) =
  sumElim (λ e -> inl (cong suc e)) (λ l' -> inr (ltSuc l')) (ltSucCase j n l)

------------------------------------------------------------------------
-- Conjunction over a list.

all : {A : Set} -> (A -> Bool) -> List A -> Bool
all p []       = true
all p (x ∷ xs) = p x ∧ᵇ all p xs

all-at : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
      -> x ∈ xs -> all p xs ≡ true -> p x ≡ true
all-at p []       ()        e
all-at p (y ∷ ys) here      e = ∧ᵇ-trueˡ (p y) (all p ys) e
all-at p (y ∷ ys) (there m) e = all-at p ys m (∧ᵇ-trueʳ (p y) (all p ys) e)

all-atFalse : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
           -> x ∈ xs -> p x ≡ false -> all p xs ≡ false
all-atFalse p []       ()        e
all-atFalse p (y ∷ ys) here      e = cong (λ c -> c ∧ᵇ all p ys) e
all-atFalse p (y ∷ ys) (there m) e =
  ∧ᵇ-false-introʳ (p y) (all p ys) (all-atFalse p ys m e)

all-false : {A : Set} (p : A -> Bool) (xs : List A) -> all p xs ≡ false
         -> Σ[ x ∈ A ] x ∈ xs × p x ≡ false
all-false p []       ()
all-false p (y ∷ ys) e =
  sumElim (λ e1 -> y , here , e1)
          (λ e2 -> there-Σ (all-false p ys e2))
          (∧ᵇ-false (p y) (all p ys) e)

all-intro : {A : Set} (p : A -> Bool) (xs : List A)
         -> ({x : A} -> x ∈ xs -> p x ≡ true) -> all p xs ≡ true
all-intro p []       f = refl
all-intro p (y ∷ ys) f =
  ∧ᵇ-intro (p y) (all p ys) (f here) (all-intro p ys (λ m -> f (there m)))
