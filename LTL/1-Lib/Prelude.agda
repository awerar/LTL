{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.1-Lib.Prelude -- Boolean connectives and their lemmas, sums, Σ-types and
-- products, and lists with membership, inclusion and indexing: for each list
-- operation (++, map, filter, any, all, concatMap), membership in both
-- directions.
--
-- The notation is that of Agda's standard library.  The Boolean connectives
-- carry a superscript b (∧ᵇ, ∨ᵇ, ¬ᵇ, ⇒ᵇ, ⇔ᵇ) because the plain symbols are
-- the LTL connectives.  The list lemmas take the library's names too, where
-- ⁺ introduces and ⁻ eliminates: ∈-++⁺ˡ puts a member of xs into xs ++ ys,
-- ∈-++⁻ splits a member of xs ++ ys.

module LTL.1-Lib.Prelude where

open import LTL.1-Lib.Base public

------------------------------------------------------------------------
-- Boolean connectives
--
-- They bind looser than application and tighter than ≡, so
-- a ∧ᵇ ¬ᵇ b ≡ true  is  (a ∧ᵇ (¬ᵇ b)) ≡ true.  ¬ᵇ and ⇒ᵇ are LTL.Statement's
-- not and imp, the connectives of its (PC) side condition Tautology.

open import LTL.Statement public
  using () renaming (not to infix 10 ¬ᵇ_; imp to infixr 7 _⇒ᵇ_)

-- The implicit arguments the signatures below leave out.

private variable
  n m   : Nat
  A B C : Set
  x y   : A
  P     : A -> Set

infixr 9 _∧ᵇ_
infixr 8 _∨ᵇ_
infix  6 _⇔ᵇ_

_∧ᵇ_ : Bool -> Bool -> Bool
true  ∧ᵇ b = b
false ∧ᵇ b = false

_∨ᵇ_ : Bool -> Bool -> Bool
true  ∨ᵇ b = true
false ∨ᵇ b = b

_⇔ᵇ_ : Bool -> Bool -> Bool
true  ⇔ᵇ b = b
false ⇔ᵇ b = ¬ᵇ b

-- Inequality of Booleans, a test like ≡ⁿ (infix 4.5).
infix 4.5 _≢ᵇ_

_≢ᵇ_ : Bool -> Bool -> Bool
a ≢ᵇ b = ¬ᵇ (a ⇔ᵇ b)

------------------------------------------------------------------------
-- Natural numbers
--
-- Boolean-valued tests carry a superscript naming the type they compare (≡ⁿ on
-- Nat here, ≡ᵛ on nodes (LTL.1-Lib.DecEq), ≡ᶠ on formulas).  They are infix 4.5: tighter than
-- ≡, looser than ∷ and ++.

infix 4.5 _≡ⁿ_

_≡ⁿ_ : Nat -> Nat -> Bool
zero  ≡ⁿ zero  = true
zero  ≡ⁿ suc _ = false
suc _ ≡ⁿ zero  = false
suc n ≡ⁿ suc m = n ≡ⁿ m

≡ⁿ-refl : (n : Nat) -> n ≡ⁿ n ≡ true
≡ⁿ-refl zero    = refl
≡ⁿ-refl (suc n) = ≡ⁿ-refl n

≡ⁿ-sound : (n m : Nat) -> n ≡ⁿ m ≡ true -> n ≡ m
≡ⁿ-sound zero    zero    p = refl
≡ⁿ-sound zero    (suc m) ()
≡ⁿ-sound (suc n) zero    ()
≡ⁿ-sound (suc n) (suc m) p = cong suc (≡ⁿ-sound n m p)

suc-injective : suc n ≡ suc m -> n ≡ m
suc-injective refl = refl

+-identityʳ : (m : Nat) -> m + zero ≡ m
+-identityʳ zero    = refl
+-identityʳ (suc m) = cong suc (+-identityʳ m)

------------------------------------------------------------------------
-- Sums

infixr 1 _⊎_

data _⊎_ (A B : Set) : Set where
  inl : A -> A ⊎ B
  inr : B -> A ⊎ B

-- Case analysis on a sum:  [ f , g ] x  applies f to a left alternative
-- and g to a right one.  A lambda branch needs parentheses, since its body
-- would otherwise run on past the comma.

[_,_] : (A -> C) -> (B -> C) -> A ⊎ B -> C
[ f , g ] (inl a) = f a
[ f , g ] (inr b) = g b

-- Does a sum hold its left alternative?

isInl : A ⊎ B -> Bool
isInl (inl _) = true
isInl (inr _) = false

------------------------------------------------------------------------
-- Strict order on Nat, needed to index into sub P

infix 4 _<_

data _<_ : Nat -> Nat -> Set where
  z<s : {n : Nat}            -> zero < suc n
  s<s : {n m : Nat} -> n < m -> suc n < suc m

------------------------------------------------------------------------
-- Σ-types and products
--
-- Σ[ x ∈ A ] B  is  Σ A (λ x -> B): a witness x : A together with a proof
-- of B.  The ∈ there names a type, not list membership.  A × B is
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

fst : {B : A -> Set} -> Σ A B -> A
fst (a , b) = a

snd : {B : A -> Set} -> (p : Σ A B) -> B (fst p)
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

-- Conjunction over disjunction

∧ᵇ∨ᵇ-distribʳ : (a b c : Bool) -> (a ∨ᵇ b) ∧ᵇ c ≡ true
              -> a ∧ᵇ c ∨ᵇ b ∧ᵇ c ≡ true
∧ᵇ∨ᵇ-distribʳ true  b true  e = refl
∧ᵇ∨ᵇ-distribʳ true  b false ()
∧ᵇ∨ᵇ-distribʳ false b c     e = e

-- Distribution, forgetting the conjunct c on the left disjunct
∧ᵇ∨ᵇ-weaken : (a b c : Bool) -> (a ∨ᵇ b) ∧ᵇ c ≡ true -> a ∨ᵇ b ∧ᵇ c ≡ true
∧ᵇ∨ᵇ-weaken true  b c e = refl
∧ᵇ∨ᵇ-weaken false b c e = e

-- Negation

¬ᵇ-true : (b : Bool) -> ¬ᵇ b ≡ true -> b ≡ false
¬ᵇ-true true  ()
¬ᵇ-true false e = refl

¬ᵇ-false : (b : Bool) -> ¬ᵇ b ≡ false -> b ≡ true
¬ᵇ-false true  e = refl
¬ᵇ-false false ()

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

-- The axioms (P1)-(P3) of LTL.2-Syntax.Deriv are Boolean tautologies.

⇒ᵇ-P1 : (a b : Bool) -> a ⇒ᵇ b ⇒ᵇ a ≡ true
⇒ᵇ-P1 true  true  = refl
⇒ᵇ-P1 true  false = refl
⇒ᵇ-P1 false b     = refl

⇒ᵇ-P2 : (a b c : Bool) -> (a ⇒ᵇ b ⇒ᵇ c) ⇒ᵇ (a ⇒ᵇ b) ⇒ᵇ a ⇒ᵇ c ≡ true
⇒ᵇ-P2 true  true  true  = refl
⇒ᵇ-P2 true  true  false = refl
⇒ᵇ-P2 true  false true  = refl
⇒ᵇ-P2 true  false false = refl
⇒ᵇ-P2 false b     c     = refl

⇒ᵇ-P3 : (a b : Bool) -> (¬ᵇ b ⇒ᵇ ¬ᵇ a) ⇒ᵇ a ⇒ᵇ b ≡ true
⇒ᵇ-P3 true  true  = refl
⇒ᵇ-P3 true  false = refl
⇒ᵇ-P3 false true  = refl
⇒ᵇ-P3 false false = refl

-- The LTL abbreviations A ∨ B = ¬ A ⇒ B and A ∧ B = ¬ (A ⇒ ¬ B), read as
-- Booleans: how an evaluation that is ¬ᵇ at ¬ and ⇒ᵇ at ⇒ sees them.

¬ᵇ⇒ᵇ-introˡ : (a b : Bool) -> a ≡ true -> ¬ᵇ a ⇒ᵇ b ≡ true
¬ᵇ⇒ᵇ-introˡ true  b e = refl
¬ᵇ⇒ᵇ-introˡ false b ()

¬ᵇ⇒ᵇ¬ᵇ-intro : (a b : Bool) -> a ≡ true -> b ≡ true -> ¬ᵇ (a ⇒ᵇ ¬ᵇ b) ≡ true
¬ᵇ⇒ᵇ¬ᵇ-intro true  true  ea eb = refl
¬ᵇ⇒ᵇ¬ᵇ-intro true  false ea ()
¬ᵇ⇒ᵇ¬ᵇ-intro false b     () eb

¬ᵇ⇒ᵇ¬ᵇ-trueˡ : (a b : Bool) -> ¬ᵇ (a ⇒ᵇ ¬ᵇ b) ≡ true -> a ≡ true
¬ᵇ⇒ᵇ¬ᵇ-trueˡ true  b e = refl
¬ᵇ⇒ᵇ¬ᵇ-trueˡ false b ()

¬ᵇ⇒ᵇ¬ᵇ-trueʳ : (a b : Bool) -> ¬ᵇ (a ⇒ᵇ ¬ᵇ b) ≡ true -> b ≡ true
¬ᵇ⇒ᵇ¬ᵇ-trueʳ true  true  e = refl
¬ᵇ⇒ᵇ¬ᵇ-trueʳ true  false ()
¬ᵇ⇒ᵇ¬ᵇ-trueʳ false b     ()

-- Equivalence

⇔ᵇ-refl : (a : Bool) -> a ⇔ᵇ a ≡ true
⇔ᵇ-refl true  = refl
⇔ᵇ-refl false = refl

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

-- Agda.Builtin.List's, which is also the List of LTL.Statement (a Period there
-- is a List Instant); it declares _∷_ infixr 5 itself.

open import Agda.Builtin.List public using (List; []; _∷_)

private variable
  ys : List A

infixr 5 _++_

_++_ : List A -> List A -> List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

length : List A -> Nat
length []       = zero
length (x ∷ xs) = suc (length xs)

map : (A -> B) -> List A -> List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

-- filter branches with if rather than "with", so that proofs about it can
-- case on the test p x directly instead of reproducing a with-abstraction.

filter : (A -> Bool) -> List A -> List A
filter p []       = []
filter p (x ∷ xs) = if p x then (x ∷ filter p xs) else filter p xs

any : (A -> Bool) -> List A -> Bool
any p []       = false
any p (x ∷ xs) = p x ∨ᵇ any p xs

all : (A -> Bool) -> List A -> Bool
all p []       = true
all p (x ∷ xs) = p x ∧ᵇ all p xs

null : List A -> Bool
null []       = true
null (x ∷ xs) = false

concat : List (List A) -> List A
concat []         = []
concat (xs ∷ xss) = xs ++ concat xss

concatMap : (A -> List B) -> List A -> List B
concatMap f []       = []
concatMap f (x ∷ xs) = f x ++ concatMap f xs

++-identityʳ : (xs : List A) -> xs ++ [] ≡ xs
++-identityʳ []       = refl
++-identityʳ (x ∷ xs) = cong (λ zs -> x ∷ zs) (++-identityʳ xs)

------------------------------------------------------------------------
-- Membership

infix 4 _∈_ _∈ᵖ_ _∉ᵖ_

data _∈_ {A : Set} (x : A) : List A -> Set where
  here  : {xs : List A}                   -> x ∈ x ∷ xs
  there : {y : A} {xs : List A} -> x ∈ xs -> x ∈ y ∷ xs

-- Membership in a set given as a Boolean predicate (Subset in
-- LTL.1-Lib.Exhaustible): x ∈ᵖ E holds when E x is true.

_∈ᵖ_ : A -> (A -> Bool) -> Set
x ∈ᵖ E = E x ≡ true

_∉ᵖ_ : A -> (A -> Bool) -> Set
x ∉ᵖ E = E x ≡ false

-- Quantifiers bounded by a list.  ∀[ x ∈ xs ] B  is  (x : _) -> x ∈ xs -> B,
-- ∀ⁱ[ x ∈ xs ] B  is  {x : _} -> x ∈ xs -> B, for when x is read off the
-- membership proof, and  ∃[ x ∈ xs ] B  is  Σ[ x ∈ _ ] x ∈ xs × B; here ∈ is
-- list membership.  ∀[ x ∈ᵖ E ] B  is  (x : _) -> x ∈ᵖ E -> B, bounded by a
-- Boolean predicate; it has no implicit form, since E x ≡ true does not
-- determine x.  Arrows are parsed before notations, so the body of ∀ ends
-- at the first unparenthesised ->; when more hypotheses follow, write the
-- telescope out.

infix 2 ∀∈-syntax ∀ⁱ∈-syntax ∃∈-syntax ∀ᵖ-syntax

∀∈-syntax : List A -> (A -> Set) -> Set
∀∈-syntax xs B = (x : _) -> x ∈ xs -> B x

syntax ∀∈-syntax xs (λ x -> B) = ∀[ x ∈ xs ] B

∀ⁱ∈-syntax : List A -> (A -> Set) -> Set
∀ⁱ∈-syntax xs B = {x : _} -> x ∈ xs -> B x

syntax ∀ⁱ∈-syntax xs (λ x -> B) = ∀ⁱ[ x ∈ xs ] B

∃∈-syntax : List A -> (A -> Set) -> Set
∃∈-syntax xs B = Σ[ x ∈ _ ] x ∈ xs × B x

syntax ∃∈-syntax xs (λ x -> B) = ∃[ x ∈ xs ] B

∀ᵖ-syntax : (A -> Bool) -> (A -> Set) -> Set
∀ᵖ-syntax E B = (x : _) -> x ∈ᵖ E -> B x

syntax ∀ᵖ-syntax E (λ x -> B) = ∀[ x ∈ᵖ E ] B

-- A witness found in ys is a witness in y ∷ ys.

there-∃ : ∃[ x ∈ ys ] P x -> ∃[ x ∈ y ∷ ys ] P x
there-∃ (x , m , p) = x , there m , p

-- Inclusion of lists as sets, with the element explicit.

infix 4 _⊆_

_⊆_ : List A -> List A -> Set
xs ⊆ ys = ∀[ x ∈ xs ] x ∈ ys

∈-++⁺ˡ : (xs ys : List A) -> x ∈ xs -> x ∈ xs ++ ys
∈-++⁺ˡ []       ys ()
∈-++⁺ˡ (z ∷ xs) ys here      = here
∈-++⁺ˡ (z ∷ xs) ys (there h) = there (∈-++⁺ˡ xs ys h)

∈-++⁺ʳ : (xs ys : List A) -> x ∈ ys -> x ∈ xs ++ ys
∈-++⁺ʳ []       ys h = h
∈-++⁺ʳ (z ∷ xs) ys h = there (∈-++⁺ʳ xs ys h)

∈-filter⁺ : (p : A -> Bool) (xs : List A) {x : A}
         -> x ∈ xs -> x ∈ᵖ p -> x ∈ filter p xs
∈-filter⁺ p []       ()        e
∈-filter⁺ p (y ∷ ys) here      e = aux (p y) e
  where
    aux : (b : Bool) -> b ≡ true -> y ∈ (if b then (y ∷ filter p ys) else filter p ys)
    aux true  e = here
    aux false ()
∈-filter⁺ p (y ∷ ys) {x} (there m) e = aux (p y)
  where
    aux : (b : Bool) -> x ∈ (if b then (y ∷ filter p ys) else filter p ys)
    aux true  = there (∈-filter⁺ p ys m e)
    aux false = ∈-filter⁺ p ys m e

-- A member of filter p xs is a member of xs, and passes p.

∈-filter⁻ : (p : A -> Bool) (xs : List A)
         -> ∀ⁱ[ x ∈ filter p xs ] x ∈ xs
∈-filter⁻ p []       ()
∈-filter⁻ p (y ∷ ys) m =
  [ (λ e  -> subst (λ z -> z ∈ y ∷ ys) (sym e) here)
  , (λ m' -> there (∈-filter⁻ p ys m'))
  ] (aux (p y) m)
  where
    aux : (b : Bool) -> ∀ {x} -> x ∈ (if b then (y ∷ filter p ys) else filter p ys)
       -> x ≡ y ⊎ x ∈ filter p ys
    aux true  here      = inl refl
    aux true  (there m) = inr m
    aux false m         = inr m

filter-prop : (p : A -> Bool) (xs : List A)
           -> ∀[ x ∈ filter p xs ] x ∈ᵖ p
filter-prop p []       x ()
filter-prop p (y ∷ ys) x m = aux (p y) refl x m
  where
    aux : (b : Bool) -> p y ≡ b
       -> ∀[ z ∈ (if b then (y ∷ filter p ys) else filter p ys) ] z ∈ᵖ p
    aux true  e z here      = e
    aux true  e z (there m) = filter-prop p ys z m
    aux false e z m         = filter-prop p ys z m

∈-map⁺ : (f : A -> B) {xs : List A}
      -> ∀ⁱ[ x ∈ xs ] f x ∈ map f xs
∈-map⁺ f here      = here
∈-map⁺ f (there h) = there (∈-map⁺ f h)

∈-map⁻ : (f : A -> B) (xs : List A)
      -> ∀ⁱ[ y ∈ map f xs ] ∃[ x ∈ xs ] y ≡ f x
∈-map⁻ f []       ()
∈-map⁻ f (x ∷ xs) here      = x , here , refl
∈-map⁻ f (x ∷ xs) (there m) = there-∃ (∈-map⁻ f xs m)

map-id : (xs : List A) -> map (λ x -> x) xs ≡ xs
map-id []       = refl
map-id (x ∷ xs) = cong (λ zs -> x ∷ zs) (map-id xs)

∈-++⁻ : (xs ys : List A)
     -> x ∈ xs ++ ys -> x ∈ xs ⊎ x ∈ ys
∈-++⁻ []       ys h         = inr h
∈-++⁻ (z ∷ xs) ys here      = inl here
∈-++⁻ (z ∷ xs) ys (there h) =
  [ (λ k -> inl (there k)) , inr ] (∈-++⁻ xs ys h)

-- Building an inclusion by cons and by append.

∷-⊆ : {xs zs : List A} -> x ∈ zs -> xs ⊆ zs -> x ∷ xs ⊆ zs
∷-⊆ m h _ here      = m
∷-⊆ m h z (there k) = h z k

++-⊆ : (xs : List A) {zs : List A} -> xs ⊆ zs -> ys ⊆ zs -> xs ++ ys ⊆ zs
++-⊆ {ys = ys} xs h1 h2 z m = [ h1 z , h2 z ] (∈-++⁻ xs ys m)

-- Dropping the head of an included list, and the identity inclusion.

⊆-tail : {xs zs : List A} -> x ∷ xs ⊆ zs -> xs ⊆ zs
⊆-tail h z m = h z (there m)

⊆-refl : {xs : List A} -> xs ⊆ xs
⊆-refl z m = m

∈-concatMap⁺ : (f : A -> List B) {xs : List A} {x : A} {y : B}
            -> x ∈ xs -> y ∈ f x -> y ∈ concatMap f xs
∈-concatMap⁺ f {x ∷ xs} here      k = ∈-++⁺ˡ (f x) (concatMap f xs) k
∈-concatMap⁺ f {z ∷ xs} (there m) k =
  ∈-++⁺ʳ (f z) (concatMap f xs) (∈-concatMap⁺ f m k)

∈-concatMap⁻ : (f : A -> List B) (xs : List A)
            -> ∀ⁱ[ y ∈ concatMap f xs ] ∃[ x ∈ xs ] y ∈ f x
∈-concatMap⁻ f []       ()
∈-concatMap⁻ f (x ∷ xs) m =
  [ (λ k -> x , here , k) , (λ k -> there-∃ (∈-concatMap⁻ f xs k)) ]
    (∈-++⁻ (f x) (concatMap f xs) m)

------------------------------------------------------------------------
-- Indexing.  nth xs i d is the i-th member of xs, or d out of range.

nth : List A -> Nat -> A -> A
nth []       n       d = d
nth (x ∷ xs) zero    d = x
nth (x ∷ xs) (suc n) d = nth xs n d

map-length : (f : A -> B) (xs : List A)
          -> length (map f xs) ≡ length xs
map-length f []       = refl
map-length f (x ∷ xs) = cong suc (map-length f xs)

------------------------------------------------------------------------
-- any and all against membership

any-true : (p : A -> Bool) (xs : List A) -> any p xs ≡ true
        -> ∃[ x ∈ xs ] x ∈ᵖ p
any-true p []       ()
any-true p (y ∷ ys) e =
  [ (λ e1 -> y , here , e1) , (λ e2 -> there-∃ (any-true p ys e2)) ]
    (∨ᵇ-true (p y) (any p ys) e)

any-intro : (p : A -> Bool) (xs : List A) {x : A}
         -> x ∈ xs -> x ∈ᵖ p -> any p xs ≡ true
any-intro p []       ()        e
any-intro p (y ∷ ys) here      e = ∨ᵇ-introˡ (p y) (any p ys) e
any-intro p (y ∷ ys) (there m) e =
  ∨ᵇ-introʳ (p y) (any p ys) (any-intro p ys m e)

any-false : (p : A -> Bool) (xs : List A) -> any p xs ≡ false
         -> ∀ⁱ[ x ∈ xs ] x ∉ᵖ p
any-false p []       e  ()
any-false p (y ∷ ys) e here      = ∨ᵇ-falseˡ (p y) (any p ys) e
any-false p (y ∷ ys) e (there m) =
  any-false p ys (∨ᵇ-falseʳ (p y) (any p ys) e) m

all-true : (p : A -> Bool) (xs : List A)
        -> all p xs ≡ true -> ∀[ x ∈ xs ] x ∈ᵖ p
all-true p []       e x ()
all-true p (y ∷ ys) e x here      = ∧ᵇ-trueˡ (p y) (all p ys) e
all-true p (y ∷ ys) e x (there m) = all-true p ys (∧ᵇ-trueʳ (p y) (all p ys) e) x m

all-false-intro : (p : A -> Bool) (xs : List A)
               -> ∃[ x ∈ xs ] x ∉ᵖ p -> all p xs ≡ false
all-false-intro p []       (x , ()      , e)
all-false-intro p (y ∷ ys) (x , here    , e) = cong (λ c -> c ∧ᵇ all p ys) e
all-false-intro p (y ∷ ys) (x , there m , e) =
  ∧ᵇ-false-introʳ (p y) (all p ys) (all-false-intro p ys (x , m , e))

all-false : (p : A -> Bool) (xs : List A) -> all p xs ≡ false
         -> ∃[ x ∈ xs ] x ∉ᵖ p
all-false p []       ()
all-false p (y ∷ ys) e =
  [ (λ e1 -> y , here , e1) , (λ e2 -> there-∃ (all-false p ys e2)) ]
    (∧ᵇ-false (p y) (all p ys) e)

all-intro : (p : A -> Bool) (xs : List A)
         -> (∀[ x ∈ xs ] x ∈ᵖ p) -> all p xs ≡ true
all-intro p []       f = refl
all-intro p (y ∷ ys) f =
  ∧ᵇ-intro (p y) (all p ys) (f y here) (all-intro p ys (λ x m -> f x (there m)))
