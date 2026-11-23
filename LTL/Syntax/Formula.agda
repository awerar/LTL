{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Syntax.Formula -- formulas: variables (var n), negation ¬, implication
-- ⇒, next ○ and always □, with ∧, ∨, ⇔, ◇, ⊤ and ⊥ as abbreviations.
-- Implication is ⇒ because Agda reserves →.
--
-- Also decidable equality ≡ᶠ, proved sound and complete once here; isState
-- and lookup by formula rely on it.  And the subformula list sub P, with its
-- membership lemmas (sub-self, sub-¬, sub-⇒L, ...).

module LTL.Syntax.Formula where

open import LTL.Lib.Prelude public

------------------------------------------------------------------------
-- Formulas
--
-- The datatype is LTL.Statement's, so the procedure runs on exactly the formulas
-- the trusted statement talks about.  Its constructors are re-exported with
-- this development's fixities: the prefix operators bind tightest, then ∧, ∨,
-- ⇒ and ⇔, so  □ A ⇒ A ∧ ○ □ A  is  (□ A) ⇒ (A ∧ (○ (□ A))).

open import LTL.Statement public
  using (Formula; var)
  renaming (¬_ to infix 30 ¬_; _⇒_ to infixr 20 _⇒_;
            ○_ to infix 30 ○_; □_ to infix 30 □_)

infix  30 ◇_
infixr 22 _∧_
infixr 21 _∨_
infix  19 _⇔_

------------------------------------------------------------------------
-- Abbreviations

⊤ : Formula
⊤ = var zero ⇒ var zero

⊥ : Formula
⊥ = ¬ ⊤

_∨_ : Formula -> Formula -> Formula
A ∨ B = ¬ A ⇒ B

_∧_ : Formula -> Formula -> Formula
A ∧ B = ¬ (A ⇒ ¬ B)

_⇔_ : Formula -> Formula -> Formula
A ⇔ B = (A ⇒ B) ∧ (B ⇒ A)

◇_ : Formula -> Formula
◇ A = ¬ □ ¬ A

------------------------------------------------------------------------
-- Decidable equality.  All twenty-five cases are written out: --exact-split
-- rejects a catch-all clause overlapping the diagonal ones.

infix 4.5 _≡ᶠ_

_≡ᶠ_ : Formula -> Formula -> Bool
var n    ≡ᶠ var m   = n ≡ⁿ m
var n    ≡ᶠ ¬ B     = false
var n    ≡ᶠ (B ⇒ C) = false
var n    ≡ᶠ ○ B     = false
var n    ≡ᶠ □ B     = false

¬ A      ≡ᶠ var m   = false
¬ A      ≡ᶠ ¬ B     = A ≡ᶠ B
¬ A      ≡ᶠ (B ⇒ C) = false
¬ A      ≡ᶠ ○ B     = false
¬ A      ≡ᶠ □ B     = false

(A ⇒ A') ≡ᶠ var m   = false
(A ⇒ A') ≡ᶠ ¬ B     = false
(A ⇒ A') ≡ᶠ (B ⇒ C) = (A ≡ᶠ B) ∧ᵇ (A' ≡ᶠ C)
(A ⇒ A') ≡ᶠ ○ B     = false
(A ⇒ A') ≡ᶠ □ B     = false

○ A      ≡ᶠ var m   = false
○ A      ≡ᶠ ¬ B     = false
○ A      ≡ᶠ (B ⇒ C) = false
○ A      ≡ᶠ ○ B     = A ≡ᶠ B
○ A      ≡ᶠ □ B     = false

□ A      ≡ᶠ var m   = false
□ A      ≡ᶠ ¬ B     = false
□ A      ≡ᶠ (B ⇒ C) = false
□ A      ≡ᶠ ○ B     = false
□ A      ≡ᶠ □ B     = A ≡ᶠ B

------------------------------------------------------------------------
-- ≡ᶠ is reflexive, hence complete

≡ᶠ-refl : (A : Formula) -> A ≡ᶠ A ≡ true
≡ᶠ-refl (var n) = ≡ⁿ-refl n
≡ᶠ-refl (¬ A)   = ≡ᶠ-refl A
≡ᶠ-refl (A ⇒ B) = ∧ᵇ-intro (A ≡ᶠ A) (B ≡ᶠ B)
                           (≡ᶠ-refl A) (≡ᶠ-refl B)
≡ᶠ-refl (○ A)   = ≡ᶠ-refl A
≡ᶠ-refl (□ A)   = ≡ᶠ-refl A

≡ᶠ-complete : (A B : Formula) -> A ≡ B -> A ≡ᶠ B ≡ true
≡ᶠ-complete A B refl = ≡ᶠ-refl A

------------------------------------------------------------------------
-- ≡ᶠ is sound

≡ᶠ-sound : (A B : Formula) -> A ≡ᶠ B ≡ true -> A ≡ B
≡ᶠ-sound (var n)  (var m) p = cong var (≡ⁿ-sound n m p)
≡ᶠ-sound (var n)  (¬ B)   ()
≡ᶠ-sound (var n)  (B ⇒ C) ()
≡ᶠ-sound (var n)  (○ B)   ()
≡ᶠ-sound (var n)  (□ B)   ()

≡ᶠ-sound (¬ A)    (var m) ()
≡ᶠ-sound (¬ A)    (¬ B)   p = cong ¬_ (≡ᶠ-sound A B p)
≡ᶠ-sound (¬ A)    (B ⇒ C) ()
≡ᶠ-sound (¬ A)    (○ B)   ()
≡ᶠ-sound (¬ A)    (□ B)   ()

≡ᶠ-sound (A ⇒ A') (var m) ()
≡ᶠ-sound (A ⇒ A') (¬ B)   ()
≡ᶠ-sound (A ⇒ A') (B ⇒ C) p =
  ⇒Cong (≡ᶠ-sound A B (∧ᵇ-trueˡ (A ≡ᶠ B) (A' ≡ᶠ C) p))
        (≡ᶠ-sound A' C (∧ᵇ-trueʳ (A ≡ᶠ B) (A' ≡ᶠ C) p))
  where
    ⇒Cong : {X Y X' Y' : Formula} -> X ≡ Y -> X' ≡ Y' -> X ⇒ X' ≡ Y ⇒ Y'
    ⇒Cong refl refl = refl
≡ᶠ-sound (A ⇒ A') (○ B)   ()
≡ᶠ-sound (A ⇒ A') (□ B)   ()

≡ᶠ-sound (○ A)    (var m) ()
≡ᶠ-sound (○ A)    (¬ B)   ()
≡ᶠ-sound (○ A)    (B ⇒ C) ()
≡ᶠ-sound (○ A)    (○ B)   p = cong ○_ (≡ᶠ-sound A B p)
≡ᶠ-sound (○ A)    (□ B)   ()

≡ᶠ-sound (□ A)    (var m) ()
≡ᶠ-sound (□ A)    (¬ B)   ()
≡ᶠ-sound (□ A)    (B ⇒ C) ()
≡ᶠ-sound (□ A)    (○ B)   ()
≡ᶠ-sound (□ A)    (□ B)   p = cong □_ (≡ᶠ-sound A B p)

------------------------------------------------------------------------
-- Subformulas
--
-- sub P by plain structural recursion (no closure operation; it may contain
-- duplicates).  The membership lemmas all follow from sub-self and the
-- transitivity lemma sub-mono.

sub : Formula -> List Formula
sub (var n) = var n ∷ []
sub (¬ A)   = ¬ A ∷ sub A
sub (A ⇒ B) = A ⇒ B ∷ sub A ++ sub B
sub (○ A)   = ○ A ∷ sub A
sub (□ A)   = □ A ∷ sub A

------------------------------------------------------------------------
-- sub P always begins with P

sub-self : (A : Formula) -> A ∈ sub A
sub-self (var n) = here
sub-self (¬ A)   = here
sub-self (A ⇒ B) = here
sub-self (○ A)   = here
sub-self (□ A)   = here

------------------------------------------------------------------------
-- Transitivity: sub is closed under passing to subformulas of its members.
-- The here cases are all  k  itself, since there Q is P.

sub-mono : (P : Formula) -> ∀ⁱ[ Q ∈ sub P ] ∀ⁱ[ X ∈ sub Q ] X ∈ sub P
sub-mono (var n) here       k = k
sub-mono (var n) (there ()) k
sub-mono (¬ A)   here       k = k
sub-mono (¬ A)   (there h)  k = there (sub-mono A h k)
sub-mono (A ⇒ B) here       k = k
sub-mono (A ⇒ B) (there h)  k =
  there (sumElim (λ h1 -> memAppL (sub A) (sub B) (sub-mono A h1 k))
                 (λ h2 -> memAppR (sub A) (sub B) (sub-mono B h2 k))
                 (memAppCase (sub A) (sub B) h))
sub-mono (○ A)   here       k = k
sub-mono (○ A)   (there h)  k = there (sub-mono A h k)
sub-mono (□ A)   here       k = k
sub-mono (□ A)   (there h)  k = there (sub-mono A h k)

------------------------------------------------------------------------
-- The five membership lemmas

module _ (P : Formula) where

  sub-¬ : {A : Formula} -> ¬ A ∈ sub P -> A ∈ sub P
  sub-¬ {A} h = sub-mono P h (there (sub-self A))

  sub-⇒L : {A B : Formula} -> A ⇒ B ∈ sub P -> A ∈ sub P
  sub-⇒L {A} {B} h = sub-mono P h (there (memAppL (sub A) (sub B) (sub-self A)))

  sub-⇒R : {A B : Formula} -> A ⇒ B ∈ sub P -> B ∈ sub P
  sub-⇒R {A} {B} h = sub-mono P h (there (memAppR (sub A) (sub B) (sub-self B)))

  sub-○ : {A : Formula} -> ○ A ∈ sub P -> A ∈ sub P
  sub-○ {A} h = sub-mono P h (there (sub-self A))

  sub-□ : {A : Formula} -> □ A ∈ sub P -> A ∈ sub P
  sub-□ {A} h = sub-mono P h (there (sub-self A))
