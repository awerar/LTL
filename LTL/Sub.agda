{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Sub -- G2 of FORMALISATION-PLAN.md.
--
-- Sub(phi) of m4.tex section 2: a plain structural recursion, no closure
-- operation (see Remark 2.1 of the note).
--
-- The five membership lemmas the development needs are all consequences of a
-- single transitivity lemma sub-mono together with sub-self, so they are
-- two-liners rather than five separate inductions.

module LTL.Sub where

open import LTL.Formula public

------------------------------------------------------------------------
-- Subformulas

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
--
-- The here cases are all  k  itself, since there Q is P.

sub-mono : (P : Formula) {Q : Formula} -> Q ∈ sub P
        -> {X : Formula} -> X ∈ sub Q -> X ∈ sub P
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
