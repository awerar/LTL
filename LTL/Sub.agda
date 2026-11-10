{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Sub -- G2 of FORMALISATION-PLAN.md.
--
-- Sub(phi) of m4.tex section 2: a plain structural recursion, no closure
-- operation (see Remark 2.1 of the note).
--
-- The six membership lemmas the development needs are all consequences of a
-- single transitivity lemma sub_mono together with sub_self, so they are
-- two-liners rather than six separate inductions.

module LTL.Sub where

open import LTL.Formula public

------------------------------------------------------------------------
-- Subformulas

sub : Formula -> List Formula
sub (var n)   = var n :: []
sub (¬ A)   = ¬ A :: sub A
sub (A ⇒ B) = A ⇒ B :: append (sub A) (sub B)
sub (○ A)   = ○ A :: sub A
sub (□ A)   = □ A :: sub A

------------------------------------------------------------------------
-- sub P always begins with P

sub_self : (A : Formula) -> Mem A (sub A)
sub_self (var n)   = memHd
sub_self (¬ A)   = memHd
sub_self (A ⇒ B) = memHd
sub_self (○ A)   = memHd
sub_self (□ A)   = memHd

------------------------------------------------------------------------
-- Transitivity: sub is closed under passing to subformulas of its members.
--
-- The memHd cases are all  k  itself, since there Q is P.

sub_mono : (P : Formula) {Q : Formula} -> Mem Q (sub P)
        -> {X : Formula} -> Mem X (sub Q) -> Mem X (sub P)
sub_mono (var n)   memHd      k = k
sub_mono (var n)   (memTl ()) k
sub_mono (¬ A)   memHd      k = k
sub_mono (¬ A)   (memTl h)  k = memTl (sub_mono A h k)
sub_mono (A ⇒ B) memHd      k = k
sub_mono (A ⇒ B) (memTl h)  k =
  memTl (sumElim (\ h1 -> memAppL (sub A) (sub B) (sub_mono A h1 k))
                 (\ h2 -> memAppR (sub A) (sub B) (sub_mono B h2 k))
                 (memAppCase (sub A) (sub B) h))
sub_mono (○ A)   memHd      k = k
sub_mono (○ A)   (memTl h)  k = memTl (sub_mono A h k)
sub_mono (□ A)   memHd      k = k
sub_mono (□ A)   (memTl h)  k = memTl (sub_mono A h k)

------------------------------------------------------------------------
-- The six membership lemmas

sub_¬ : (P : Formula) {A : Formula} -> Mem (¬ A) (sub P) -> Mem A (sub P)
sub_¬ P {A} h = sub_mono P h (memTl (sub_self A))

sub_⇒L : (P : Formula) {A B : Formula} -> Mem (A ⇒ B) (sub P) -> Mem A (sub P)
sub_⇒L P {A} {B} h = sub_mono P h (memTl (memAppL (sub A) (sub B) (sub_self A)))

sub_⇒R : (P : Formula) {A B : Formula} -> Mem (A ⇒ B) (sub P) -> Mem B (sub P)
sub_⇒R P {A} {B} h = sub_mono P h (memTl (memAppR (sub A) (sub B) (sub_self B)))

sub_○ : (P : Formula) {A : Formula} -> Mem (○ A) (sub P) -> Mem A (sub P)
sub_○ P {A} h = sub_mono P h (memTl (sub_self A))

sub_□ : (P : Formula) {A : Formula} -> Mem (□ A) (sub P) -> Mem A (sub P)
sub_□ P {A} h = sub_mono P h (memTl (sub_self A))

------------------------------------------------------------------------
-- sub produces duplicates.
--
-- This is the point recorded in FORMALISATION-PLAN.md section 0.  Ben-Ari's own
-- example is already an instance: for  □ p ⇒ ○ □ p  we get
--
--   [ □ p ⇒ ○ □ p , □ p , p , ○ □ p , □ p , p ]
--
-- of length 6, with  □ p  and  p  each occurring twice.  A valuation as a
-- List Bool of length 6 therefore assigns them independent bits, which is why
-- isState (G5) carries a duplicate-coherence clause.

benAri : Formula
benAri = □ (var zero) ⇒ ○ □ (var zero)

subBenAri_length : Eq (length (sub benAri)) 6
subBenAri_length = refl

subBenAri_dup : Eq (nth (sub benAri) 1 ⊥) (nth (sub benAri) 4 ⊥)
subBenAri_dup = refl
