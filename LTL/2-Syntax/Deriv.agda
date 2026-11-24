{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.2-Syntax.Deriv -- derivability ⊢ A in the system L: eight axiom schemes,
-- modus ponens, generalisation, and the optional rule (PC).  The datatype is
-- LTL.Statement's, so the derivations decide builds are the ones the trusted
-- statement talks about.
--
-- (PC)'s side condition there is Tautology A: A is true under every Boolean
-- reading that is compositional on ¬ and ⇒.  The procedures establish it with
-- the decidable test isTaut (isTaut-sound, through pcTaut), and soundness reads
-- it back at one compositional reading (tautologyHolds).
--
-- Propositional reasoning uses (P1)-(P3), so everything in LTL.3-Rules is
-- derived without (PC).  (PC) is used only by LTL.5-States.CompletePC and
-- LTL.8-Procedures.Decide, where it keeps the certificates short.

module LTL.2-Syntax.Deriv where

open import LTL.2-Syntax.Skel public
import LTL.Statement as S

-- ⊢ A  says that A is derivable.  ⊢ binds looser than every formula
-- connective, so  ⊢ □ A ⇒ A  is  ⊢ (□ A ⇒ A).

open S public
  using (⊢_; p1; p2; p3; k□; k○; exp; ind; lin; mp; gen; pc; Tautology)

------------------------------------------------------------------------
-- (PC) from the decidable test.  S.propValue ρ is compositional by
-- definition, so tautSound applies to it with refl for both hypotheses.

isTaut-sound : (A : Formula) -> isTaut A ≡ true -> Tautology A
isTaut-sound A e ρ =
  tautSound (S.propValue ρ) A (λ X m -> refl) (λ X Y m -> refl) e

pcTaut : {A : Formula} -> isTaut A ≡ true -> ⊢ A
pcTaut {A} e = pc (isTaut-sound A e)

------------------------------------------------------------------------
-- A Tautology is true under any reading f compositional on ¬ and ⇒: on
-- every formula, S.propValue f agrees with f.

module _ (f : Formula -> Bool)
         (fn : (X : Formula) -> f (¬ X) ≡ ¬ᵇ f X)
         (fi : (X Y : Formula) -> f (X ⇒ Y) ≡ f X ⇒ᵇ f Y) where

  propValue-agree : (A : Formula) -> S.propValue f A ≡ f A
  propValue-agree (var x) = refl
  propValue-agree (¬ A)   = trans (cong ¬ᵇ_ (propValue-agree A)) (sym (fn A))
  propValue-agree (A ⇒ B) =
    trans (cong₂ _⇒ᵇ_ (propValue-agree A) (propValue-agree B)) (sym (fi A B))
  propValue-agree (○ A)   = refl
  propValue-agree (□ A)   = refl

  tautologyHolds : (A : Formula) -> Tautology A -> f A ≡ true
  tautologyHolds A t = trans (sym (propValue-agree A)) (t f)
