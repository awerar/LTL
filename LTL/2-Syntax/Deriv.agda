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
  using (⊢_; p1; p2; p3; k□; k○; exp; ind; lin; mp; gen; pc)

------------------------------------------------------------------------
-- (PC) from the decidable test.

pcTaut : {A : Formula} -> isTaut A ≡ true -> ⊢ A
pcTaut {A} e = pc (isTaut-sound A e)

-- A Tautology is true under any reading f compositional on ¬ and ⇒, since
-- f is its own propValue.

tautologyHolds : (f : Formula -> Bool)
              -> ((X : Formula) -> f (¬ X) ≡ ¬ᵇ f X)
              -> ((X Y : Formula) -> f (X ⇒ Y) ≡ f X ⇒ᵇ f Y)
              -> (A : Formula) -> Tautology A -> f A ≡ true
tautologyHolds f fn fi A t = trans (sym (propValue-agree f fn fi A)) (t f)
