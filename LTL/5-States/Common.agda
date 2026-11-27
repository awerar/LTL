{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.5-States.Common -- the formula-independent base of the P-modules.
--
-- The modules from LTL.5-States.State to LTL.7-SCC.SccSeed are parameterised by
-- the formula P.  What they share that does not mention P lives here, so that
-- an importer who opens them unapplied does not see a spurious P argument:
-- the refutation lemmas.  It re-exports the derived rules and the set layer
-- (LTL.1-Lib.Sets, LTL.1-Lib.Exhaustible).  The valuations of P, with
-- positions over them, are LTL.5-States.Valuation, a P-module, so a P-module
-- opens this module, Valuation at P, and its other P-modules.

module LTL.5-States.Common where

open import LTL.3-Rules.Temporal  public
open import LTL.1-Lib.Sets        public
open import LTL.1-Lib.Exhaustible public

------------------------------------------------------------------------
-- Refutation from a formula and its negation

refute : {C B : Formula} -> ⊢ C ⇒ B -> ⊢ C ⇒ ¬ B -> ⊢ ¬ C
refute f g = mp (¬IntroU (liftP f) (liftP g)) deriv⊤

-- Closing the (T1) case of the step lemma, uniformly in the bit

refute○ : {R B : Formula} (c : Bool)
       -> ⊢ R ⇒ (lit (○ B) (¬ᵇ c))
       -> ⊢ R ⇒ ○ (lit B c)
       -> ⊢ ¬ R
refute○ true  f g = refute g f
refute○ false f g = refute f (⇒Trans g linFwd)
