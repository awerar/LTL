{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Eval -- G25 of FORMALISATION-PLAN.md.
--
--   "The lasso is a finite structure with a total successor function, so Always
--    and Eventually evaluate on it by conjunction and disjunction over the
--    finite forward orbit of a state; write [[.]]_s for that Boolean
--    evaluation."                                          -- m4.tex section 5
--
-- Five clauses, one per constructor of Formula.  Only two are not immediate:
--
--   * a variable is read off the state at the position, through valOf.  For a
--     variable not occurring in Sub(P) this gives false -- indexOf returns
--     length (sub P), off the end of the vector -- which is a perfectly good
--     valuation, and G26 will need the evaluation to be total on ALL formulas,
--     not only on subformulas of P, since a derivation may mention anything.
--
--   * □ A is the conjunction of A over the forward orbit.  Since orbitOf
--     returns a list, this is all, and the recursion is structural in the
--     formula: all is passed the partial application evalAt P c0 c1 A at the
--     smaller formula A.  Eventually needs no clause of its own; ◇ A is
--     ¬ □ ¬ A, so it comes out as the disjunction the note describes.
--
-- The evaluation is by POSITION, not by index into a sequence: ○ is one step
-- of nextPos and □ is a conjunction over orbitOf, both of which are functions
-- of the position alone.  eval then indexes by a Nat, as the plan asks, by
-- iterating the successor that many times from the start of the run.

module LTL.Eval where

open import LTL.Global public

------------------------------------------------------------------------
-- The Boolean evaluation at a position

module _ (P : Formula) where

  evalAt : (c0 : Val) (c1 : List Val) -> Formula -> Pos -> Bool
  evalAt c0 c1 (var n) pos = valOf P (posState pos) (var n)
  evalAt c0 c1 (¬ A)   pos = ¬ᵇ evalAt c0 c1 A pos
  evalAt c0 c1 (A ⇒ B) pos = evalAt c0 c1 A pos ⇒ᵇ evalAt c0 c1 B pos
  evalAt c0 c1 (○ A)   pos = evalAt c0 c1 A (nextPos c0 c1 pos)
  evalAt c0 c1 (□ A)   pos = all (evalAt c0 c1 A) (orbitOf c0 c1 pos)

  ------------------------------------------------------------------------
  -- The two ways of using it, and the shapes G26 and G27 will want

  eval□-at : (c0 : Val) (c1 : List Val) (A : Formula) (pos q : Pos)
          -> evalAt c0 c1 (□ A) pos ≡ true -> q ∈ orbitOf c0 c1 pos
          -> evalAt c0 c1 A q ≡ true
  eval□-at c0 c1 A pos q e m =
    all-at (evalAt c0 c1 A) (orbitOf c0 c1 pos) m e

  eval□-intro : (c0 : Val) (c1 : List Val) (A : Formula) (pos : Pos)
             -> ((q : Pos) -> q ∈ orbitOf c0 c1 pos -> evalAt c0 c1 A q ≡ true)
             -> evalAt c0 c1 (□ A) pos ≡ true
  eval□-intro c0 c1 A pos f =
    all-intro (evalAt c0 c1 A) (orbitOf c0 c1 pos) (λ {q} m -> f q m)

  eval□-false : (c0 : Val) (c1 : List Val) (A : Formula) (pos q : Pos)
             -> q ∈ orbitOf c0 c1 pos -> evalAt c0 c1 A q ≡ false
             -> evalAt c0 c1 (□ A) pos ≡ false
  eval□-false c0 c1 A pos q m e =
    all-atFalse (evalAt c0 c1 A) (orbitOf c0 c1 pos) m e

  ------------------------------------------------------------------------
  -- The evaluation on a run, indexed as in the note's unwinding

  eval : (v0 : Val) -> Run P v0 -> Formula -> Nat -> Bool
  eval v0 r A i = evalAt c0 c1 A (posIter c0 c1 i (v0 , rest))
    where open Run r

  ------------------------------------------------------------------------
  -- Running it.
  --
  -- evalOn P v e A i evaluates A at stage i of the lasso built from the named
  -- surviving state v.  It is the whole pipeline in one expression: the states,
  -- the elimination, Proposition 5.3, the unwinding, and the Boolean semantics.

  evalOn : (v : Val) -> v ∈ᵛ Uinf P ≡ true
        -> Formula -> Nat -> Bool
  evalOn v e A i = eval v (runOf P v m (lasso P v m)) A i
    where
      m : v ∈ Uinf P
      m = ∈ᵛ-sound v (Uinf P) e
