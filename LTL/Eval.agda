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
--     variable not occurring in Sub(P) this gives false -- idx returns
--     length (sub P), off the end of the vector -- which is a perfectly good
--     valuation, and G26 will need the evaluation to be total on ALL formulas,
--     not only on subformulas of P, since a derivation may mention anything.
--
--   * □ A is the conjunction of A over the forward orbit.  Since orbitOf
--     returns a list, this is allB, and the recursion is structural in the
--     formula: allB is passed the partial application evalAt P c0 c1 A at the
--     smaller formula A.  Eventually needs no clause of its own; ◇ A is
--     ¬ □ ¬ A, so it comes out as the disjunction the note describes.
--
-- The evaluation is by POSITION, not by index into a sequence: nxt is one step
-- of nextPos and box is a conjunction over orbitOf, both of which are functions
-- of the position alone.  eval then indexes by a Nat, as the plan asks, by
-- iterating the successor that many times from the start of the run.

module LTL.Eval where

open import LTL.Global public

------------------------------------------------------------------------
-- The Boolean evaluation at a position

evalAt : (P : Formula) (c0 : Val) (c1 : List Val) -> Formula -> Pos -> Bool
evalAt P c0 c1 (var n)   pos = valOf P (posState pos) (var n)
evalAt P c0 c1 (¬ A)   pos = boolNot (evalAt P c0 c1 A pos)
evalAt P c0 c1 (A ⇒ B) pos = boolImp (evalAt P c0 c1 A pos) (evalAt P c0 c1 B pos)
evalAt P c0 c1 (○ A)   pos = evalAt P c0 c1 A (nextPos c0 c1 pos)
evalAt P c0 c1 (□ A)   pos = allB (evalAt P c0 c1 A) (orbitOf c0 c1 pos)

------------------------------------------------------------------------
-- The two ways of using it, and the shapes G26 and G27 will want

eval□_at : (P : Formula) (c0 : Val) (c1 : List Val) (A : Formula) (pos q : Pos)
          -> Eq (evalAt P c0 c1 (□ A) pos) true -> Mem q (orbitOf c0 c1 pos)
          -> Eq (evalAt P c0 c1 A q) true
eval□_at P c0 c1 A pos q e m =
  allB_at (evalAt P c0 c1 A) (orbitOf c0 c1 pos) m e

eval□_intro : (P : Formula) (c0 : Val) (c1 : List Val) (A : Formula) (pos : Pos)
             -> ((q : Pos) -> Mem q (orbitOf c0 c1 pos) -> Eq (evalAt P c0 c1 A q) true)
             -> Eq (evalAt P c0 c1 (□ A) pos) true
eval□_intro P c0 c1 A pos f =
  allB_intro (evalAt P c0 c1 A) (orbitOf c0 c1 pos) (\ {q} m -> f q m)

allB_atFalse : {A : Set} (p : A -> Bool) (xs : List A) {x : A}
            -> Mem x xs -> Eq (p x) false -> Eq (allB p xs) false
allB_atFalse p (y :: ys) memHd     e = eqCong (\ c -> boolAnd c (allB p ys)) e
allB_atFalse p (y :: ys) (memTl m) e = andFalseR (p y) (allB p ys)
                                                 (allB_atFalse p ys m e)
  where
    andFalseR : (a b : Bool) -> Eq b false -> Eq (boolAnd a b) false
    andFalseR true  b eb = eb
    andFalseR false b eb = refl
allB_atFalse p []        ()        e

eval□_false : (P : Formula) (c0 : Val) (c1 : List Val) (A : Formula) (pos q : Pos)
             -> Mem q (orbitOf c0 c1 pos) -> Eq (evalAt P c0 c1 A q) false
             -> Eq (evalAt P c0 c1 (□ A) pos) false
eval□_false P c0 c1 A pos q m e =
  allB_atFalse (evalAt P c0 c1 A) (orbitOf c0 c1 pos) m e

------------------------------------------------------------------------
-- The evaluation on a run, indexed as in the note's unwinding

eval : (P : Formula) (v0 : Val) -> Run P v0 -> Formula -> Nat -> Bool
eval P v0 (mkRun b c0 c1 mc0 wc stb mbc cyc rest mv0 wr) A i =
  evalAt P c0 c1 A (posIter c0 c1 i (prod v0 rest))

------------------------------------------------------------------------
-- Running it.
--
-- evalOn P v e A i evaluates A at stage i of the lasso built from the named
-- surviving state v.  It is the whole pipeline in one expression: the states,
-- the elimination, Proposition 5.3, the unwinding, and the Boolean semantics.

evalOn : (P : Formula) (v : Val) -> Eq (memB v (Uinf P)) true
      -> Formula -> Nat -> Bool
evalOn P v e A i = eval P v (runOf P v m (lasso P v m)) A i
  where
    m : Mem v (Uinf P)
    m = memB_sound v (Uinf P) e

------------------------------------------------------------------------
-- Checkpoint.
--
-- For ◇ p, started at the state  1 0 1 0  of LTL.Lasso, the run is
--
--    1 0 1 0  ->  1 0 0 1  ->  0 1 1 0  ->  0 1 1 0  ->  ...
--
-- so p fails at stage 0, holds at stage 1, and fails from stage 2 on, the sink
-- being the state where ◇ p itself is false.  So
--
--   ◇ p    holds at stage 0 -- the eventuality is fulfilled at stage 1
--   p        fails at stage 0 and holds at stage 1
--   □ p    fails, and so does □ ○ p
--   ○ p    holds at stage 0
--   ◇ p    holds at every stage, and this is a genuine countermodel to
--            ¬ ◇ p, which is what Theorem 6.1 will read off.

◇_p : Formula
◇_p = ◇ (var zero)

ev◇St : Val
ev◇St = true :: false :: true :: false :: []

evBnbSt : Val
evBnbSt = false :: true :: true :: true :: true :: true :: true :: []

eval_◇ : Eq (evalOn ◇P ev◇St refl ◇_p 0) true
eval_◇ = refl

eval_p0 : Eq (evalOn ◇P ev◇St refl (var zero) 0) false
eval_p0 = refl

eval_p1 : Eq (evalOn ◇P ev◇St refl (var zero) 1) true
eval_p1 = refl

eval_p2 : Eq (evalOn ◇P ev◇St refl (var zero) 2) false
eval_p2 = refl

eval_○_p : Eq (evalOn ◇P ev◇St refl (○ (var zero)) 0) true
eval_○_p = refl

eval_□_p : Eq (evalOn ◇P ev◇St refl (□ (var zero)) 0) false
eval_□_p = refl

eval_◇1 : Eq (evalOn ◇P ev◇St refl ◇_p 1) true
eval_◇1 = refl

-- and the formula the procedure was run on holds at stage 0, as Hintikka's
-- lemma (G27) will say in general

eval_input : Eq (evalOn ◇P ev◇St refl ◇P 0) true
eval_input = refl

eval_□_○_p : Eq (evalOn ◇P ev◇St refl (□ ○ (var zero)) 0) false
eval_□_○_p = refl

-- The contrast, in the two forms G30 gives it.
--
-- For  □ p  the lasso is the single state of LTL.Lasso at which p holds
-- forever, so □ p is TRUE there and the lasso IS a countermodel to
-- ¬ □ p.

eval_□P_p : Eq (evalOn □P s□ refl (var zero) 3) true
eval_□P_p = refl

eval_□P_input : Eq (evalOn □P s□ refl □P 0) true
eval_□P_input = refl

-- For ¬ bnb there is no lasso at all: nothing containing ¬ bnb survives,
-- and since G30 explores only the closure of the states that do contain it,
-- U_infinity is empty rather than merely free of them (Uinf_¬Bnb in
-- LTL.Trace).  That is the branch where the certificate is a derivation, and
-- provable supplies it -- see bnbProof in LTL.Extract.

eval_¬Bnb_empty : Eq (nullB (Uinf ¬Bnb)) true
eval_¬Bnb_empty = refl
