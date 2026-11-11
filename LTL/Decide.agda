{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Decide -- G28 of FORMALISATION-PLAN.md, Theorem 6.1 of m4.tex.
--
--   decide : (Q : Formula) -> ⊢ Q ⊎ LassoCountermodel Q
--
-- Run the elimination on Sub(¬ Q) and ask whether some surviving state
-- contains ¬ Q.  That is one boolean, satB (¬ Q), and it decides which
-- branch applies; both branches were already complete before this module.
--
--   satB (¬ Q) = false.  Every state containing ¬ Q was removed, so is
--     refutable by Theorem 4.1; every survivor contains Q.  State completeness
--     closes it.  This is `provable` in LTL.Extract, and the certificate is a
--     derivation.
--
--   satB (¬ Q) = true.  Proposition 5.3 gives a fulfilling lasso through such
--     a state, Hintikka's lemma evaluates ¬ Q to 1 there, hence Q to 0, and
--     soundness says a derivation of Q would evaluate it to 1.  The certificate
--     is the lasso, together with the function turning any derivation of Q into
--     Empty.
--
-- The asymmetry the note insists on is visible in the types.  Neither branch is
-- obtained by refuting the other: `provable` never mentions a lasso, and
-- `countermodel` never mentions a derivation except to consume one.  In
-- particular the false branch returns a DERIVATION rather than an assertion of
-- unsatisfiability, which is what removes the classical step.

module LTL.Decide where

open import LTL.Hintikka public

------------------------------------------------------------------------
-- What a countermodel is

data LassoCountermodel (Q : Formula) : Set where
  countermodel : (v0 : Val) (r : Run (¬ Q) v0)
              -> v0 ∈ Uinf (¬ Q)
              -> eval (¬ Q) v0 r Q 0 ≡ false
              -> (⊢ Q -> Empty)
              -> LassoCountermodel Q

------------------------------------------------------------------------
-- Building one.
--
-- v0 contains ¬ Q and is a state, so by (S1) it does not contain Q;
-- Hintikka's lemma at stage 0 transfers that to the evaluation.

buildCM : (Q : Formula) (v0 : Val) -> v0 ∈ Uinf (¬ Q)
       -> valOf (¬ Q) v0 (¬ Q) ≡ true -> LassoCountermodel Q
buildCM Q v0 m ev = countermodel v0 r m evalFalse noDeriv
  where
    r : Run (¬ Q) v0
    r = runOf (¬ Q) v0 m (lasso (¬ Q) v0 m)

    -- (S1) at ¬ Q, the head of sub (¬ Q)
    valQ : valOf (¬ Q) v0 Q ≡ false
    valQ =
      notTrue (valOf (¬ Q) v0 Q)
        (trans (sym (boolEq_sound (valOf (¬ Q) v0 (¬ Q))
                                  (¬ᵇ valOf (¬ Q) v0 Q)
                                  (stateOk (¬ Q) v0 m (sub_self (¬ Q)))))
               ev)

    evalFalse : eval (¬ Q) v0 r Q 0 ≡ false
    evalFalse =
      trans (sym (hintStart (¬ Q) v0 r Q (there (sub_self Q)))) valQ

    noDeriv : ⊢ Q -> Empty
    noDeriv d = tfAbs (trans (sym (soundRun (¬ Q) v0 r d 0)) evalFalse)

------------------------------------------------------------------------
-- Theorem 6.1

decide : (Q : Formula) -> ⊢ Q ⊎ LassoCountermodel Q
decide Q = onSat (satB (¬ Q)) refl
  where
    fromSig : (Σ[ v ∈ Val ] v ∈ Uinf (¬ Q) ×
                                valOf (¬ Q) v (¬ Q) ≡ true)
           -> ⊢ Q ⊎ LassoCountermodel Q
    fromSig (v0 , m , ev) = inr (buildCM Q v0 m ev)

    onSat : (x : Bool) -> satB (¬ Q) ≡ x
         -> ⊢ Q ⊎ LassoCountermodel Q
    onSat false e = inl (provable Q e)
    onSat true  e =
      fromSig (anyL_true (λ v -> valOf (¬ Q) v (¬ Q)) (Uinf (¬ Q)) e)

------------------------------------------------------------------------
-- Reading the answer

isProof : {A B : Set} -> A ⊎ B -> Bool
isProof (inl a) = true
isProof (inr b) = false

-- The run stores the states still to come before the cycle restarts, which is
-- the lasso's stem followed by its cycle; so the stem has length
-- length (cmRest Q c) - length (cmCycle Q c), and is empty exactly when the two
-- agree.
cmRest : (Q : Formula) -> LassoCountermodel Q -> List Val
cmRest Q (countermodel v0 (mkRun b c0 c1 mc0 wc stb mbc cyc rest mv0 wr) m ef rf) =
  rest

cmCycle : (Q : Formula) -> LassoCountermodel Q -> List Val
cmCycle Q (countermodel v0 (mkRun b c0 c1 mc0 wc stb mbc cyc rest mv0 wr) m ef rf) =
  c0 ∷ c1

cmStart : (Q : Formula) -> LassoCountermodel Q -> Val
cmStart Q (countermodel v0 r m ef rf) = v0

lassoOfDecide : (Q : Formula) -> ⊢ Q ⊎ LassoCountermodel Q
             -> Val × List Val × List Val
lassoOfDecide Q (inl d) = [] , [] , []
lassoOfDecide Q (inr c) = cmStart Q c , cmRest Q c , cmCycle Q c

------------------------------------------------------------------------
-- Looking at a derivation.
--
-- A derivation is a finite tree -- eleven constructors, of which only pc
-- carries a side condition, and that one a decidable boolean -- so one can
-- simply count it.  These are the inl branch's counterpart to traceOf
-- below: what decide returns on a provable formula is not the assertion that it
-- is provable but the proof, and this is how one looks at it.

derivSize : {A : Formula} -> ⊢ A -> Nat
derivSize p1       = 1
derivSize p2       = 1
derivSize p3       = 1
derivSize k□     = 1
derivSize k○     = 1
derivSize exp      = 1
derivSize ind      = 1
derivSize lin      = 1
derivSize (pc e)   = 1
derivSize (mp d e) = suc (plus (derivSize d) (derivSize e))
derivSize (gen d)  = suc (derivSize d)

derivMP : {A : Formula} -> ⊢ A -> Nat
derivMP p1       = 0
derivMP p2       = 0
derivMP p3       = 0
derivMP k□     = 0
derivMP k○     = 0
derivMP exp      = 0
derivMP ind      = 0
derivMP lin      = 0
derivMP (pc e)   = 0
derivMP (mp d e) = suc (plus (derivMP d) (derivMP e))
derivMP (gen d)  = derivMP d

derivGen : {A : Formula} -> ⊢ A -> Nat
derivGen p1       = 0
derivGen p2       = 0
derivGen p3       = 0
derivGen k□     = 0
derivGen k○     = 0
derivGen exp      = 0
derivGen ind      = 0
derivGen lin      = 0
derivGen (pc e)   = 0
derivGen (mp d e) = plus (derivGen d) (derivGen e)
derivGen (gen d)  = suc (derivGen d)

-- (Ind) is the only constructor whose presence is interesting: it is the one
-- case of Theorem 4.1 that the loop invariant needs, so counting it says
-- whether the refutation went through extractR2 at all.

derivInd : {A : Formula} -> ⊢ A -> Nat
derivInd p1       = 0
derivInd p2       = 0
derivInd p3       = 0
derivInd k□     = 0
derivInd k○     = 0
derivInd exp      = 0
derivInd ind      = 1
derivInd lin      = 0
derivInd (pc e)   = 0
derivInd (mp d e) = plus (derivInd d) (derivInd e)
derivInd (gen d)  = derivInd d

-- size, modus ponens steps, generalisations, (Ind) instances

countOf : (Q : Formula) -> Nat × Nat × Nat × Nat
countOf Q = onDec (decide Q)
  where
    onDec : ⊢ Q ⊎ LassoCountermodel Q -> Nat × Nat × Nat × Nat
    onDec (inl d) = derivSize d , derivMP d , derivGen d , derivInd d
    onDec (inr c) = zero , zero , zero , zero

------------------------------------------------------------------------
-- Looking at a countermodel.
--
-- The bit vectors above are the states as the procedure stores them, read
-- against sub (¬ Q); they say everything but say it unreadably.  What one
-- actually wants to see is the truth value of a chosen formula at each stage of
-- the run, and the record already carries the run, so this is eval of LTL.Eval
-- applied at the successive stages.
--
-- Note the formula being evaluated is arbitrary: evalAt is total on all of
-- Formula, not only on sub (¬ Q) (see section 4d of FORMALISATION-PLAN.md),
-- so one may ask about a variable, about Q itself, or about anything else.

cmEval : (Q : Formula) -> LassoCountermodel Q -> Formula -> Nat -> Bool
cmEval Q (countermodel v0 r m ef rf) A i = eval (¬ Q) v0 r A i

cmFrom : (Q : Formula) -> LassoCountermodel Q -> Formula -> Nat -> Nat -> List Bool
cmFrom Q c A i zero    = []
cmFrom Q c A i (suc n) = cmEval Q c A i ∷ cmFrom Q c A (suc i) n

-- The truth values of A at stages 0,...,n-1 of the countermodel to Q, or the
-- empty list if Q turned out to be provable and there is no countermodel.

traceOf : (Q : Formula) -> Formula -> Nat -> List Bool
traceOf Q A n = onDec (decide Q)
  where
    onDec : ⊢ Q ⊎ LassoCountermodel Q -> List Bool
    onDec (inl d) = []
    onDec (inr c) = cmFrom Q c A zero n

-- and the shape of the lasso: the run is  v0  followed by cmRest, whose tail is
-- the cycle, so it is periodic from stage  1 + |cmRest| - |cmCycle|  on, with
-- period |cmCycle|.

shapeOf : (Q : Formula) -> Nat × Nat
shapeOf Q = onDec (decide Q)
  where
    onDec : ⊢ Q ⊎ LassoCountermodel Q -> Nat × Nat
    onDec (inl d) = zero , zero
    onDec (inr c) = length (cmRest Q c) , length (cmCycle Q c)

------------------------------------------------------------------------
-- Checkpoint C4.
--
-- Ben-Ari's formula is decided in the affirmative: decide returns inl, so the
-- certificate is a derivation of  □ p ⇒ ○ □ p  in the system L.  The
-- same for  □ p ⇒ □ ○ p , whose derivation goes through case (R2) of
-- Theorem 4.1 -- see bnbProof in LTL.Extract.

decide_benAri : isProof (decide benAri) ≡ true
decide_benAri = refl

decide_bnb : isProof (decide bnb) ≡ true
decide_bnb = refl

-- ◇ p is decided in the negative, and the certificate is a lasso.
--
-- The procedure runs on  ¬ ◇ p = ¬ ¬ □ ¬ p , whose five
-- subformulas are
--
--    ¬ ◇ p ,  ◇ p ,  □ ¬ p ,  ¬ p ,  p
--
-- and the surviving state it starts from is  1 0 1 1 0 : ◇ p fails, □ ¬ p
-- holds, p does not.  The stem is empty -- rest and cycle coincide -- and the
-- cycle is that state looping to itself.  So the countermodel is the obvious
-- one, p false forever, and by the ⊢ Q -> Empty field of the record,
-- ◇ p has no derivation in L.

cmState : Val
cmState = true ∷ false ∷ true ∷ true ∷ false ∷ []

decide_◇P : isProof (decide ◇P) ≡ false
decide_◇P = refl

decide_◇P_lasso : lassoOfDecide ◇P (decide ◇P) ≡
                       (cmState , cmState ∷ [] , cmState ∷ [])
decide_◇P_lasso = refl

------------------------------------------------------------------------
-- Checkpoint C5, the target of Phase 8.
--
--   □ (p ∨ q) ⇒ □ p ∨ □ q
--
-- is NOT valid, and decide says so with a lasso.  Sub of its negation has
-- length 13, so the state space is nominally 8192 vectors; the five atoms are
-- □ (p ∨ q), p, q, □ p, □ q, so 32 assignments are built, 17 of them are
-- states, and the closure of those containing the negation has 8 members, none
-- of which is eliminated.  This is the measurement Phase 8 exists for: 34.6 s
-- before G29, 1.4 s after it, and 0.9 s after G30 -- for the whole
-- countermodel, not just the branch.
--
-- The countermodel it returns is the expected one.  Writing a state as the
-- pair (p , q) -- the other eleven bits are determined -- the run is
--
--   (1,1)  ->  (0,1)  ->  (1,0)  ->  (1,1)  ->  (1,1)  ->  ...
--
-- so p or q holds at every stage, while p fails at stage 1 and q at stage 2.
-- Hence □ (p ∨ q) holds and neither □ p nor □ q does.  The stem is
-- three states and the cycle is the single state at which both hold forever.

cp : Formula
cp = var zero

cq : Formula
cq = var (suc zero)

c5 : Formula
c5 = □ (cp ∨ cq) ⇒ □ cp ∨ □ cq

-- p and q, but neither forever
c5both : Val
c5both = true  ∷ false ∷ true ∷ true ∷ false ∷ true ∷ true
      ∷ false ∷ true  ∷ false ∷ true  ∷ false ∷ true ∷ []

-- q, not p
c5q : Val
c5q = true  ∷ false ∷ true ∷ true ∷ true  ∷ false ∷ true
   ∷ false ∷ true  ∷ false ∷ false ∷ false ∷ true ∷ []

-- p, not q
c5p : Val
c5p = false ∷ true ∷ true ∷ true ∷ false ∷ true ∷ false
   ∷ true  ∷ false ∷ true  ∷ true  ∷ false ∷ false ∷ []

-- p and q, both forever
c5pq : Val
c5pq = false ∷ true ∷ true ∷ true ∷ false ∷ true ∷ true
    ∷ true  ∷ false ∷ true ∷ true ∷ true  ∷ true ∷ []

decide_c5 : isProof (decide c5) ≡ false
decide_c5 = refl

decide_c5_lasso : lassoOfDecide c5 (decide c5) ≡
                  (c5both , c5q ∷ c5p ∷ c5pq ∷ c5pq ∷ [] ,
                            c5pq ∷ [])
decide_c5_lasso = refl
