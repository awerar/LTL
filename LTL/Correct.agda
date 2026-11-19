{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Correct -- decideSCC meets the specification of LTL.Trusted.
--
-- A DecisionProcedure answers true only for formulas valid on every lasso, and
-- false only with a lasso on which the formula fails.  decideSCC answers with
-- ⊢ Q ⊎ LassoCountermodel Q , and the two branches meet Trusted through one
-- bridge: when a Trusted lasso L starts at pos0 and loops back to loop, the
-- Boolean evaluation of LTL.Countermodel.LassoEval at stage n IS truth at time
-- n of T.interpret L (evalAt-holds, holds-evalAt, by induction on the
-- formula).  The □ case uses the finite forward orbit: every iterate of a
-- position is in its orbit, and every member of the orbit is an iterate.
--
-- ⊢-valid uses the bridge on an arbitrary Trusted lasso, toCounterModel on the
-- lasso a countermodel reads off.  Formula is LTL.Trusted's own datatype, so
-- the statement is about the formulas the procedure runs on.

module LTL.Correct where

open import LTL.Procedures.DecideSCC public
import LTL.Trusted as T
open T using (_,_⊨_)
import LTL.Countermodel.Orbit
import LTL.Countermodel.LassoEval

------------------------------------------------------------------------
-- The bridge.  States have any type S, read gives the instant of a state, and
-- the lasso loops back to the position loop.

module _ {S : Set} (read : S -> T.Instant)
         (loop : LTL.Countermodel.Orbit.Pos S) where

  private
    module O = LTL.Countermodel.Orbit S
    module E = LTL.Countermodel.LassoEval S read

  toPosition : O.Pos -> T.Position
  toPosition (s , ws) = T.at (read s) (map read ws)

  -- L agrees with the lasso of loop from pos0 when it starts at pos0 and loops
  -- back to loop.  Then T.step is nextPos, and so the positions of L are the
  -- iterates of nextPos from pos0.

  module _ (L : T.Lasso) (pos0 : O.Pos)
           (loopBack : T.loopBack L ≡ toPosition loop)
           (initial  : T.initial L ≡ toPosition pos0) where

    stepAgree : (q : O.Pos) -> T.step L (toPosition q) ≡ toPosition (O.nextPos loop q)
    stepAgree (s , [])     = loopBack
    stepAgree (s , w ∷ ws) = refl

    private
      stage : Nat -> O.Pos
      stage n = O.posIter loop n pos0

      True : Formula -> O.Pos -> Set
      True A q = E.evalAt loop A q ≡ true

      nowAgree : (q : O.Pos) -> T.Position.now (toPosition q) ≡ read (O.posState q)
      nowAgree (s , ws) = refl

    positionAgree : (n : Nat) -> T.position L n ≡ toPosition (stage n)
    positionAgree zero    = initial
    positionAgree (suc n) =
      trans (cong (T.step L) (positionAgree n))
            (trans (stepAgree (stage n))
                   (cong toPosition (sym (O.posIter-suc loop n pos0))))

    interpretAgree : (n : Nat) -> T.interpret L n ≡ read (O.posState (stage n))
    interpretAgree n =
      trans (cong T.Position.now (positionAgree n)) (nowAgree (stage n))

    ----------------------------------------------------------------------
    -- The Boolean evaluation is the semantics.  Both directions are proved
    -- together, since ¬ and ⇒ are contravariant in their first argument.

    evalAt-holds : (A : Formula) (n : Nat) -> True A (stage n) -> T.interpret L , n ⊨ A
    holds-evalAt : (A : Formula) (n : Nat) -> T.interpret L , n ⊨ A -> True A (stage n)

    evalAt-holds (var x) n e = subst (λ i -> i x ≡ true) (sym (interpretAgree n)) e

    evalAt-holds (¬ A) n e h =
      true≢false (trans (sym (holds-evalAt A n h))
                        (¬ᵇ-true (E.evalAt loop A (stage n)) e))

    evalAt-holds (A ⇒ B) n e h =
      evalAt-holds B n
        (⇒ᵇ-mp (E.evalAt loop A (stage n)) (E.evalAt loop B (stage n))
               e (holds-evalAt A n h))

    evalAt-holds (○ A) n e =
      evalAt-holds A (suc n)
        (subst (True A) (sym (O.posIter-suc loop n pos0)) e)

    evalAt-holds (□ A) n e k =
      evalAt-holds A (k + n)
        (subst (True A) (sym (O.posIter-+ʳ loop k n pos0))
               (E.eval□-at loop A (stage n) (O.posIter loop k (stage n)) e
                           (O.iter∈orbit loop k (stage n))))

    holds-evalAt (var x) n h = subst (λ i -> i x ≡ true) (interpretAgree n) h

    holds-evalAt (¬ A) n h with E.evalAt loop A (stage n) in ea
    ... | true  = emptyElim (h (evalAt-holds A n ea))
    ... | false = refl

    holds-evalAt (A ⇒ B) n h =
      ⇒ᵇ-intro (E.evalAt loop A (stage n)) (E.evalAt loop B (stage n))
               (λ ea -> holds-evalAt B n (h (evalAt-holds A n ea)))

    holds-evalAt (○ A) n h =
      subst (True A) (O.posIter-suc loop n pos0) (holds-evalAt A (suc n) h)

    holds-evalAt (□ A) n h =
      E.eval□-intro loop A (stage n)
        (λ q m -> fromIter q (O.∈orbit-iter loop (stage n) q m))
      where
        fromIter : (q : O.Pos) -> Σ[ t ∈ Nat ] O.posIter loop t (stage n) ≡ q
                -> True A q
        fromIter q (t , et) =
          subst (True A) (trans (O.posIter-+ʳ loop t n pos0) et)
                (holds-evalAt A (t + n) (h t))

------------------------------------------------------------------------
-- Soundness: a derivable formula is valid.  A Trusted lasso l is a lasso of
-- instants, read by the identity, from T.initial l back to T.loopBack l;
-- LassoEval's soundness holds there.

⊢-valid : {A : Formula} -> ⊢ A -> T.valid A
⊢-valid {A} d l =
  evalAt-holds read loop l pos0
    (cong (T.at _) (sym (map-id (T.Lasso.loopTail l))))
    (cong (T.at _) (sym (map-id (T.Position.rest (T.initial l)))))
    A zero (LTL.Countermodel.LassoEval.sound T.Instant read loop d pos0)
  where
    read : T.Instant -> T.Instant
    read i = i

    loop pos0 : T.Instant × List T.Instant
    loop = T.Lasso.loopHead l , T.Lasso.loopTail l
    pos0 = T.Position.now (T.initial l) , T.Position.rest (T.initial l)

------------------------------------------------------------------------
-- A countermodel is a Trusted countermodel.  Its lasso, read through readVal
-- (¬ Q), is a Trusted lasso: v0 followed by rest, then the cycle c0 ∷ c1 for
-- ever, where loop = c0 , c1 .  Q is false at stage 0 (falseAtStart), so it is
-- not true at time 0.

toCounterModel : (Q : Formula) -> LassoCountermodel Q -> T.LassoCounterModel Q
toCounterModel Q
  (countermodel v0 (mkLasso (mkCycle b (c0 , c1) lv stb) fair rest sv) falseQ) =
  T.counter L qFalse
  where
    rd : Val -> T.Instant
    rd = readVal (¬ Q)

    L : T.Lasso
    L = record { start = map rd (v0 ∷ rest)
               ; loopHead = rd c0
               ; loopTail = map rd c1 }

    qFalse : T.interpret L , zero ⊨ ¬ Q
    qFalse h =
      true≢false
        (trans (sym (holds-evalAt rd (c0 , c1) L (v0 , rest) refl refl Q zero h))
               falseQ)

------------------------------------------------------------------------
-- decideSCC as a Trusted DecisionProcedure.  The test is which branch it took:
-- a derivation is valid by ⊢-valid, and a countermodel translates by
-- toCounterModel.

decideSCCCorrect : T.DecisionProcedure
decideSCCCorrect = record
  { decideValid    = λ Q -> isProof (decideSCC Q)
  ; validIfTrue    = validIfTrue
  ; counterIfFalse = counterIfFalse
  }
  where
    validIfTrue : (Q : Formula) -> isProof (decideSCC Q) ≡ true -> T.valid Q
    validIfTrue Q e with decideSCC Q
    ... | inl d = ⊢-valid d
    ... | inr c = emptyElim (true≢false (sym e))

    counterIfFalse : (Q : Formula) -> isProof (decideSCC Q) ≡ false
                  -> T.LassoCounterModel Q
    counterIfFalse Q e with decideSCC Q
    ... | inl d = emptyElim (true≢false e)
    ... | inr c = toCounterModel Q c
