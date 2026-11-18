{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.States.Closure -- G30 of FORMALISATION-PLAN.md: the set the SEARCH explores, as
-- opposed to the list the DERIVATIONS quantify over.
--
-- The two are different lists.
--
--   St P is  filter (isState P) (allVecs |Sub P|) , and it has to stay that
--   way: state completeness (G17) is proved by splitting the disjunction over
--   ALL 2^|Sub P| valuations and then dropping the non-states, so  beta (St P)
--   being a theorem IS the fact that the state set is complete.  That term is
--   typechecked and never normalised, so its 2^|Sub P| costs nothing.
--
--   The elimination, Theorem 4.1 and the lasso, on the other hand, ARE
--   normalised -- computing with the decision procedure directly is the point
--   (Coquand and Siles, section 6) -- and they do not need every state.  They
--   need a set U of states that is closed under ->-successors and contains
--   every state containing P, and nothing else.
--
-- This module builds such a U and proves the three properties, ustSt, ustSeed
-- and ustClosed, that everything downstream is stated against.
--
-- Why exactly those three.  ustClosed is what case (R1) of Theorem 4.1 needs:
-- the step lemma offers ALL state-successors of u, and each has to be either
-- already refuted or still inside the set being eliminated.  ustSeed is what
-- the provable branch needs: a state outside U cannot contain P, so by (S1) it
-- contains ¬ P and chi_w yields the conclusion with no elimination at all.
-- ustSt keeps every member of U a state.
--
-- U is built in two steps.
--
-- 1. The candidates.  A state is not an arbitrary vector: (S1) determines the
--    bit at  ¬ A  and at  A ⇒ B  from the bits at A and at B, and coherence
--    makes the bit depend on the formula rather than on the position.  So a
--    state is determined by its bits at the ATOMS of Sub P -- the var, ○ and
--    □ entries -- and mkV builds the whole vector from such an assignment.
--    That replaces 2^|Sub P| candidates by 2^|atoms|; for the C5 formula, 8192
--    by 128.  stCandSt and stStCand show the resulting StCand P (St P built
--    from the CANDIDATES) has exactly the members of St P, so nothing is lost
--    and nothing is gained but speed.
--
-- 2. The closure.  U need not be all of StCand P either: it is enough to
--    take the ->-closure of the states containing P.  That is a LEAST fixed
--    point, the one place in the development where the removing iteration of
--    section 4b does not apply -- the accumulator grows -- and it is why Bar is
--    needed rather than another decreasing length.  Each round adds a state
--    that was not there before, so the vectors chosen are distinct, and vecIFin
--    says one cannot go on choosing distinct vectors of length n forever.

module LTL.States.Closure where

open import LTL.States.VecBar public

------------------------------------------------------------------------
-- Extensionality for bit vectors, and the assignment a state induces.
--
-- The skeleton evaluation (∈ᶠ, insF, atoms, valFrom; LTL.Syntax.Skel) is shared with
-- the tautology test of (PC): mkV builds a state from a truth-table row.

valExt : (v w : Val) -> length v ≡ length w
      -> ((i : Nat) -> i < length v -> bitAt v i ≡ bitAt w i) -> v ≡ w
valExt []      []      e  h = refl
valExt []      (c ∷ w) () h
valExt (b ∷ v) []      () h
valExt (b ∷ v) (c ∷ w) e  h =
  cong₂ _∷_ (h zero ltZero)
            (valExt v w (sucInj e) (λ i l -> h (suc i) (ltSuc l)))

------------------------------------------------------------------------
-- The vector an assignment to the atoms determines, and the assignment a
-- state induces

module _ (P : Formula) where

  mkV : Val -> Val
  mkV a = map (valFrom (atoms (sub P)) a) (sub P)

  atomBits : Val -> Val
  atomBits v = map (valOf P v) (atoms (sub P))

  ------------------------------------------------------------------------
  -- A state is the vector its own atom bits determine.
  --
  -- This is one instance of skelEval (LTL.Syntax.Skel): valOf at a state is a
  -- COMPOSITIONAL reading of formulas, which is exactly what (S1) says, and
  -- skelEval says any such reading agrees with the skeleton evaluation.  The
  -- other instance of the same lemma is the soundness of (PC) in LTL.Countermodel.Sound,
  -- where the two hypotheses are refl because evalAt is defined by ¬ᵇ and ⇒ᵇ.

  valFromEq : (v : Val) -> allOk P v (sub P) ≡ true
           -> (A : Formula) -> A ∈ sub P
           -> valFrom (atoms (sub P)) (atomBits v) A ≡ valOf P v A
  valFromEq v ok =
    skelEval (valOf P v) (atoms (sub P)) P
             (λ X mX aX -> atomMem (sub P) mX aX)
             (λ X mX -> ⇔ᵇ-sound (valOf P v (¬ X)) (¬ᵇ valOf P v X)
                                 (all-at (okAt P v) (sub P) mX ok))
             (λ X Y mX -> ⇔ᵇ-sound (valOf P v (X ⇒ Y))
                                   (valOf P v X ⇒ᵇ valOf P v Y)
                                   (all-at (okAt P v) (sub P) mX ok))

  mkV-id : (v : Val) -> isState P v ≡ true
        -> length v ≡ length (sub P) -> mkV (atomBits v) ≡ v
  mkV-id v st len = valExt (mkV (atomBits v)) v lenEq pointwise
    where
      ok : allOk P v (sub P) ≡ true
      ok = ∧ᵇ-trueˡ (allOk P v (sub P)) (allCoh P v (length (sub P))) st

      coh : allCoh P v (length (sub P)) ≡ true
      coh = ∧ᵇ-trueʳ (allOk P v (sub P)) (allCoh P v (length (sub P))) st

      lenEq : length (mkV (atomBits v)) ≡ length v
      lenEq = trans (map-length (valFrom (atoms (sub P)) (atomBits v)) (sub P))
                    (sym len)

      pointwise : (i : Nat) -> i < length (mkV (atomBits v))
               -> bitAt (mkV (atomBits v)) i ≡ bitAt v i
      pointwise i l = trans (trans atI (valFromEq v ok (nth (sub P) i ⊥) mI))
                            (sym cohI)
        where
          lI : i < length (sub P)
          lI = subst (λ k -> i < k)
                     (map-length (valFrom (atoms (sub P)) (atomBits v)) (sub P))
                     l

          mI : nth (sub P) i ⊥ ∈ sub P
          mI = nth-mem (sub P) i lI ⊥

          atI : bitAt (mkV (atomBits v)) i ≡
                valFrom (atoms (sub P)) (atomBits v) (nth (sub P) i ⊥)
          atI = nth-map (valFrom (atoms (sub P)) (atomBits v)) (sub P)
                        i lI ⊥ false

          cohI : bitAt v i ≡ valOf P v (nth (sub P) i ⊥)
          cohI = ⇔ᵇ-sound (bitAt v i) (valOf P v (nth (sub P) i ⊥))
                          (allCoh-at P v (length (sub P)) i lI coh)

  ------------------------------------------------------------------------
  -- The candidates, and the state list they give

  cands : List Val
  cands = map mkV (allVecs (length (atoms (sub P))))

  candsLen : {v : Val} -> v ∈ cands
          -> length v ≡ length (sub P)
  candsLen {v} m =
    fromSig (map-mem-inv mkV (allVecs (length (atoms (sub P)))) m)
    where
      fromSig : (Σ[ a ∈ Val ] a ∈ allVecs (length (atoms (sub P))) ×
                                  v ≡ mkV a)
             -> length v ≡ length (sub P)
      fromSig (a , ma , ea) =
        trans (cong length ea)
              (map-length (valFrom (atoms (sub P)) a) (sub P))

  -- St P, computed from the candidates rather than from all of allVecs.

  StCand : List Val
  StCand = filter (isState P) cands

  stCandSt : {v : Val} -> v ∈ StCand -> v ∈ St P
  stCandSt {v} m =
    filter-true (isState P) (allVecs (length (sub P)))
                (allVecs-complete (length (sub P)) v
                                  (candsLen (filter-sub (isState P) cands m)))
                (filter-prop (isState P) cands m)

  stStCand : {v : Val} -> v ∈ St P -> v ∈ StCand
  stStCand {v} m = filter-true (isState P) cands inCands st
    where
      st : isState P v ≡ true
      st = filter-prop (isState P) (allVecs (length (sub P))) m

      len : length v ≡ length (sub P)
      len = allVecs-len' (length (sub P)) v
                         (filter-sub (isState P) (allVecs (length (sub P))) m)
        where
          allVecs-len' : (n : Nat) (w : Val) -> w ∈ allVecs n -> length w ≡ n
          allVecs-len' n w mw = ≡ⁿ-sound (length w) n (allVecs-len n mw)

      inCands : v ∈ cands
      inCands =
        subst (λ z -> z ∈ cands) (mkV-id v st len)
              (memMap mkV
                      (allVecs-complete
                         (length (atoms (sub P))) (atomBits v)
                         (map-length (valOf P v) (atoms (sub P)))))

  ------------------------------------------------------------------------
  -- The ->-closure of the states containing P.
  --
  -- Step 2.  The accumulator acc starts empty and each round adds every state
  -- of StCand P that is WANTED -- contains P, or is a ->-successor of something
  -- already in acc -- and is not there yet.  When a round finds nothing to add,
  -- acc contains every wanted state, which is ustSeed and ustClosed together.
  --
  -- This is the one search in the development that GROWS, so the removing
  -- iteration of FORMALISATION-PLAN.md section 4b does not apply and there is
  -- no decreasing length to run on.  What there is instead: each round adds at
  -- least one state that was not there before, that state is a vector of length
  -- |Sub P|, and one cannot go on choosing distinct vectors of a fixed length
  -- forever.  That is vecIFin exactly, guarded so that it is not forced as the
  -- search runs, and it is why Bar is needed here and not merely convenient.

  vecBar : IFin (hasLength (length (sub P)))
  vecBar = guardedVecBar (length (sub P)) (hasLength (length (sub P)))
                         (λ v ev -> ev)

  wanted : List Val -> Val -> Bool
  wanted acc v = valOf P v P ∨ᵇ any (λ u -> step P u v) acc

  missing : List Val -> Val -> Bool
  missing acc v = wanted acc v ∧ᵇ ¬ᵇ (v ∈ᵛ acc)

  -- x is settled when it needs no adding: it is not wanted, or acc already has
  -- it.  The search looks for an unsettled x with findFalse.

  settled : List Val -> Val -> Bool
  settled acc v = ¬ᵇ missing acc v

  addAll : List Val -> List Val
  addAll acc = filter (missing acc) StCand ++ acc

  -- Reading settled in both directions (the Boolean step is ¬ᵇ∧ᵇ-cancelˡ of
  -- LTL.Lib.Prelude)

  missingOf : (acc : List Val) (x : Val) -> settled acc x ≡ false
           -> missing acc x ≡ true
  missingOf acc x q = ¬ᵇ-false (missing acc x) q

  notInAcc : (acc : List Val) (x : Val) -> settled acc x ≡ false
          -> x ∈ᵛ acc ≡ false
  notInAcc acc x q =
    ¬ᵇ-true (x ∈ᵛ acc)
            (∧ᵇ-trueʳ (wanted acc x) (¬ᵇ (x ∈ᵛ acc)) (missingOf acc x q))

  inAddAll : (acc : List Val) (x : Val) -> x ∈ StCand
          -> settled acc x ≡ false -> x ∈ addAll acc
  inAddAll acc x m q =
    memAppL (filter (missing acc) StCand) acc
            (filter-true (missing acc) StCand m (missingOf acc x q))

  ------------------------------------------------------------------------
  -- The search

  closeGo   : {E : Pred} (acc : List Val)
           -> Avail E StCand acc
           -> IFin E -> List Val
  closeFind : {E : Pred} (acc : List Val)
           -> Avail E StCand acc
           -> IFin E -> FindResult (settled acc) StCand -> List Val

  closeGo acc av bar = closeFind acc av bar (findFalse (settled acc) StCand)

  closeFind acc av bar      (allTrue f)      = acc
  closeFind {E} acc av (cBar h) (found x m q) =
    closeGo (addAll acc) av' (h x (av x m (notInAcc acc x q)))
    where
      av' : (z : Val) -> z ∈ StCand -> z ∈ᵛ addAll acc ≡ false
         -> E z ∧ᵇ (x ≢ᵛ z) ≡ true
      av' z mz e =
        ∧ᵇ-intro (E z) (x ≢ᵛ z)
                 (av z mz outAcc)
                 (cong ¬ᵇ_ outX)
        where
          outAcc : z ∈ᵛ acc ≡ false
          outAcc = refuteTrue (z ∈ᵛ acc) λ eb ->
            ∈ᵛ-false z (addAll acc) e
             (memAppR (filter (missing acc) StCand) acc
                      (∈ᵛ-sound z acc eb))

          outX : x ≡ᵛ z ≡ false
          outX = refuteTrue (x ≡ᵛ z) λ eb ->
            ∈ᵛ-false z (addAll acc) e
             (subst (λ y -> y ∈ addAll acc) (≡ᵛ-sound x z eb)
                    (inAddAll acc x m q))

  ------------------------------------------------------------------------
  -- Its three properties, each by the same recursion

  closeGoSt   : {E : Pred} (acc : List Val)
             -> (av : Avail E StCand acc)
             -> (bar : IFin E)
             -> acc ⊆ StCand
             -> {z : Val} -> z ∈ closeGo acc av bar -> z ∈ StCand
  closeFindSt : {E : Pred} (acc : List Val)
             -> (av : Avail E StCand acc)
             -> (bar : IFin E) (fr : FindResult (settled acc) StCand)
             -> acc ⊆ StCand
             -> {z : Val} -> z ∈ closeFind acc av bar fr -> z ∈ StCand

  closeGoSt acc av bar =
    closeFindSt acc av bar (findFalse (settled acc) StCand)

  closeFindSt acc av bar      (allTrue f)      sb {z} m = sb z m
  closeFindSt acc av (cBar h) (found x mx q) sb       m =
    closeGoSt (addAll acc) _ (h x (av x mx (notInAcc acc x q))) sb' m
    where
      sb' : (z : Val) -> z ∈ addAll acc -> z ∈ StCand
      sb' z mz = sumElim (λ m1 -> filter-sub (missing acc) StCand m1)
                         (λ m2 -> sb z m2)
                         (memAppCase (filter (missing acc) StCand) acc mz)

  closeGoSeed   : {E : Pred} (acc : List Val)
               -> (av : Avail E StCand acc)
               -> (bar : IFin E) {z : Val}
               -> z ∈ StCand -> valOf P z P ≡ true
               -> z ∈ closeGo acc av bar
  closeFindSeed : {E : Pred} (acc : List Val)
               -> (av : Avail E StCand acc)
               -> (bar : IFin E) (fr : FindResult (settled acc) StCand)
               -> {z : Val} -> z ∈ StCand -> valOf P z P ≡ true
               -> z ∈ closeFind acc av bar fr

  closeGoSeed acc av bar =
    closeFindSeed acc av bar (findFalse (settled acc) StCand)

  closeFindSeed acc av bar      (allTrue f)       {z} mz e =
    ∈ᵛ-sound z acc
      (¬ᵇ-false (z ∈ᵛ acc)
                (¬ᵇ∧ᵇ-cancelˡ (wanted acc z) (¬ᵇ (z ∈ᵛ acc)) (f mz)
                   (∨ᵇ-introˡ (valOf P z P) (any (λ u -> step P u z) acc) e)))
  closeFindSeed acc av (cBar h) (found x mx q)     mz e =
    closeGoSeed (addAll acc) _ (h x (av x mx (notInAcc acc x q))) mz e

  closeGoClosed   : {E : Pred} (acc : List Val)
                 -> (av : Avail E StCand acc)
                 -> (bar : IFin E) {u w : Val}
                 -> u ∈ closeGo acc av bar -> w ∈ StCand
                 -> step P u w ≡ true -> w ∈ closeGo acc av bar
  closeFindClosed : {E : Pred} (acc : List Val)
                 -> (av : Avail E StCand acc)
                 -> (bar : IFin E) (fr : FindResult (settled acc) StCand)
                 -> {u w : Val} -> u ∈ closeFind acc av bar fr -> w ∈ StCand
                 -> step P u w ≡ true -> w ∈ closeFind acc av bar fr

  closeGoClosed acc av bar =
    closeFindClosed acc av bar (findFalse (settled acc) StCand)

  closeFindClosed acc av bar      (allTrue f)       {u} {w} mu mw st =
    ∈ᵛ-sound w acc
      (¬ᵇ-false (w ∈ᵛ acc)
                (¬ᵇ∧ᵇ-cancelˡ (wanted acc w) (¬ᵇ (w ∈ᵛ acc)) (f mw)
                   (∨ᵇ-introʳ (valOf P w P) (any (λ u' -> step P u' w) acc)
                              (any-intro (λ u' -> step P u' w) acc mu st))))
  closeFindClosed acc av (cBar h) (found x mx q)      mu mw st =
    closeGoClosed (addAll acc) _ (h x (av x mx (notInAcc acc x q))) mu mw st

  ------------------------------------------------------------------------
  -- The set the search explores, and its three properties

  emptyAcc : (z : Val) -> z ∈ [] {A = Val} -> z ∈ StCand
  emptyAcc z ()

  -- Ust P is the set U of m5.tex (U_st in m4.tex): the ->-closure of the states
  -- that contain P.  It is the state set every later search runs on.

  Ust : List Val
  Ust = closeGo [] (λ z mz e -> stAllSat P z (stCandSt mz)) vecBar

  ustSt : {v : Val} -> v ∈ Ust -> v ∈ St P
  ustSt m =
    stCandSt (closeGoSt [] (λ z mz e -> stAllSat P z (stCandSt mz)) vecBar
                        emptyAcc m)

  ustSeed : {v : Val}
         -> v ∈ St P -> valOf P v P ≡ true -> v ∈ Ust
  ustSeed m e =
    closeGoSeed [] (λ z mz e' -> stAllSat P z (stCandSt mz)) vecBar
                (stStCand m) e

  ustClosed : {v w : Val}
           -> v ∈ Ust -> w ∈ St P -> step P v w ≡ true -> w ∈ Ust
  ustClosed mv mw st =
    closeGoClosed [] (λ z mz e -> stAllSat P z (stCandSt mz)) vecBar
                  mv (stStCand mw) st

  ustAllSat : AllSat (hasLength (length (sub P))) Ust
  ustAllSat x m = stAllSat P x (ustSt m)

  ustBar : IFin (hasLength (length (sub P)))
  ustBar = vecBar
