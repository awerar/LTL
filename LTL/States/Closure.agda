{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.States.Closure -- Ust P, the set of states the searches explore.
--
-- St P (all states, filtered from all 2^|sub P| valuations) is what the
-- derivations quantify over: ⊢ beta P (St P) is state completeness.  The
-- searches are computed, so they run on a smaller set Ust P with three
-- properties:
--
--   ustSt      every member is a state;
--   ustSeed    every state containing P is a member;
--   ustClosed  the successors of a member are members.
--
-- ustClosed lets a refutation of u use all state-successors of u; ustSeed lets
-- a state outside Ust P be disposed of by (S1), since it cannot contain P.
--
-- Ust P is built in two steps.  First the candidates: a state is determined by
-- its bits at the ATOMS of sub P (the var, ○ and □ entries), so mkV builds
-- it from an assignment to the atoms, and StCand P has exactly the members of
-- St P (8192 candidates become 128 for c5 of LTL.Tests.Checks).
-- Then the successor closure of the states containing P.  That search GROWS
-- its accumulator, so it recurses on a Bar (vecIFin) rather than a length.

module LTL.States.Closure where

open import LTL.States.VecBar public

------------------------------------------------------------------------
-- Extensionality for bit vectors, and the assignment a state induces.  The
-- skeleton evaluation of LTL.Syntax.Skel is shared with the (PC) test: mkV
-- builds a state from a truth-table row.

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
  -- A state is the vector its own atom bits determine.  This is skelEval
  -- (LTL.Syntax.Skel) at valOf, which is compositional by (S1).

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
  -- The successor closure of the states containing P.
  --
  -- The accumulator starts empty, and each round adds every state of StCand P
  -- that is WANTED -- contains P, or is a successor of something already in --
  -- and is not there yet.  When a round adds nothing, the accumulator contains
  -- every wanted state.  Each round adds a new vector of length |sub P|, and
  -- vecIFin says that cannot go on forever.

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

  -- Ust P: the successor closure of the states that contain P.  Every search
  -- runs on it.

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
