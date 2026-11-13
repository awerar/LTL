{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Closure -- G30 of FORMALISATION-PLAN.md: the set the SEARCH explores, as
-- opposed to the list the DERIVATIONS quantify over.
--
-- Until Phase 8 those were the same object, St P.  They should not be.
--
--   St P is  filter (isState P) (allVecs |Sub P|) , and it has to stay that
--   way: state completeness (G17) is proved by splitting the disjunction over
--   ALL 2^|Sub P| valuations and then dropping the non-states, so  beta (St P)
--   being a theorem IS the fact that the state set is complete.  That term is
--   typechecked and never normalised, so its 2^|Sub P| costs nothing.
--
--   The elimination, Theorem 4.1 and the lasso, on the other hand, ARE
--   normalised -- computing with the decision procedure directly is the point
--   (siles.pdf section 6) -- and they do not need every state.  They need a set
--   U of states that is closed under ->-successors and contains every state
--   containing P, and nothing else.
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
--    state is determined by its bits at the ATOMS of Sub P -- the var, nxt and
--    box entries -- and mkV builds the whole vector from such an assignment.
--    That replaces 2^|Sub P| candidates by 2^|atoms|; for the C5 formula, 8192
--    by 128.  stCandSt and stStCand show the resulting StCand P (St P built
--    from the CANDIDATES) has exactly the members of St P, so nothing is lost
--    and nothing is gained but speed.
--
-- 2. The closure.  U need not be all of StCand P either: it is enough to
--    take the ->-closure of the states containing P.  That is a LEAST fixed point, the
--    one place in the development where the removing iteration of section 4b
--    does not apply -- the accumulator grows -- and it is why Bar is needed
--    rather than another decreasing length.  Each round adds a state that was
--    not there before, so the vectors chosen are distinct, and vecIFin says one
--    cannot go on choosing distinct vectors of length n forever.

module LTL.Closure where

open import LTL.Bar public

------------------------------------------------------------------------
-- Extensionality for bit vectors, and the assignment a state induces.
--
-- Everything else this module used to define -- ∈ᶠ, insF, atoms, valFrom and
-- the indexOf/nth round-trip -- moved down to LTL.Skel when (PC) needed it
-- below Deriv.  The skeleton evaluation is shared with the tautology test,
-- which is the point: mkV builds a state from a truth-table row.

valExt : (v w : Val) -> length v ≡ length w
      -> ((i : Nat) -> i < length v -> bitAt v i ≡ bitAt w i) -> v ≡ w
valExt []      []      e  h = refl
valExt []      (c ∷ w) () h
valExt (b ∷ v) []      () h
valExt (b ∷ v) (c ∷ w) e  h =
  eqCons (h zero ltZero) (valExt v w (sucInj e) (λ i l -> h (suc i) (ltSuc l)))

------------------------------------------------------------------------
-- The vector an assignment to the atoms determines, and the assignment a
-- state induces

mkV : Formula -> Val -> Val
mkV P a = map (valFrom (atoms (sub P)) a) (sub P)

atomBits : Formula -> Val -> Val
atomBits P v = map (valOf P v) (atoms (sub P))

------------------------------------------------------------------------
-- A state is the vector its own atom bits determine.
--
-- This used to be a five-case induction on the formula.  It is now one
-- instance of skelEval (LTL.Skel): valOf at a state is a COMPOSITIONAL reading
-- of formulas, which is exactly what (S1) says, and skelEval says any such
-- reading agrees with the skeleton evaluation.  The other instance of the same
-- lemma is the soundness of (PC) in LTL.Sound, where the two hypotheses are
-- refl because evalAt is defined by ¬ᵇ and ⇒ᵇ.

valFromEq : (P : Formula) (v : Val) -> allOk P v (sub P) ≡ true
         -> (A : Formula) -> A ∈ sub P
         -> valFrom (atoms (sub P)) (atomBits P v) A ≡ valOf P v A
valFromEq P v ok =
  skelEval (valOf P v) (atoms (sub P)) P
           (λ X mX aX -> atomMem (sub P) mX aX)
           (λ X mX -> ⇔ᵇ-sound (valOf P v (¬ X)) (¬ᵇ valOf P v X)
                               (allOk_at P v (sub P) mX ok))
           (λ X Y mX -> ⇔ᵇ-sound (valOf P v (X ⇒ Y))
                                 (valOf P v X ⇒ᵇ valOf P v Y)
                                 (allOk_at P v (sub P) mX ok))

mkV_id : (P : Formula) (v : Val) -> isState P v ≡ true
      -> length v ≡ length (sub P) -> mkV P (atomBits P v) ≡ v
mkV_id P v st len = valExt (mkV P (atomBits P v)) v lenEq pointwise
  where
    ok : allOk P v (sub P) ≡ true
    ok = andTrueL (allOk P v (sub P)) (allCoh P v (length (sub P))) st

    coh : allCoh P v (length (sub P)) ≡ true
    coh = andTrueR (allOk P v (sub P)) (allCoh P v (length (sub P))) st

    lenEq : length (mkV P (atomBits P v)) ≡ length v
    lenEq = trans (map_length (valFrom (atoms (sub P)) (atomBits P v)) (sub P))
                  (sym len)

    pointwise : (i : Nat) -> i < length (mkV P (atomBits P v))
             -> bitAt (mkV P (atomBits P v)) i ≡ bitAt v i
    pointwise i l = trans (trans atI (valFromEq P v ok (nth (sub P) i ⊥) mI))
                          (sym cohI)
      where
        lI : i < length (sub P)
        lI = subst (λ k -> i < k)
                   (map_length (valFrom (atoms (sub P)) (atomBits P v)) (sub P)) l

        mI : nth (sub P) i ⊥ ∈ sub P
        mI = nth_mem (sub P) i lI ⊥

        atI : bitAt (mkV P (atomBits P v)) i ≡
              valFrom (atoms (sub P)) (atomBits P v) (nth (sub P) i ⊥)
        atI = nth_map (valFrom (atoms (sub P)) (atomBits P v)) (sub P) i lI ⊥ false

        cohI : bitAt v i ≡ valOf P v (nth (sub P) i ⊥)
        cohI = ⇔ᵇ-sound (bitAt v i) (valOf P v (nth (sub P) i ⊥))
                        (allCoh_at P v (length (sub P)) i lI coh)

------------------------------------------------------------------------
-- The candidates, and the state list they give

cands : Formula -> List Val
cands P = map (mkV P) (allVecs (length (atoms (sub P))))

candsLen : (P : Formula) {v : Val} -> v ∈ cands P
        -> length v ≡ length (sub P)
candsLen P {v} m =
  fromSig (map_mem_inv (mkV P) (allVecs (length (atoms (sub P)))) m)
  where
    fromSig : (Σ[ a ∈ Val ] a ∈ allVecs (length (atoms (sub P))) ×
                                v ≡ mkV P a)
           -> length v ≡ length (sub P)
    fromSig (a , ma , ea) =
      trans (cong length ea)
            (map_length (valFrom (atoms (sub P)) a) (sub P))

-- St P, computed from the candidates rather than from all of allVecs.

StCand : Formula -> List Val
StCand P = filter (isState P) (cands P)

stCandSt : (P : Formula) {v : Val} -> v ∈ StCand P -> v ∈ St P
stCandSt P {v} m =
  filter_true (isState P) (allVecs (length (sub P)))
              (allVecs_complete (length (sub P)) v
                                (candsLen P (filter_sub (isState P) (cands P) m)))
              (filter_prop (isState P) (cands P) m)

stStCand : (P : Formula) {v : Val} -> v ∈ St P -> v ∈ StCand P
stStCand P {v} m = filter_true (isState P) (cands P) inCands st
  where
    st : isState P v ≡ true
    st = filter_prop (isState P) (allVecs (length (sub P))) m

    len : length v ≡ length (sub P)
    len = allVecs_len' (length (sub P)) v
                       (filter_sub (isState P) (allVecs (length (sub P))) m)
      where
        allVecs_len' : (n : Nat) (w : Val) -> w ∈ allVecs n -> length w ≡ n
        allVecs_len' n w mw = ≡ⁿ-sound (length w) n (allVecs_len n mw)

    inCands : v ∈ cands P
    inCands =
      subst (λ z -> z ∈ cands P) (mkV_id P v st len)
            (memMap (mkV P)
                    (allVecs_complete (length (atoms (sub P))) (atomBits P v)
                                      (map_length (valOf P v) (atoms (sub P)))))

------------------------------------------------------------------------
-- The ->-closure of the states containing P.
--
-- Step 2.  The accumulator acc starts empty and each round adds every state of
-- StCand P that is WANTED -- contains P, or is a ->-successor of something
-- already in acc -- and is not there yet.  When a round finds nothing to add,
-- acc contains every wanted state, which is ustSeed and ustClosed together.
--
-- This is the one search in the development that GROWS, so the removing
-- iteration of FORMALISATION-PLAN.md section 4b does not apply and there is no
-- decreasing length to run on.  What there is instead: each round adds at least
-- one state that was not there before, that state is a vector of length
-- |Sub P|, and one cannot go on choosing distinct vectors of a fixed length
-- forever.  That is vecIFin exactly, guarded so that it is not forced as the
-- search runs, and it is why Bar is needed here and not merely convenient.

vecBar : (P : Formula) -> IFin (hasLength (length (sub P)))
vecBar P = guardedVecBar (length (sub P)) (hasLength (length (sub P))) (λ v ev -> ev)

wanted : Formula -> List Val -> Val -> Bool
wanted P acc v = valOf P v P ∨ᵇ any (λ u -> step P u v) acc

missing : Formula -> List Val -> Val -> Bool
missing P acc v = wanted P acc v ∧ᵇ ¬ᵇ (v ∈ᵛ acc)

-- x is settled when it needs no adding: it is not wanted, or acc already has
-- it.  The search looks for an unsettled x with findFalse.

settled : Formula -> List Val -> Val -> Bool
settled P acc v = ¬ᵇ missing P acc v

addAll : Formula -> List Val -> List Val
addAll P acc = filter (missing P acc) (StCand P) ++ acc

-- Reading settled in both directions (the Boolean step is nandTrueL of
-- LTL.Prelude)

missingOf : (P : Formula) (acc : List Val) (x : Val) -> settled P acc x ≡ false
         -> missing P acc x ≡ true
missingOf P acc x q = notFalse (missing P acc x) q

notInAcc : (P : Formula) (acc : List Val) (x : Val) -> settled P acc x ≡ false
        -> x ∈ᵛ acc ≡ false
notInAcc P acc x q =
  notTrue (x ∈ᵛ acc)
          (andTrueR (wanted P acc x) (¬ᵇ (x ∈ᵛ acc)) (missingOf P acc x q))

inAddAll : (P : Formula) (acc : List Val) (x : Val) -> x ∈ StCand P
        -> settled P acc x ≡ false -> x ∈ addAll P acc
inAddAll P acc x m q =
  memAppL (filter (missing P acc) (StCand P)) acc
          (filter_true (missing P acc) (StCand P) m (missingOf P acc x q))

------------------------------------------------------------------------
-- The search

closeGo   : (P : Formula) {E : Pred} (acc : List Val)
         -> Avail E (StCand P) acc
         -> IFin E -> List Val
closeFind : (P : Formula) {E : Pred} (acc : List Val)
         -> Avail E (StCand P) acc
         -> IFin E -> FindResult (settled P acc) (StCand P) -> List Val

closeGo P acc av bar = closeFind P acc av bar (findFalse (settled P acc) (StCand P))

closeFind P acc av bar      (allTrue f)      = acc
closeFind P {E} acc av (cBar h) (found x m q) =
  closeGo P (addAll P acc) av' (h x (av x m (notInAcc P acc x q)))
  where
    av' : (z : Val) -> z ∈ StCand P -> z ∈ᵛ addAll P acc ≡ false
       -> E z ∧ᵇ (x ≢ᵛ z) ≡ true
    av' z mz e =
      andIntro (E z) (x ≢ᵛ z)
               (av z mz (outAcc (z ∈ᵛ acc) refl))
               (cong ¬ᵇ_ (outX (x ≡ᵛ z) refl))
      where
        outAcc : (b : Bool) -> z ∈ᵛ acc ≡ b -> z ∈ᵛ acc ≡ false
        outAcc false eb = eb
        outAcc true  eb =
          emptyElim (∈ᵛ-false z (addAll P acc) e
                      (memAppR (filter (missing P acc) (StCand P)) acc
                               (∈ᵛ-sound z acc eb)))

        outX : (b : Bool) -> x ≡ᵛ z ≡ b -> x ≡ᵛ z ≡ false
        outX false eb = eb
        outX true  eb =
          emptyElim (∈ᵛ-false z (addAll P acc) e
                      (subst (λ y -> y ∈ addAll P acc) (≡ᵛ-sound x z eb)
                             (inAddAll P acc x m q)))

------------------------------------------------------------------------
-- Its three properties, each by the same recursion

closeGoSt   : (P : Formula) {E : Pred} (acc : List Val)
           -> (av : Avail E (StCand P) acc)
           -> (bar : IFin E)
           -> acc ⊆ StCand P
           -> {z : Val} -> z ∈ closeGo P acc av bar -> z ∈ StCand P
closeFindSt : (P : Formula) {E : Pred} (acc : List Val)
           -> (av : Avail E (StCand P) acc)
           -> (bar : IFin E) (fr : FindResult (settled P acc) (StCand P))
           -> acc ⊆ StCand P
           -> {z : Val} -> z ∈ closeFind P acc av bar fr -> z ∈ StCand P

closeGoSt P acc av bar =
  closeFindSt P acc av bar (findFalse (settled P acc) (StCand P))

closeFindSt P acc av bar      (allTrue f)      sb {z} m = sb z m
closeFindSt P acc av (cBar h) (found x mx q) sb       m =
  closeGoSt P (addAll P acc) _ (h x (av x mx (notInAcc P acc x q))) sb' m
  where
    sb' : (z : Val) -> z ∈ addAll P acc -> z ∈ StCand P
    sb' z mz = sumElim (λ m1 -> filter_sub (missing P acc) (StCand P) m1)
                       (λ m2 -> sb z m2)
                       (memAppCase (filter (missing P acc) (StCand P)) acc mz)

closeGoSeed   : (P : Formula) {E : Pred} (acc : List Val)
             -> (av : Avail E (StCand P) acc)
             -> (bar : IFin E) {z : Val}
             -> z ∈ StCand P -> valOf P z P ≡ true
             -> z ∈ closeGo P acc av bar
closeFindSeed : (P : Formula) {E : Pred} (acc : List Val)
             -> (av : Avail E (StCand P) acc)
             -> (bar : IFin E) (fr : FindResult (settled P acc) (StCand P)) {z : Val}
             -> z ∈ StCand P -> valOf P z P ≡ true
             -> z ∈ closeFind P acc av bar fr

closeGoSeed P acc av bar =
  closeFindSeed P acc av bar (findFalse (settled P acc) (StCand P))

closeFindSeed P acc av bar      (allTrue f)       {z} mz e =
  ∈ᵛ-sound z acc
    (notFalse (z ∈ᵛ acc)
              (nandTrueL (wanted P acc z) (¬ᵇ (z ∈ᵛ acc)) (f mz)
                         (orL (valOf P z P) (any (λ u -> step P u z) acc) e)))
closeFindSeed P acc av (cBar h) (found x mx q)     mz e =
  closeGoSeed P (addAll P acc) _ (h x (av x mx (notInAcc P acc x q))) mz e

closeGoClosed   : (P : Formula) {E : Pred} (acc : List Val)
               -> (av : Avail E (StCand P) acc)
               -> (bar : IFin E) {u w : Val}
               -> u ∈ closeGo P acc av bar -> w ∈ StCand P
               -> step P u w ≡ true -> w ∈ closeGo P acc av bar
closeFindClosed : (P : Formula) {E : Pred} (acc : List Val)
               -> (av : Avail E (StCand P) acc)
               -> (bar : IFin E) (fr : FindResult (settled P acc) (StCand P)) {u w : Val}
               -> u ∈ closeFind P acc av bar fr -> w ∈ StCand P
               -> step P u w ≡ true -> w ∈ closeFind P acc av bar fr

closeGoClosed P acc av bar =
  closeFindClosed P acc av bar (findFalse (settled P acc) (StCand P))

closeFindClosed P acc av bar      (allTrue f)       {u} {w} mu mw st =
  ∈ᵛ-sound w acc
    (notFalse (w ∈ᵛ acc)
              (nandTrueL (wanted P acc w) (¬ᵇ (w ∈ᵛ acc)) (f mw)
                         (orR (valOf P w P) (any (λ u' -> step P u' w) acc)
                              (any_intro (λ u' -> step P u' w) acc mu st))))
closeFindClosed P acc av (cBar h) (found x mx q)      mu mw st =
  closeGoClosed P (addAll P acc) _ (h x (av x mx (notInAcc P acc x q))) mu mw st

------------------------------------------------------------------------
-- The set the search explores, and its three properties

emptyAcc : (P : Formula) (z : Val) -> z ∈ [] {A = Val} -> z ∈ StCand P
emptyAcc P z ()

-- Ust P is the set U of m5.tex (U_st in m4.tex): the ->-closure of the states
-- that contain P.  It is the state set every later search runs on.

Ust : Formula -> List Val
Ust P = closeGo P [] (λ z mz e -> stAllSat P z (stCandSt P mz)) (vecBar P)

ustSt : (P : Formula) {v : Val} -> v ∈ Ust P -> v ∈ St P
ustSt P m =
  stCandSt P (closeGoSt P [] (λ z mz e -> stAllSat P z (stCandSt P mz)) (vecBar P)
                        (emptyAcc P) m)

ustSeed : (P : Formula) {v : Val}
       -> v ∈ St P -> valOf P v P ≡ true -> v ∈ Ust P
ustSeed P m e =
  closeGoSeed P [] (λ z mz e' -> stAllSat P z (stCandSt P mz)) (vecBar P) (stStCand P m) e

ustClosed : (P : Formula) {v w : Val}
         -> v ∈ Ust P -> w ∈ St P -> step P v w ≡ true -> w ∈ Ust P
ustClosed P mv mw st =
  closeGoClosed P [] (λ z mz e -> stAllSat P z (stCandSt P mz)) (vecBar P)
                mv (stStCand P mw) st

ustAllSat : (P : Formula) -> AllSat (hasLength (length (sub P))) (Ust P)
ustAllSat P x m = stAllSat P x (ustSt P m)

ustBar : (P : Formula) -> IFin (hasLength (length (sub P)))
ustBar P = vecBar P
