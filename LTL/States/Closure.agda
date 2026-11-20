{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.States.Closure -- Ust P, the set of states the searches explore.
--
-- St (all states, filtered from all 2^|sub P| valuations) is what the
-- derivations quantify over: ⊢ beta St is state completeness.  The
-- searches are computed, so they run on a smaller set Ust with three
-- properties:
--
--   ustSt      every member is a state;
--   ustSeed    every state containing P is a member;
--   ustClosed  the successors of a member are members.
--
-- ustClosed lets a refutation of u use all state-successors of u; ustSeed lets
-- a state outside Ust be disposed of by (S1), since it cannot contain P.
--
-- Ust is built in two steps.  First the candidates: a state is determined by
-- its bits at the ATOMS of sub P (the var, ○ and □ entries), so mkV builds
-- it from an assignment to the atoms, and StCand has exactly the members of
-- St (8192 candidates become 128 for c5 of LTL.Tests.Checks).
-- Then the successor closure of the states containing P, by the growing
-- search of LTL.SCC.Graph.  That search GROWS its accumulator, so it
-- recurses on a Bar (vecIFin) rather than a length.

open import LTL.Syntax.Formula using (Formula)

module LTL.States.Closure (P : Formula) where

open import LTL.States.Common
open import LTL.States.VecBar
open import LTL.States.State P
open import LTL.States.Step P

-- The growing search, at the edge test step.  LTL.Countermodel.Walk makes
-- the application the other P-modules see; this one stays private.
open import LTL.SCC.Graph _≡ᵛ_ ≡ᵛ-sound ≡ᵛ-refl step
  using (closure; closureIn; closureSeed; closureClosed)

------------------------------------------------------------------------
-- The vector an assignment to the atoms determines, and the assignment a
-- state induces.  The skeleton evaluation of LTL.Syntax.Skel is shared with
-- the (PC) test: mkV builds a state from a truth-table row.

-- Every state has the length the bar over vectors expects.
stAllSat : AllSat (hasLength (length (sub P))) St
stAllSat x m = hasLength-intro (length (sub P)) x (stLen m)

mkV : Val -> Val
mkV a = map (valFrom (atoms (sub P)) a) (sub P)

atomBits : Val -> Val
atomBits v = map (valOf v) (atoms (sub P))

------------------------------------------------------------------------
-- A state is the vector its own atom bits determine.  This is skelEval
-- (LTL.Syntax.Skel) at valOf, which is compositional by (S1).

valFromEq : (v : Val) -> allOk v (sub P) ≡ true
         -> ∀[ A ∈ sub P ] valFrom (atoms (sub P)) (atomBits v) A ≡ valOf v A
valFromEq v ok =
  skelEval (valOf v) (atoms (sub P)) P
           (λ X mX aX -> atomMem (sub P) mX aX)
           (λ X mX -> ⇔ᵇ-sound (valOf v (¬ X)) (¬ᵇ valOf v X)
                               (all-at (okAt v) (sub P) mX ok))
           (λ X Y mX -> ⇔ᵇ-sound (valOf v (X ⇒ Y))
                                 (valOf v X ⇒ᵇ valOf v Y)
                                 (all-at (okAt v) (sub P) mX ok))

mkV-id : (v : Val) -> isState v ≡ true
      -> length v ≡ length (sub P) -> mkV (atomBits v) ≡ v
mkV-id v st len = valExt (mkV (atomBits v)) v lenEq pointwise
  where
    ok : allOk v (sub P) ≡ true
    ok = ∧ᵇ-trueˡ (allOk v (sub P)) (allCoh v (length (sub P))) st

    coh : allCoh v (length (sub P)) ≡ true
    coh = ∧ᵇ-trueʳ (allOk v (sub P)) (allCoh v (length (sub P))) st

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

        cohI : bitAt v i ≡ valOf v (nth (sub P) i ⊥)
        cohI = ⇔ᵇ-sound (bitAt v i) (valOf v (nth (sub P) i ⊥))
                        (allCoh-at v (length (sub P)) i lI coh)

------------------------------------------------------------------------
-- The candidates, and the state list they give

cands : List Val
cands = map mkV (allVecs (length (atoms (sub P))))

candsLen : {v : Val} -> v ∈ cands
        -> length v ≡ length (sub P)
candsLen {v} m =
  fromSig (map-mem-inv mkV (allVecs (length (atoms (sub P)))) m)
  where
    fromSig : (∃[ a ∈ allVecs (length (atoms (sub P))) ] v ≡ mkV a)
           -> length v ≡ length (sub P)
    fromSig (a , ma , ea) =
      trans (cong length ea)
            (map-length (valFrom (atoms (sub P)) a) (sub P))

-- St P, computed from the candidates rather than from all of allVecs.

StCand : List Val
StCand = filter isState cands

stCandSt : {v : Val} -> v ∈ StCand -> v ∈ St
stCandSt {v} m =
  filter-true isState (allVecs (length (sub P)))
              (allVecs-complete (length (sub P)) v
                                (candsLen (filter-sub isState cands m)))
              (filter-prop isState cands m)

stStCand : {v : Val} -> v ∈ St -> v ∈ StCand
stStCand {v} m = filter-true isState cands inCands st
  where
    st : isState v ≡ true
    st = filter-prop isState (allVecs (length (sub P))) m

    inCands : v ∈ cands
    inCands =
      subst (λ z -> z ∈ cands) (mkV-id v st (stLen m))
            (memMap mkV
                    (allVecs-complete
                       (length (atoms (sub P))) (atomBits v)
                       (map-length (valOf v) (atoms (sub P)))))

------------------------------------------------------------------------
-- The successor closure of the states containing P: the growing search
-- closure of LTL.SCC.Graph, seeded by "contains P", over StCand.  Each round
-- adds a new vector of length |sub P|, and vecBar says that cannot go on
-- forever.

vecBar : IFin (hasLength (length (sub P)))
vecBar = guardedVecBar (length (sub P)) (hasLength (length (sub P)))
                       (λ v ev -> ev)

containsP : Val -> Bool
containsP v = valOf v P

stCandLen : AllSat (hasLength (length (sub P))) StCand
stCandLen z mz = stAllSat z (stCandSt mz)

-- Ust P: the successor closure of the states that contain P.  Every search
-- runs on it.

Ust : List Val
Ust = closure containsP StCand stCandLen vecBar

ustSt : {v : Val} -> v ∈ Ust -> v ∈ St
ustSt {v} m = stCandSt (closureIn containsP StCand stCandLen vecBar v m)

-- Named rather than applied inline: giving filter-prop its list argument
-- against the folded  St  keeps the elaborator from unfolding Ust.

stIsState : {v : Val} -> v ∈ St -> isState v ≡ true
stIsState m = filter-prop isState (allVecs (length (sub P))) m

-- Every member is a state, so (S1) and (S2) can be read off it.

ustState : {v : Val} -> v ∈ Ust -> isState v ≡ true
ustState m = stIsState (ustSt m)

ustSeed : {v : Val}
       -> v ∈ St -> valOf v P ≡ true -> v ∈ Ust
ustSeed m e = closureSeed containsP StCand stCandLen vecBar (stStCand m) e

ustClosed : {v w : Val}
         -> v ∈ Ust -> w ∈ St -> step v w ≡ true -> w ∈ Ust
ustClosed mv mw st =
  closureClosed containsP StCand stCandLen vecBar mv (stStCand mw) st
