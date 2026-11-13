{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.ShortPC -- Theorem 6.1 with the short certificate.
--
-- decidePC is decide with one word changed: where the provable branch of
-- LTL.Decide closes with stateComplete, this one closes with stateCompletePC.
-- Everything else -- the boolean satB (¬ Q) that chooses the branch, the
-- three cases of provableEach, the whole countermodel branch -- is the same
-- term, reused rather than copied.  That is what edit 2 of section 7 was for: the
-- content of the provable branch is provableEach, and it does not know which
-- proof of Lemma 2.6 stands beside it.
--
-- So decide and decidePC decide the same formulas the same way and differ only
-- in what they hand back on the inl branch, which is the comparison checkpoint
-- C6 makes in LTL.Proofs.
--
-- The countermodel branch is not merely unchanged, it is unchangeable: the
-- inr branch already denies derivability in the ELEVEN-constructor system,
-- since soundness (LTL.Sound) has a (PC) case.  Nothing about a certificate is
-- involved there -- the certificate is the lasso.

module LTL.ShortPC where

open import LTL.Decide     public
open import LTL.CompletePC public

------------------------------------------------------------------------
-- The branches, G34 of PHASE10-PLAN.md.
--
-- provableEach (LTL.Extract) puts every state of St (¬ Q) in one of three
-- positions, and two of them end at the same place: w does not contain ¬ Q,
-- however that was found out, so chi_w carries the literal ¬ ¬ Q and
-- (L2) then double negation give  chi_w ⇒ Q .  Those 67 constructors are, for
-- a formula whose elimination removes nothing, the WHOLE certificate apart
-- from two pc nodes -- 134 of the 139 for p ⇒ p -- and they are the last term
-- of the count that is neither constant nor linear-with-constant-one.
--
-- They are also propositional, and tautChi (LTL.Taut) says so: chi_w ⇒ Q is a
-- tautology of its own skeleton as soon as the bit at ¬ Q is false.  So the
-- two cases collapse to one pc node each and the certificate becomes
--
--     1 + 2 |St P| + 46 |□Args (sub P)| + 2
--
-- with the 2 |St P| being one pc node and one modus ponens per state.
--
-- The THIRD case is untouched and untouchable: the state was removed by the
-- elimination, and refuting it is extract, Theorem 4.1.  It is not a tautology
-- -- if it were, the temporal argument would be unnecessary -- and it is the
-- only part of a certificate that is about the temporal content at all.  So
-- what G34 does is exactly to remove the propositional padding from around it.
--
-- Additive, as Phase 9 was: provableEach and provable stay as they are, and
-- LTL.Proofs reports 82357 against 7 only because all three proofs are in the
-- development at once.

provableEachPC : (Q : Formula) -> satB (¬ Q) ≡ false
              -> (w : Val) -> w ∈ St (¬ Q)
              -> ⊢ (chi (¬ Q) w) ⇒ Q
provableEachPC Q e w m = outer (w ∈ᵛ Ust R) refl
  where
    R : Formula
    R = ¬ Q

    -- w does not contain R, however that was found out: one pc node
    fromR : valOf R w R ≡ false -> ⊢ (chi R w) ⇒ Q
    fromR ev = pc (tautChi Q w (stLen R m) ev)

    outer : (c : Bool) -> w ∈ᵛ Ust R ≡ c -> ⊢ (chi R w) ⇒ Q
    outer false ec = fromR (notIn (valOf R w R) refl)
      where
        notIn : (d : Bool) -> valOf R w R ≡ d -> valOf R w R ≡ false
        notIn false ed = ed
        notIn true  ed =
          emptyElim (∈ᵛ-false w (Ust R) ec (ustSeed R m ed))
    outer true  ec = go (w ∈ᵛ Uinf R) refl
      where
        mu : w ∈ Ust R
        mu = ∈ᵛ-sound w (Ust R) ec

        go : (b : Bool) -> w ∈ᵛ Uinf R ≡ b -> ⊢ (chi R w) ⇒ Q
        go true  eb =
          fromR (any-false (λ z -> valOf R z R) (Uinf R) e
                           (∈ᵛ-sound w (Uinf R) eb))
        go false eb =
          mp ¬Elim
             (extract R (filter-true (λ z -> ¬ᵇ (z ∈ᵛ Uinf R))
                                     (Ust R) mu (cong ¬ᵇ_ eb)))

-- G34's certificate, kept as a named term so that LTL.Proofs can put the whole
-- progression side by side.  It is the Phase 9 shape with the branches
-- shortened; provablePC below changes the SHAPE.

provableStPC : (Q : Formula) -> satB (¬ Q) ≡ false -> ⊢ Q
provableStPC Q e =
  mp (betaElimPC (¬ Q) (St (¬ Q)) (provableEachPC Q e))
     (stateCompletePC (¬ Q))

------------------------------------------------------------------------
-- The disjunction, cut down to the states that need it.
--
-- Everything above still quantifies over St (¬ Q) -- the case split, (L5),
-- and one branch per state -- because that is how Lemma 2.6 is stated.  But
-- after G34 two of the three cases of a branch are DECIDED rather than derived,
-- and a decided case need not be a case at all: it can be absorbed into the
-- decision.  What is genuinely needed from the state space is only the states
-- the elimination REMOVED, because those are the only ones whose branch is a
-- theorem about the temporal argument (extract, Theorem 4.1) rather than about
-- the skeleton.
--
-- So state the whole propositional part as one implication,
--
--     (S2 chain)  ⇒  ¬ chi_{w_1} ⇒ ... ⇒ ¬ chi_{w_k}  ⇒  Q
--
-- with w_1..w_k the REMOVED states and nothing else, and observe that it is a
-- tautology of its own skeleton.  The argument is betaSkel's, contraposed.
-- Take a row of the table satisfying the premises and suppose Q false; then
-- ¬ Q is true under that row, so the vector the row induces -- skelVec, a
-- state because the (S2) premises hold -- contains ¬ Q.  Where can it be?
-- Not outside Ust (¬ Q), by ustSeed; not inside Uinf (¬ Q), because satB
-- says no survivor contains ¬ Q.  So it is one of the w_i, and then its own
-- premise  ¬ chi_{w_i}  is false at that very row, since chiRowTrue says a
-- row satisfies the chi of the state it induces.  Contradiction.
--
-- What that removes is everything the state space was costing:
--
--     beta and (L5)          gone -- there is no disjunction any more
--     one branch per state   gone for every state except the removed ones
--     mp ¬Elim per state   gone -- the premise IS ¬ chi_w, which is what
--                                    extract proves, so it is applied directly
--
-- and the count becomes
--
--     1  +  46 |□Args (sub P)|  +  sum over removed w of (1 + |extract w|)
--
-- with NOTHING indexed by |St P| at all.  For a formula whose elimination
-- removes nothing -- and p ⇒ p, □ p ⇒ p and □ □ p ⇒ □ p are all of
-- that kind, since no state contains their negations -- the certificate is
--
--     1 + 46 |□Args (sub P)|
--
-- i.e. ONE (PC) node for p ⇒ p.  That is the honest end of this line of
-- shortening: what is left is Lemma 2.6's chain of (T), one instance per
-- eventuality, plus Theorem 4.1 once per state the temporal argument actually
-- eliminated.  Nothing propositional survives except the single decided line.

¬Chi : Formula -> Val -> Formula
¬Chi P w = ¬ (chi P w)

-- The certificate formula over the REMOVED states (see above).

removedFml : Formula -> Formula
removedFml Q = ⇒List (s2List (¬ Q))
                   (⇒List (map (¬Chi (¬ Q)) (removed (¬ Q))) Q)

tautRemoved : (Q : Formula) -> satB (¬ Q) ≡ false -> isTaut (removedFml Q) ≡ true
tautRemoved Q e =
  all-intro (λ a -> valFrom Ats a (removedFml Q))
            (allVecs (length Ats)) row
  where
    R : Formula
    R = ¬ Q

    Ats : List Formula
    Ats = atomsOf (removedFml Q)

    row : {a : Val} -> a ∈ allVecs (length Ats)
       -> valFrom Ats a (removedFml Q) ≡ true
    row {a} m =
      □Chain Ats a (□Args (sub R))
               (⇒List (map (¬Chi R) (removed R)) Q) outer
      where
        outer : S2At Ats a (□Args (sub R))
             -> valFrom Ats a (⇒List (map (¬Chi R) (removed R)) Q) ≡ true
        outer s2 = ⇒Chain Ats a (map (¬Chi R) (removed R)) Q inner
          where
            boxOk : □Ok Ats a R
            boxOk B mb = s2 B (□Args-of (sub R) mb)

            -- the state the row induces
            w : Val
            w = skelVec Ats a R

            mSt : w ∈ St R
            mSt = memStSkel Ats a R boxOk

            inner : ({X : Formula} -> X ∈ map (¬Chi R) (removed R)
                       -> valFrom Ats a X ≡ true)
                 -> valFrom Ats a Q ≡ true
            inner prem = onQ (valFrom Ats a Q) refl
              where
                onQ : (b : Bool) -> valFrom Ats a Q ≡ b
                   -> valFrom Ats a Q ≡ true
                onQ true  eq = eq
                onQ false eq = emptyElim bad
                  where
                    -- so the row makes ¬ Q true, and w contains ¬ Q
                    ev : valOf R w R ≡ true
                    ev = trans (valOfSkelVec R Ats a R (sub-self R)) (cong ¬ᵇ_ eq)

                    -- w joined the search, by ustSeed
                    mUst : w ∈ Ust R
                    mUst = ustSeed R mSt ev

                    -- and did not survive it, because satB is false
                    notUinf : w ∈ᵛ Uinf R ≡ false
                    notUinf = onU (w ∈ᵛ Uinf R) refl
                      where
                        onU : (b : Bool) -> w ∈ᵛ Uinf R ≡ b
                           -> w ∈ᵛ Uinf R ≡ false
                        onU false eu = eu
                        onU true  eu =
                          emptyElim (true≢false (trans (sym ev)
                            (any-false (λ z -> valOf R z R) (Uinf R) e
                                       (∈ᵛ-sound w (Uinf R) eu))))

                    mRem : w ∈ removed R
                    mRem = filter-true (λ z -> ¬ᵇ (z ∈ᵛ Uinf R)) (Ust R)
                                       mUst (cong ¬ᵇ_ notUinf)

                    -- but then its own premise denies the chi of the row that
                    -- built it, which chiRowTrue affirms
                    bad : Empty
                    bad =
                      true≢false (trans (sym (chiRowTrue Ats a (sub R)))
                                        (notTrue (valFrom Ats a (chi R w))
                                                 (prem (memMap (¬Chi R) mRem))))

-- one modus ponens per removed state, against Theorem 4.1.  Same shape as
-- mpChain and mpVals, and for the same reason: the instances are consumed as
-- they are met, so there is no propositional glue.

mpRemoved : (P : Formula) (ws : List Val) {C : Formula}
         -> ((w : Val) -> w ∈ ws -> ⊢ ¬ (chi P w))
         -> ⊢ ⇒List (map (¬Chi P) ws) C -> ⊢ C
mpRemoved P []       h d = d
mpRemoved P (w ∷ ws) h d = mpRemoved P ws (λ z m -> h z (there m)) (mp d (h w here))

------------------------------------------------------------------------
-- Theorem 6.1 again

provablePC : (Q : Formula) -> satB (¬ Q) ≡ false -> ⊢ Q
provablePC Q e =
  mpRemoved (¬ Q) (removed (¬ Q)) (λ w m -> extract (¬ Q) m)
            (mpChain (□Args (sub (¬ Q))) (pc (tautRemoved Q e)))

decidePC : (Q : Formula) -> ⊢ Q ⊎ LassoCountermodel Q
decidePC Q = onSat (satB (¬ Q)) refl
  where
    fromSig : (Σ[ v ∈ Val ] v ∈ Uinf (¬ Q) ×
                                valOf (¬ Q) v (¬ Q) ≡ true)
           -> ⊢ Q ⊎ LassoCountermodel Q
    fromSig (v0 , m , ev) = inr (buildCM Q v0 m ev)

    onSat : (x : Bool) -> satB (¬ Q) ≡ x
         -> ⊢ Q ⊎ LassoCountermodel Q
    onSat false e = inl (provablePC Q e)
    onSat true  e =
      fromSig (any-true (λ v -> valOf (¬ Q) v (¬ Q)) (Uinf (¬ Q)) e)

------------------------------------------------------------------------
-- Counting it.
--
-- The same four numbers as countOf (LTL.Decide) -- size, modus ponens,
-- generalisations, (Ind) -- so that the two are comparable line by line, and
-- one more that only the new system can have: how many nodes are (PC).

derivPC : {A : Formula} -> ⊢ A -> Nat
derivPC p1  = 0
derivPC p2  = 0
derivPC p3  = 0
derivPC k□  = 0
derivPC k○  = 0
derivPC exp = 0
derivPC ind = 0
derivPC lin = 0
derivPC (pc e)   = 1
derivPC (mp d e) = derivPC d + derivPC e
derivPC (gen d)  = derivPC d

countOfPC : (Q : Formula) -> Nat × Nat × Nat × Nat
countOfPC Q = onDec (decidePC Q)
  where
    onDec : ⊢ Q ⊎ LassoCountermodel Q
         -> Nat × Nat × Nat × Nat
    onDec (inl d) =
      derivSize d , derivMP d , derivGen d , derivInd d
    onDec (inr c) = zero , zero , zero , zero

pcCountOf : (Q : Formula) -> Nat
pcCountOf Q = onDec (decidePC Q)
  where
    onDec : ⊢ Q ⊎ LassoCountermodel Q -> Nat
    onDec (inl d) = derivPC d
    onDec (inr c) = zero

------------------------------------------------------------------------
-- Checkpoints.
--
-- The two formulas of C4 are still decided in the affirmative, and by the same
-- boolean: what changed is the size of the answer, not the answer.

decidePC-benAri : isProof (decidePC benAri) ≡ true
decidePC-benAri = refl

decidePC-bnb : isProof (decidePC bnb) ≡ true
decidePC-bnb = refl

decidePC-◇P : isProof (decidePC ◇P) ≡ false
decidePC-◇P = refl

------------------------------------------------------------------------
-- G35 of PHASE10-PLAN.md: chi over atoms.
--
-- chi P v lists a literal for every position of Sub P, but (S1) determines the
-- bits at ¬ and ⇒ from the bits at the atoms, so the non-atomic literals
-- are redundant: for ¬ axK5fwd that is 22 conjuncts where 8 would do.  chiA
-- keeps only the atomic ones.
--
-- The bridge is ONE (PC) node and not an induction with (S1) as a derivation,
-- which is what PHASE10-PLAN.md expected.  The reason is skelAgree (LTL.Taut):
-- a row of the skeleton table that agrees with a state on the atoms agrees with
-- it everywhere, so  chiA_v ⇒ chi_v  holds under every row and is therefore a
-- tautology of its own skeleton.  Stated contraposed, since what extract hands
-- over is ¬ (chi_v) and what the certificate wants is ¬ (chiA_v), it is
--
--     ¬ chi_v  ⇒  ¬ chiA_v
--
-- and one modus ponens applies it.
--
-- This is the one place in the phase where the trade goes the OTHER way, and
-- LTL.Proofs measures it: the main line gets much shorter, but each bridge is a
-- new pc node whose own side condition mentions chi again, so the total work of
-- CHECKING goes up.  Both certificates are therefore kept, and decidePC uses
-- the short-to-check one.

chiA : Formula -> Val -> Formula
chiA P v = ⋀ (litList (atoms (sub P)) (atomBits P v))

¬ChiA : Formula -> Val -> Formula
¬ChiA P v = ¬ (chiA P v)

-- a row making chiA true makes chi true, for a state v

chiABridge : (P : Formula) (v : Val) -> isState P v ≡ true
          -> length v ≡ length (sub P)
          -> (Ats : List Formula) (a : Val)
          -> valFrom Ats a (chiA P v) ≡ true
          -> valFrom Ats a (chi P v) ≡ true
chiABridge P v st len Ats a ec =
  subst (λ u -> valFrom Ats a (chi P u) ≡ true) (mkV-id P v st len) full
  where
    ok : allOk P v (sub P) ≡ true
    ok = andTrueL (allOk P v (sub P)) (allCoh P v (length (sub P))) st

    atomAg : (X : Formula) -> X ∈ sub P -> isAtomB X ≡ true
          -> valFrom Ats a X ≡ valOf P v X
    atomAg X mX aX =
      litSound Ats a X (valOf P v X)
               (⋀ProjTrue Ats a (litList (atoms (sub P)) (atomBits P v))
                             (litMapMem (valOf P v) (atoms (sub P))
                                        (∈ᶠ-sound (atoms (sub P)) X
                                                  (atomMem (sub P) mX aX)))
                             ec)

    full : valFrom Ats a (chi P (mkV P (atomBits P v))) ≡ true
    full =
      ⋀True Ats a (litList (sub P) (mkV P (atomBits P v)))
               (litMapOk Ats a (valFrom (atoms (sub P)) (atomBits P v)) (sub P)
                         (λ A mA -> trans (skelAgree Ats a P v ok atomAg A mA)
                                          (sym (valFromEq P v ok A mA))))

tautBridge : (P : Formula) (v : Val) -> isState P v ≡ true
          -> length v ≡ length (sub P)
          -> isTaut (¬ (chi P v) ⇒ (¬ChiA P v)) ≡ true
tautBridge P v st len =
  all-intro (λ a -> valFrom Ats a F) (allVecs (length Ats)) row
  where
    F : Formula
    F = ¬ (chi P v) ⇒ (¬ChiA P v)

    Ats : List Formula
    Ats = atomsOf F

    row : {a : Val} -> a ∈ allVecs (length Ats) -> valFrom Ats a F ≡ true
    row {a} m = boolContra (valFrom Ats a (chi P v)) (valFrom Ats a (chiA P v))
                           (chiABridge P v st len Ats a)

------------------------------------------------------------------------
-- and the certificate over chiA

removedFmlA : Formula -> Formula
removedFmlA Q = ⇒List (s2List (¬ Q))
                    (⇒List (map (¬ChiA (¬ Q)) (removed (¬ Q))) Q)

tautRemovedA : (Q : Formula) -> satB (¬ Q) ≡ false
            -> isTaut (removedFmlA Q) ≡ true
tautRemovedA Q e =
  all-intro (λ a -> valFrom Ats a (removedFmlA Q)) (allVecs (length Ats)) row
  where
    R : Formula
    R = ¬ Q

    Ats : List Formula
    Ats = atomsOf (removedFmlA Q)

    row : {a : Val} -> a ∈ allVecs (length Ats)
       -> valFrom Ats a (removedFmlA Q) ≡ true
    row {a} m =
      □Chain Ats a (□Args (sub R))
               (⇒List (map (¬ChiA R) (removed R)) Q) outer
      where
        outer : S2At Ats a (□Args (sub R))
             -> valFrom Ats a (⇒List (map (¬ChiA R) (removed R)) Q) ≡ true
        outer s2 = ⇒Chain Ats a (map (¬ChiA R) (removed R)) Q inner
          where
            boxOk : □Ok Ats a R
            boxOk B mb = s2 B (□Args-of (sub R) mb)

            w : Val
            w = skelVec Ats a R

            mSt : w ∈ St R
            mSt = memStSkel Ats a R boxOk

            -- the row satisfies the chiA of the state it induces
            chiARow : valFrom Ats a (chiA R w) ≡ true
            chiARow =
              ⋀True Ats a (litList (atoms (sub R)) (atomBits R w))
                       (litMapOk Ats a (valOf R w) (atoms (sub R))
                                 (λ X mX ->
                                    sym (valOfSkelVec R Ats a X (atomsIn (sub R) mX))))

            inner : ({X : Formula} -> X ∈ map (¬ChiA R) (removed R)
                       -> valFrom Ats a X ≡ true)
                 -> valFrom Ats a Q ≡ true
            inner prem = onQ (valFrom Ats a Q) refl
              where
                onQ : (b : Bool) -> valFrom Ats a Q ≡ b
                   -> valFrom Ats a Q ≡ true
                onQ true  eq = eq
                onQ false eq = emptyElim bad
                  where
                    ev : valOf R w R ≡ true
                    ev = trans (valOfSkelVec R Ats a R (sub-self R)) (cong ¬ᵇ_ eq)

                    mUst : w ∈ Ust R
                    mUst = ustSeed R mSt ev

                    notUinf : w ∈ᵛ Uinf R ≡ false
                    notUinf = onU (w ∈ᵛ Uinf R) refl
                      where
                        onU : (b : Bool) -> w ∈ᵛ Uinf R ≡ b
                           -> w ∈ᵛ Uinf R ≡ false
                        onU false eu = eu
                        onU true  eu =
                          emptyElim (true≢false (trans (sym ev)
                            (any-false (λ z -> valOf R z R) (Uinf R) e
                                       (∈ᵛ-sound w (Uinf R) eu))))

                    mRem : w ∈ removed R
                    mRem = filter-true (λ z -> ¬ᵇ (z ∈ᵛ Uinf R)) (Ust R)
                                       mUst (cong ¬ᵇ_ notUinf)

                    bad : Empty
                    bad =
                      true≢false (trans (sym chiARow)
                                        (notTrue (valFrom Ats a (chiA R w))
                                                 (prem (memMap (¬ChiA R) mRem))))

mpRemovedA : (P : Formula) (ws : List Val) {C : Formula}
          -> ((w : Val) -> w ∈ ws -> ⊢ ¬ChiA P w)
          -> ⊢ ⇒List (map (¬ChiA P) ws) C -> ⊢ C
mpRemovedA P []       h d = d
mpRemovedA P (w ∷ ws) h d = mpRemovedA P ws (λ z m -> h z (there m)) (mp d (h w here))

provablePCA : (Q : Formula) -> satB (¬ Q) ≡ false -> ⊢ Q
provablePCA Q e =
  mpRemovedA (¬ Q) (removed (¬ Q)) each
             (mpChain (□Args (sub (¬ Q))) (pc (tautRemovedA Q e)))
  where
    R : Formula
    R = ¬ Q

    each : (w : Val) -> w ∈ removed R -> ⊢ ¬ChiA R w
    each w m = mp (pc (tautBridge R w (stIsState R mSt) (stLen R mSt)))
                  (extract R m)
      where
        mSt : w ∈ St R
        mSt = ustSt R (filter-sub (λ z -> ¬ᵇ (z ∈ᵛ Uinf R)) (Ust R) m)
