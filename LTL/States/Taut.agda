{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.States.Taut -- Boolean facts about how the skeleton evaluation valFrom
-- reads lit, ⋀, ⋁, chi and beta.  They are the side conditions of the pc
-- nodes built in LTL.Procedures.CompletePC and LTL.Procedures.Decide.  The
-- one derivation here is mpChain, which discharges the premises of □Chain.
--
-- Every lemma fixes one atom list Ats and one row a.  valFrom depends on Ats,
-- so readings under different atom lists are unrelated, and each caller uses
-- atomsOf of the one formula its pc node proves.  (The mkV lemmas of
-- LTL.States.Closure use atoms (sub P), a different list, and do not apply.)
--
-- The central fact: skelVec Ats a P = map (valFrom Ats a) (sub P) is a state
-- of P as soon as the (S2) instances hold in row a.  (S1) and coherence are
-- free, since valFrom is compositional on ¬ and ⇒ by definition.  So beta P
-- (St P) is true in every row satisfying (S2), which is state completeness as
-- a Boolean fact.

module LTL.States.Taut where

open import LTL.States.Common

-- Taut states its lemmas for any formula P, so it opens State unapplied, and
-- privately: a P-module that opens Taut has State at its own P.
open import LTL.States.State

------------------------------------------------------------------------
-- Membership, as a boolean: what turns a membership proof into the side
-- condition of atomLook.

∈ᶠ-mem : (As : List Formula) {A : Formula} -> A ∈ As -> A ∈ᶠ As ≡ true
∈ᶠ-mem []       ()
∈ᶠ-mem (B ∷ Bs) here     = ∨ᵇ-introˡ (B ≡ᶠ B) (B ∈ᶠ Bs) (≡ᶠ-refl B)
∈ᶠ-mem (B ∷ Bs) {A} (there m) =
  ∨ᵇ-introʳ (B ≡ᶠ A) (A ∈ᶠ Bs) (∈ᶠ-mem Bs m)

------------------------------------------------------------------------
-- The skeleton reads ∨ and ∧ as expected.  C ∨ D is ¬ C ⇒ D and C ∧ D is
-- ¬ (C ⇒ ¬ D), so these are Boolean identities, stated at the shapes the
-- list constructions produce.

skel∨Inl : (x y : Bool) -> x ≡ true -> ¬ᵇ x ⇒ᵇ y ≡ true
skel∨Inl true  y e = refl
skel∨Inl false y ()

skel∧Intro : (x y : Bool) -> x ≡ true -> y ≡ true
          -> ¬ᵇ (x ⇒ᵇ ¬ᵇ y) ≡ true
skel∧Intro true  true  e1 e2 = refl
skel∧Intro true  false e1 ()
skel∧Intro false y     () e2

------------------------------------------------------------------------
-- ⋁ is true as soon as one disjunct is, ⋀ as soon as all conjuncts are.  The
-- empty ⋀ is ⊤, which is  var 0 ⇒ var 0  and true whatever the row says.

⋁True : (Ats : List Formula) (a : Val) (Cs : List Formula) {C : Formula}
     -> C ∈ Cs -> valFrom Ats a C ≡ true
     -> valFrom Ats a (⋁ Cs) ≡ true
⋁True Ats a []       ()       e
⋁True Ats a (D ∷ Cs) here     e =
  skel∨Inl (valFrom Ats a D) (valFrom Ats a (⋁ Cs)) e
⋁True Ats a (D ∷ Cs) (there m) e =
  ⇒ᵇ-const (¬ᵇ valFrom Ats a D) (valFrom Ats a (⋁ Cs))
           (⋁True Ats a Cs m e)

⋀True : (Ats : List Formula) (a : Val) (Cs : List Formula)
     -> ({C : Formula} -> C ∈ Cs -> valFrom Ats a C ≡ true)
     -> valFrom Ats a (⋀ Cs) ≡ true
⋀True Ats a []       h = ⇒ᵇ-refl (valFrom Ats a (var zero))
⋀True Ats a (D ∷ Cs) h =
  skel∧Intro (valFrom Ats a D) (valFrom Ats a (⋀ Cs))
             (h here) (⋀True Ats a Cs (λ m -> h (there m)))

------------------------------------------------------------------------
-- The chi of the row the assignment itself gives is true: its literals are
-- true one by one.  This is the witness disjunct for the tautologies of
-- LTL.Procedures.CompletePC.

litTrue : (Ats : List Formula) (a : Val) (A : Formula)
       -> valFrom Ats a (lit A (valFrom Ats a A)) ≡ true
litTrue Ats a A with valFrom Ats a A in e
... | true  = e
... | false = cong ¬ᵇ_ e

litListTrue : (Ats : List Formula) (a : Val) (As : List Formula) {C : Formula}
           -> C ∈ litList As (map (valFrom Ats a) As)
           -> valFrom Ats a C ≡ true
litListTrue Ats a []       ()
litListTrue Ats a (A ∷ As) here      = litTrue Ats a A
litListTrue Ats a (A ∷ As) (there m) = litListTrue Ats a As m

chiRowTrue : (Ats : List Formula) (a : Val) (As : List Formula)
          -> valFrom Ats a (⋀ (litList As (map (valFrom Ats a) As))) ≡ true
chiRowTrue Ats a As =
  ⋀True Ats a (litList As (map (valFrom Ats a) As))
           (λ m -> litListTrue Ats a As m)

------------------------------------------------------------------------
-- The bridge: the vector a truth-table row gives, read by valOf.  skelVec is
-- mkV of LTL.States.Closure with the atom list left free; valOfSkelVec is
-- atomLook (LTL.Syntax.Skel), needing only that the formula occurs.

skelVec : List Formula -> Val -> Formula -> Val
skelVec Ats a P = map (valFrom Ats a) (sub P)

valOfSkelVec : (P : Formula) (Ats : List Formula) (a : Val) (A : Formula)
            -> A ∈ sub P
            -> valOf P (skelVec Ats a P) A ≡ valFrom Ats a A
valOfSkelVec P Ats a A m =
  atomLook (valFrom Ats a) (sub P) A (∈ᶠ-mem (sub P) m)

------------------------------------------------------------------------
-- skelVec is a state, given (S2).  (S1) and coherence hold because the bit at
-- A is valFrom's reading of A (valOfSkelVec), and valFrom is ¬ᵇ at ¬ and ⇒ᵇ
-- at ⇒.  (S2) does not hold in an arbitrary row, since □ A and A are
-- independent atoms; it is assumed, as □Ok, and the caller pays for it.

-- The instance □ A ⇒ A of (S2) as a formula.

s2Fml : Formula -> Formula
s2Fml A = □ A ⇒ A

□Ok : List Formula -> Val -> Formula -> Set
□Ok Ats a P = (B : Formula) -> □ B ∈ sub P
             -> valFrom Ats a (□ B) ⇒ᵇ valFrom Ats a B ≡ true

okAtSkel : (Ats : List Formula) (a : Val) (P : Formula) (A : Formula)
        -> A ∈ sub P -> □Ok Ats a P
        -> okAt P (skelVec Ats a P) A ≡ true
okAtSkel Ats a P (var n) m boxOk = refl
okAtSkel Ats a P (○ B)   m boxOk = refl
okAtSkel Ats a P (¬ B)   m boxOk =
  ⇔ᵇ-complete (valOf P (skelVec Ats a P) (¬ B))
              (¬ᵇ valOf P (skelVec Ats a P) B)
              (trans (valOfSkelVec P Ats a (¬ B) m)
                     (cong ¬ᵇ_
                           (sym (valOfSkelVec P Ats a B (sub-¬ P m)))))
okAtSkel Ats a P (B ⇒ C) m boxOk =
  ⇔ᵇ-complete (valOf P (skelVec Ats a P) (B ⇒ C))
              (valOf P (skelVec Ats a P) B ⇒ᵇ valOf P (skelVec Ats a P) C)
              (trans (valOfSkelVec P Ats a (B ⇒ C) m)
                     (cong₂ _⇒ᵇ_
                            (sym (valOfSkelVec P Ats a B (sub-⇒L P m)))
                            (sym (valOfSkelVec P Ats a C (sub-⇒R P m)))))
okAtSkel Ats a P (□ B)   m boxOk =
  trans (cong₂ _⇒ᵇ_ (valOfSkelVec P Ats a (□ B) m)
                    (valOfSkelVec P Ats a B (sub-□ P m)))
        (boxOk B m)

allOkSkel : (Ats : List Formula) (a : Val) (P : Formula) (As : List Formula)
         -> ({A : Formula} -> A ∈ As -> A ∈ sub P) -> □Ok Ats a P
         -> allOk P (skelVec Ats a P) As ≡ true
allOkSkel Ats a P As sb boxOk =
  all-intro (okAt P (skelVec Ats a P)) As
            (λ {A} m -> okAtSkel Ats a P A (sb m) boxOk)

-- Coherence.  The bit at position i is the skeleton's reading of the formula
-- there (nth-map), and so is the bit at that formula's first occurrence
-- (valOfSkelVec), so the two agree.

cohAtSkel : (Ats : List Formula) (a : Val) (P : Formula) (i : Nat)
         -> i < length (sub P)
         -> cohAt P (skelVec Ats a P) i ≡ true
cohAtSkel Ats a P i l =
  ⇔ᵇ-complete (bitAt (skelVec Ats a P) i)
              (valOf P (skelVec Ats a P) (nth (sub P) i ⊥))
              (trans (nth-map (valFrom Ats a) (sub P) i l ⊥ false)
                     (sym (valOfSkelVec P Ats a (nth (sub P) i ⊥)
                                        (nth-mem (sub P) i l ⊥))))

allCohSkel : (Ats : List Formula) (a : Val) (P : Formula) (n : Nat)
          -> ((i : Nat) -> i < n -> i < length (sub P))
          -> allCoh P (skelVec Ats a P) n ≡ true
allCohSkel Ats a P zero    h = refl
allCohSkel Ats a P (suc n) h =
  ∧ᵇ-intro (cohAt P (skelVec Ats a P) n) (allCoh P (skelVec Ats a P) n)
           (cohAtSkel Ats a P n (h n (ltNSucN n)))
           (allCohSkel Ats a P n (λ i l -> h i (ltWeak l)))

isStateSkel : (Ats : List Formula) (a : Val) (P : Formula) -> □Ok Ats a P
           -> isState P (skelVec Ats a P) ≡ true
isStateSkel Ats a P boxOk =
  ∧ᵇ-intro (allOk P (skelVec Ats a P) (sub P))
           (allCoh P (skelVec Ats a P) (length (sub P)))
           (allOkSkel Ats a P (sub P) (λ m -> m) boxOk)
           (allCohSkel Ats a P (length (sub P)) (λ i l -> l))

memStSkel : (Ats : List Formula) (a : Val) (P : Formula) -> □Ok Ats a P
         -> skelVec Ats a P ∈ St P
memStSkel Ats a P boxOk =
  filter-true (isState P) (allVecs (length (sub P)))
              (allVecs-complete (length (sub P)) (skelVec Ats a P)
                                (map-length (valFrom Ats a) (sub P)))
              (isStateSkel Ats a P boxOk)

------------------------------------------------------------------------
-- Hence beta P (St P) is true in any row satisfying (S2): chi P (skelVec Ats
-- a P) is a disjunct (memStSkel) and is true (chiRowTrue).
-- LTL.Procedures.CompletePC turns this into a one-node derivation.

betaSkel : (Ats : List Formula) (a : Val) (P : Formula) -> □Ok Ats a P
        -> valFrom Ats a (beta P (St P)) ≡ true
betaSkel Ats a P boxOk =
  ⋁True Ats a (map (chi P) (St P))
           (memMap (chi P) (memStSkel Ats a P boxOk))
           (chiRowTrue Ats a (sub P))

------------------------------------------------------------------------
-- The (S2) instances, discharged one at a time.
--
-- (S2) is assumed above, so it is a premise of the formula the pc node
-- proves.  It is an implication chain rather than a conjunction: a conjunction
-- is built by (L2) through ∧Pair, about 239 constructors per instance of (T),
-- while each premise of a chain is discharged by one modus ponens.  The
-- certificate is then  |□Args (sub P)| * (1 + |□Elim|) + 1  exactly.
--
-- ⇒Chain says that reading a chain as true is assuming its premises; □Chain is
-- that at the (S2) instances.  The caller turns a box-subformula into a member
-- with □Args-of.

⇒List : List Formula -> Formula -> Formula
⇒List []       C = C
⇒List (A ∷ As) C = A ⇒ (⇒List As C)

⇒Chain : (Ats : List Formula) (a : Val) (As : List Formula) (C : Formula)
      -> ((({A : Formula} -> A ∈ As -> valFrom Ats a A ≡ true)
            -> valFrom Ats a C ≡ true))
      -> valFrom Ats a (⇒List As C) ≡ true
⇒Chain Ats a []       C h = h (λ ())
⇒Chain Ats a (A ∷ As) C h =
  ⇒ᵇ-intro (valFrom Ats a A) (valFrom Ats a (⇒List As C))
           (λ eA -> ⇒Chain Ats a As C (λ g -> h (more eA g)))
  where
    more : valFrom Ats a A ≡ true
        -> ({X : Formula} -> X ∈ As -> valFrom Ats a X ≡ true)
        -> {X : Formula} -> X ∈ A ∷ As -> valFrom Ats a X ≡ true
    more eA g here      = eA
    more eA g (there m) = g m

-- (S2) holds in row a at each B of As: □ B true implies B true.

S2At : List Formula -> Val -> List Formula -> Set
S2At Ats a As = ∀[ B ∈ As ] valFrom Ats a (□ B) ⇒ᵇ valFrom Ats a B ≡ true

□Chain : (Ats : List Formula) (a : Val) (As : List Formula) (C : Formula)
      -> (S2At Ats a As -> valFrom Ats a C ≡ true)
      -> valFrom Ats a (⇒List (map s2Fml As) C) ≡ true
□Chain Ats a As C h =
  ⇒Chain Ats a (map s2Fml As) C (λ g -> h (λ B mB -> g (memMap s2Fml mB)))

------------------------------------------------------------------------
-- (L5), as a boolean.
--
-- ⋁Elim (LTL.Rules.PropList) derives  (C1 ∨ ... ∨ Cn) ⇒ C  from the n
-- implications at about 426 constructors per disjunct, which would dominate a
-- certificate.  The implication is a tautology of its skeleton, so it can be
-- one pc node with the n branches discharged by modus ponens (betaElimPC).
-- This is its truth: walk the disjunction to a true disjunct and use the
-- premise there.

infixl 20 _⇐_

_⇐_ : Formula -> Formula -> Formula
C ⇐ D = D ⇒ C

⋁ElimTrue : (Ats : List Formula) (a : Val) (Cs : List Formula) (C : Formula)
         -> ({D : Formula} -> D ∈ Cs
               -> valFrom Ats a (C ⇐ D) ≡ true)
         -> valFrom Ats a (⋁ Cs ⇒ C) ≡ true
⋁ElimTrue Ats a Cs C h =
  ⇒ᵇ-intro (valFrom Ats a (⋁ Cs)) (valFrom Ats a C) (go Cs h)
  where
    go : (Ds : List Formula)
      -> ({D : Formula} -> D ∈ Ds -> valFrom Ats a (C ⇐ D) ≡ true)
      -> valFrom Ats a (⋁ Ds) ≡ true -> valFrom Ats a C ≡ true
    go []        k e =
      emptyElim (true≢false (trans (sym e)
                                   (cong ¬ᵇ_
                                         (⇒ᵇ-refl (valFrom Ats a (var zero))))))
    go (D ∷ Ds) k e with valFrom Ats a D in eb
    ... | true  = ⇒ᵇ-mp (valFrom Ats a D) (valFrom Ats a C) (k here) eb
    -- with D false, e already says that ⋁ Ds holds
    ... | false = go Ds (λ m -> k (there m)) e

------------------------------------------------------------------------
-- A state not containing ¬ Q, as one node.
--
-- For a state w of ¬ Q with the bit at ¬ Q false,  chi_w ⇒ Q  is a skeleton
-- tautology: chi_w has the conjunct  lit (¬ Q) false = ¬ ¬ Q , and valFrom is
-- ¬ᵇ at ¬.  So (PC) proves it in one node where projecting and cancelling the
-- double negation takes 67 constructors.

------------------------------------------------------------------------
-- ∧, read out: a projection needs the two eliminations (skel∧Intro above is
-- the introduction).

skel∧Fst : (x y : Bool) -> ¬ᵇ (x ⇒ᵇ ¬ᵇ y) ≡ true
        -> x ≡ true
skel∧Fst true  y e = refl
skel∧Fst false y ()

skel∧Snd : (x y : Bool) -> ¬ᵇ (x ⇒ᵇ ¬ᵇ y) ≡ true
        -> y ≡ true
skel∧Snd true  true  e = refl
skel∧Snd true  false ()
skel∧Snd false y     ()

-- the converse of ⋀True: a true conjunction has true conjuncts

⋀ProjTrue : (Ats : List Formula) (a : Val) (Cs : List Formula) {C : Formula}
         -> C ∈ Cs -> valFrom Ats a (⋀ Cs) ≡ true
         -> valFrom Ats a C ≡ true
⋀ProjTrue Ats a []       ()       e
⋀ProjTrue Ats a (D ∷ Cs) here     e =
  skel∧Fst (valFrom Ats a D) (valFrom Ats a (⋀ Cs)) e
⋀ProjTrue Ats a (D ∷ Cs) (there m) e =
  ⋀ProjTrue Ats a Cs m
               (skel∧Snd (valFrom Ats a D) (valFrom Ats a (⋀ Cs)) e)

------------------------------------------------------------------------
-- The literal of P itself inside chi P w.  sub P begins with P, and P ≡ᶠ P is
-- true, so indexOf finds it at position zero, where sub-self points.

idxSelf : (P : Formula) -> indexOf (sub P) P ≡ index (sub-self P)
idxSelf (var n) = cong (λ b -> indexOfCons b (indexOf [] (var n))) (≡ᶠ-refl (var n))
idxSelf (¬ A)   = cong (λ b -> indexOfCons b (indexOf (sub A) (¬ A))) (≡ᶠ-refl (¬ A))
idxSelf (A ⇒ B) =
  cong (λ b -> indexOfCons b (indexOf (sub A ++ sub B) (A ⇒ B)))
       (≡ᶠ-refl (A ⇒ B))
idxSelf (○ A)   = cong (λ b -> indexOfCons b (indexOf (sub A) (○ A))) (≡ᶠ-refl (○ A))
idxSelf (□ A)   = cong (λ b -> indexOfCons b (indexOf (sub A) (□ A))) (≡ᶠ-refl (□ A))

litSelf : (P : Formula) (w : Val) -> length w ≡ length (sub P)
       -> lit P (valOf P w P) ∈ litList (sub P) w
litSelf P w len =
  subst (λ n -> lit P (bitAt w n) ∈ litList (sub P) w)
        (sym (idxSelf P))
        (litList-mem (sub P) w len (sub-self P))

------------------------------------------------------------------------
-- chi_w ⇒ Q is a skeleton tautology when w does not contain ¬ Q.

tautChi : (Q : Formula) (w : Val) -> length w ≡ length (sub (¬ Q))
       -> valOf (¬ Q) w (¬ Q) ≡ false
       -> isTaut ((chi (¬ Q) w) ⇒ Q) ≡ true
tautChi Q w len ev =
  all-intro (λ a -> valFrom Ats a F) (allVecs (length Ats)) row
  where
    R : Formula
    R = ¬ Q

    F : Formula
    F = (chi R w) ⇒ Q

    Ats : List Formula
    Ats = atomsOf F

    -- the conjunct  lit R false , i.e.  ¬ ¬ Q
    mneg : ¬ R ∈ litList (sub R) w
    mneg = subst (λ b -> lit R b ∈ litList (sub R) w) ev (litSelf R w len)

    row : {a : Val} -> a ∈ allVecs (length Ats)
       -> valFrom Ats a F ≡ true
    row {a} m = ⇒ᵇ-intro (valFrom Ats a (chi R w)) (valFrom Ats a Q) step
      where
        step : valFrom Ats a (chi R w) ≡ true -> valFrom Ats a Q ≡ true
        step ec =
          ¬ᵇ¬ᵇ-true (valFrom Ats a Q)
                    (⋀ProjTrue Ats a (litList (sub R) w) mneg ec)

------------------------------------------------------------------------
-- The derivation half of □Chain: one modus ponens against one instance of
-- (T) per premise, left to right.

mpChain : (As : List Formula) {C : Formula}
       -> ⊢ ⇒List (map s2Fml As) C -> ⊢ C
mpChain []       d = d
mpChain (A ∷ As) d = mpChain As (mp d □Elim)

------------------------------------------------------------------------
-- The implication behind (L5),
--
--     (C1 ⇒ C) ⇒ ... ⇒ (Cn ⇒ C) ⇒ ((C1 ∨ ... ∨ Cn) ⇒ C),
--
-- is a tautology of its skeleton.

⋁⇒Fml : List Formula -> Formula -> Formula
⋁⇒Fml Cs C = ⇒List (map (C ⇐_) Cs) (⋁ Cs ⇒ C)

taut⋁Elim : (Cs : List Formula) (C : Formula)
         -> isTaut (⋁⇒Fml Cs C) ≡ true
taut⋁Elim Cs C =
  all-intro (λ a -> valFrom (atomsOf (⋁⇒Fml Cs C)) a (⋁⇒Fml Cs C))
            (allVecs (length (atomsOf (⋁⇒Fml Cs C))))
            row
  where
    Ats : List Formula
    Ats = atomsOf (⋁⇒Fml Cs C)

    row : {a : Val} -> a ∈ allVecs (length Ats)
       -> valFrom Ats a (⋁⇒Fml Cs C) ≡ true
    row {a} m =
      ⇒Chain Ats a (map (C ⇐_) Cs) (⋁ Cs ⇒ C)
               (λ g -> ⋁ElimTrue Ats a Cs C (λ mD -> g (memMap (C ⇐_) mD)))
