{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.States.Taut -- Boolean facts about how the skeleton evaluation valFrom
-- reads lit, ⋀, ⋁, chi and beta.  They are the side conditions of the pc
-- nodes built in LTL.States.CompletePC and LTL.Procedures.Decide.  The
-- one derivation here is mpChain, which discharges the premises of □Chain.
--
-- Every row lemma fixes one atom list Ats and one row a (the module block
-- below).  Each caller uses atomsOf of the one formula its pc node proves.
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
-- The formulas the pc nodes prove are built from these.

-- An implication chain  A1 ⇒ ... ⇒ An ⇒ C .
⇒List : List Formula -> Formula -> Formula
⇒List []       C = C
⇒List (A ∷ As) C = A ⇒ (⇒List As C)

-- The instance □ A ⇒ A of (S2).
s2Fml : Formula -> Formula
s2Fml A = □ A ⇒ A

infixl 20 _⇐_

_⇐_ : Formula -> Formula -> Formula
C ⇐ D = D ⇒ C

-- The implication behind (L5),
--
--     (C1 ⇒ C) ⇒ ... ⇒ (Cn ⇒ C) ⇒ ((C1 ∨ ... ∨ Cn) ⇒ C).
⋁⇒Fml : List Formula -> Formula -> Formula
⋁⇒Fml Cs C = ⇒List (map (C ⇐_) Cs) (⋁ Cs ⇒ C)

------------------------------------------------------------------------
-- Readings in one row a of the truth table over the atoms Ats.

module _ (Ats : List Formula) (a : Val) where

  ----------------------------------------------------------------------
  -- ⋁ is true as soon as one disjunct is, ⋀ exactly when all conjuncts are.
  -- The empty ⋀ is ⊤, which is  var 0 ⇒ var 0 ; the empty ⋁ is ⊥ = ¬ ⊤.
  -- The skeleton reads C ∨ D = ¬ C ⇒ D and C ∧ D = ¬ (C ⇒ ¬ D).

  ⋁True : (Cs : List Formula) {C : Formula}
       -> C ∈ Cs -> valFrom Ats a C ≡ true
       -> valFrom Ats a (⋁ Cs) ≡ true
  ⋁True []       ()        e
  ⋁True (D ∷ Cs) here      e =
    ¬ᵇ⇒ᵇ-introˡ (valFrom Ats a D) (valFrom Ats a (⋁ Cs)) e
  ⋁True (D ∷ Cs) (there m) e =
    ⇒ᵇ-const (¬ᵇ valFrom Ats a D) (valFrom Ats a (⋁ Cs)) (⋁True Cs m e)

  ⋀True : (Cs : List Formula)
       -> ({C : Formula} -> C ∈ Cs -> valFrom Ats a C ≡ true)
       -> valFrom Ats a (⋀ Cs) ≡ true
  ⋀True []       h = ⇒ᵇ-refl (valFrom Ats a (var zero))
  ⋀True (D ∷ Cs) h =
    ¬ᵇ⇒ᵇ¬ᵇ-intro (valFrom Ats a D) (valFrom Ats a (⋀ Cs))
                  (h here) (⋀True Cs (λ m -> h (there m)))

  ⋀ProjTrue : (Cs : List Formula) {C : Formula}
           -> C ∈ Cs -> valFrom Ats a (⋀ Cs) ≡ true
           -> valFrom Ats a C ≡ true
  ⋀ProjTrue []       ()        e
  ⋀ProjTrue (D ∷ Cs) here      e =
    ¬ᵇ⇒ᵇ¬ᵇ-trueˡ (valFrom Ats a D) (valFrom Ats a (⋀ Cs)) e
  ⋀ProjTrue (D ∷ Cs) (there m) e =
    ⋀ProjTrue Cs m (¬ᵇ⇒ᵇ¬ᵇ-trueʳ (valFrom Ats a D) (valFrom Ats a (⋀ Cs)) e)

  -- (L5): walk the disjunction to a true disjunct and use the premise there.

  ⋁ElimTrue : (Cs : List Formula) (C : Formula)
           -> ({D : Formula} -> D ∈ Cs -> valFrom Ats a (C ⇐ D) ≡ true)
           -> valFrom Ats a (⋁ Cs) ≡ true -> valFrom Ats a C ≡ true
  ⋁ElimTrue []       C k e =
    emptyElim (true≢false (trans (sym e)
                                 (cong ¬ᵇ_ (⇒ᵇ-refl (valFrom Ats a (var zero))))))
  ⋁ElimTrue (D ∷ Ds) C k e with valFrom Ats a D in eb
  ... | true  = ⇒ᵇ-mp (valFrom Ats a D) (valFrom Ats a C) (k here) eb
  -- with D false, e already says that ⋁ Ds holds
  ... | false = ⋁ElimTrue Ds C (λ m -> k (there m)) e

  -- ⇒Chain: reading a chain as true is assuming its premises.

  ⇒Chain : (As : List Formula) (C : Formula)
        -> (({A : Formula} -> A ∈ As -> valFrom Ats a A ≡ true)
              -> valFrom Ats a C ≡ true)
        -> valFrom Ats a (⇒List As C) ≡ true
  ⇒Chain []       C h = h (λ ())
  ⇒Chain (A ∷ As) C h =
    ⇒ᵇ-intro (valFrom Ats a A) (valFrom Ats a (⇒List As C))
             (λ eA -> ⇒Chain As C (λ g -> h (more eA g)))
    where
      more : valFrom Ats a A ≡ true
          -> ({X : Formula} -> X ∈ As -> valFrom Ats a X ≡ true)
          -> {X : Formula} -> X ∈ A ∷ As -> valFrom Ats a X ≡ true
      more eA g here      = eA
      more eA g (there m) = g m

  ----------------------------------------------------------------------
  -- (S2) holds in row a at each B of As: □ B true implies B true.  It does
  -- not hold in an arbitrary row, since □ B and B are independent atoms, so
  -- it is a premise of the formula the pc node proves; □Chain is ⇒Chain at
  -- its instances.

  S2At : List Formula -> Set
  S2At As = ∀[ B ∈ As ] valFrom Ats a (□ B) ⇒ᵇ valFrom Ats a B ≡ true

  □Chain : (As : List Formula) (C : Formula)
        -> (S2At As -> valFrom Ats a C ≡ true)
        -> valFrom Ats a (⇒List (map s2Fml As) C) ≡ true
  □Chain As C h =
    ⇒Chain (map s2Fml As) C (λ g -> h (λ B mB -> g (memMap s2Fml mB)))

  ----------------------------------------------------------------------
  -- The chi of the row the assignment itself gives is true: its literals are
  -- true one by one.

  litTrue : (A : Formula) -> valFrom Ats a (lit A (valFrom Ats a A)) ≡ true
  litTrue A with valFrom Ats a A in e
  ... | true  = e
  ... | false = cong ¬ᵇ_ e

  litListTrue : (As : List Formula) {C : Formula}
             -> C ∈ litList As (map (valFrom Ats a) As)
             -> valFrom Ats a C ≡ true
  litListTrue []       ()
  litListTrue (A ∷ As) here      = litTrue A
  litListTrue (A ∷ As) (there m) = litListTrue As m

  ----------------------------------------------------------------------
  -- The vector the row gives, read by valOf: the bit at A is valFrom's
  -- reading of A.  (mkV of LTL.States.Closure is skelVec at atoms (sub P).)

  skelVec : Formula -> Val
  skelVec P = map (valFrom Ats a) (sub P)

  valOfSkelVec : (P A : Formula) -> A ∈ sub P
              -> valOf P (skelVec P) A ≡ valFrom Ats a A
  valOfSkelVec P A m =
    trans (nth-map (valFrom Ats a) (sub P) (indexOf (sub P) A)
                   (indexOf-lt (sub P) m) ⊥ false)
          (cong (valFrom Ats a) (indexOf-nth (sub P) m))

  ----------------------------------------------------------------------
  -- skelVec is a state, given (S2) at the box-subformulas.  (S1) holds
  -- because valFrom is ¬ᵇ at ¬ and ⇒ᵇ at ⇒ (valOfSkelVec).

  okAtSkel : (P A : Formula) -> A ∈ sub P -> S2At (□Args (sub P))
          -> okAt P (skelVec P) A ≡ true
  okAtSkel P (var n) m s2 = refl
  okAtSkel P (○ B)   m s2 = refl
  okAtSkel P (¬ B)   m s2 =
    ⇔ᵇ-complete (valOf P (skelVec P) (¬ B)) (¬ᵇ valOf P (skelVec P) B)
                (trans (valOfSkelVec P (¬ B) m)
                       (cong ¬ᵇ_ (sym (valOfSkelVec P B (sub-¬ P m)))))
  okAtSkel P (B ⇒ C) m s2 =
    ⇔ᵇ-complete (valOf P (skelVec P) (B ⇒ C))
                (valOf P (skelVec P) B ⇒ᵇ valOf P (skelVec P) C)
                (trans (valOfSkelVec P (B ⇒ C) m)
                       (cong₂ _⇒ᵇ_ (sym (valOfSkelVec P B (sub-⇒L P m)))
                                   (sym (valOfSkelVec P C (sub-⇒R P m)))))
  okAtSkel P (□ B)   m s2 =
    trans (cong₂ _⇒ᵇ_ (valOfSkelVec P (□ B) m)
                      (valOfSkelVec P B (sub-□ P m)))
          (s2 B (□Args-of (sub P) m))

  -- Coherence.  The bit at position i is the skeleton's reading of the
  -- formula there (nth-map), and so is the bit at that formula's first
  -- occurrence (valOfSkelVec), so the two agree.

  cohAtSkel : (P : Formula) (i : Nat) -> i < length (sub P)
           -> cohAt P (skelVec P) i ≡ true
  cohAtSkel P i l =
    ⇔ᵇ-complete (bitAt (skelVec P) i)
                (valOf P (skelVec P) (nth (sub P) i ⊥))
                (trans (nth-map (valFrom Ats a) (sub P) i l ⊥ false)
                       (sym (valOfSkelVec P (nth (sub P) i ⊥)
                                          (nth-mem (sub P) i l ⊥))))

  allCohSkel : (P : Formula) (n : Nat)
            -> ((i : Nat) -> i < n -> i < length (sub P))
            -> allCoh P (skelVec P) n ≡ true
  allCohSkel P zero    h = refl
  allCohSkel P (suc n) h =
    ∧ᵇ-intro (cohAt P (skelVec P) n) (allCoh P (skelVec P) n)
             (cohAtSkel P n (h n (ltNSucN n)))
             (allCohSkel P n (λ i l -> h i (ltWeak l)))

  memStSkel : (P : Formula) -> S2At (□Args (sub P)) -> skelVec P ∈ St P
  memStSkel P s2 =
    filter-true (isState P) (allVecs (length (sub P)))
                (allVecs-complete (length (sub P)) (skelVec P)
                                  (map-length (valFrom Ats a) (sub P)))
                (∧ᵇ-intro (allOk P (skelVec P) (sub P))
                          (allCoh P (skelVec P) (length (sub P)))
                          (all-intro (okAt P (skelVec P)) (sub P)
                                     (λ {A} m -> okAtSkel P A m s2))
                          (allCohSkel P (length (sub P)) (λ i l -> l)))

  -- Hence beta P (St P) is true in any row satisfying (S2): chi P (skelVec
  -- P) is a disjunct (memStSkel) and is true (litListTrue).

  betaSkel : (P : Formula) -> S2At (□Args (sub P))
          -> valFrom Ats a (beta P (St P)) ≡ true
  betaSkel P s2 =
    ⋁True (map (chi P) (St P)) (memMap (chi P) (memStSkel P s2))
          (⋀True (litList (sub P) (skelVec P)) (litListTrue (sub P)))

------------------------------------------------------------------------
-- The derivation half of □Chain: one modus ponens against one instance of
-- (T) per premise, left to right.  A chain rather than a conjunction of the
-- (S2) instances: a conjunction is built by (L2) through ∧Pair, about 239
-- constructors per instance, while each premise of a chain costs one modus
-- ponens.

mpChain : (As : List Formula) {C : Formula}
       -> ⊢ ⇒List (map s2Fml As) C -> ⊢ C
mpChain []       d = d
mpChain (A ∷ As) d = mpChain As (mp d □Elim)

------------------------------------------------------------------------
-- (L5) as one pc node.  ⋁Elim (LTL.Rules.PropList) derives
-- (C1 ∨ ... ∨ Cn) ⇒ C  at about 426 constructors per disjunct; its implication
-- ⋁⇒Fml is a tautology of its skeleton, so betaElimPC is one pc node with the
-- n branches discharged by modus ponens.

taut⋁Elim : (Cs : List Formula) (C : Formula) -> isTaut (⋁⇒Fml Cs C) ≡ true
taut⋁Elim Cs C =
  isTaut-intro (⋁⇒Fml Cs C) λ a ->
    ⇒Chain Ats a (map (C ⇐_) Cs) (⋁ Cs ⇒ C) λ g ->
      ⇒ᵇ-intro (valFrom Ats a (⋁ Cs)) (valFrom Ats a C)
               (⋁ElimTrue Ats a Cs C (λ mD -> g (memMap (C ⇐_) mD)))
  where
    Ats : List Formula
    Ats = atomsOf (⋁⇒Fml Cs C)

------------------------------------------------------------------------
-- A state not containing ¬ Q, as one node.
--
-- For a state w of ¬ Q with the bit at ¬ Q false,  chi_w ⇒ Q  is a skeleton
-- tautology: chi_w has the conjunct  lit (¬ Q) false = ¬ ¬ Q , and valFrom is
-- ¬ᵇ at ¬.  So (PC) proves it in one node where projecting and cancelling the
-- double negation takes 67 constructors.

-- The literal of P itself inside chi P w, at the first occurrence of P.
litSelf : (P : Formula) (w : Val) -> length w ≡ length (sub P)
       -> lit P (valOf P w P) ∈ litList (sub P) w
litSelf P w len =
  subst (λ X -> lit X (valOf P w P) ∈ litList (sub P) w)
        (indexOf-nth (sub P) (sub-self P))
        (litList-nth (sub P) w (indexOf (sub P) P)
                     (indexOf-lt (sub P) (sub-self P)) len)

tautChi : (Q : Formula) (w : Val) -> length w ≡ length (sub (¬ Q))
       -> valOf (¬ Q) w (¬ Q) ≡ false
       -> isTaut ((chi (¬ Q) w) ⇒ Q) ≡ true
tautChi Q w len ev =
  isTaut-intro F λ a ->
    ⇒ᵇ-intro (valFrom Ats a (chi R w)) (valFrom Ats a Q)
             (λ ec -> ¬ᵇ¬ᵇ-true (valFrom Ats a Q)
                                (⋀ProjTrue Ats a (litList (sub R) w) mneg ec))
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
