{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.States.Taut -- Boolean facts about how the skeleton evaluation valFrom
-- reads lit, ⋀, ⋁, chi and beta.  They are the side conditions of the pc
-- nodes built in LTL.States.CompletePC and LTL.Procedures.Decide.  The
-- one derivation here is mpChain, which discharges the premises of □Chain.
--
-- Every row lemma fixes one atom list Ats and one row a (the module block
-- below).  Each caller uses atomsOf of the one formula its pc node proves.
--
-- The central fact: row a gives a valuation of P, skelVec P, that reads every
-- subformula of P as row a does, and it is a state as soon as the (S2)
-- instances hold in row a.  So beta P (St P) is true in every row satisfying
-- (S2), which is state completeness as a Boolean fact.

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
       -> (∀ⁱ[ C ∈ Cs ] valFrom Ats a C ≡ true)
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
           -> (∀ⁱ[ D ∈ Cs ] valFrom Ats a (C ⇐ D) ≡ true)
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
        -> ((∀ⁱ[ A ∈ As ] valFrom Ats a A ≡ true)
              -> valFrom Ats a C ≡ true)
        -> valFrom Ats a (⇒List As C) ≡ true
  ⇒Chain []       C h = h (λ ())
  ⇒Chain (A ∷ As) C h =
    ⇒ᵇ-intro (valFrom Ats a A) (valFrom Ats a (⇒List As C))
             (λ eA -> ⇒Chain As C (λ g -> h (more eA g)))
    where
      more : valFrom Ats a A ≡ true
          -> (∀ⁱ[ X ∈ As ] valFrom Ats a X ≡ true)
          -> ∀ⁱ[ X ∈ A ∷ As ] valFrom Ats a X ≡ true
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
  -- The valuation of P that row a gives: P's own atoms read in row a.  By
  -- skelEval it reads every subformula of P as row a does, since valFrom is
  -- ¬ᵇ at ¬ and ⇒ᵇ at ⇒ in any row.

  skelVec : Formula -> Val
  skelVec P = map (valFrom Ats a) (stateAtoms P)

  valOfSkelVec : (P A : Formula) -> A ∈ sub P
              -> valOf P (skelVec P) A ≡ valFrom Ats a A
  valOfSkelVec P A m =
    skelEval (valFrom Ats a) (stateAtoms P) P
             (λ X mX aX -> atomMem (sub P) mX aX)
             (λ X mX -> refl) (λ X Y mX -> refl) A m

  ----------------------------------------------------------------------
  -- Its chi is true in row a: every literal is.

  litTrue : (A : Formula) -> valFrom Ats a (lit A (valFrom Ats a A)) ≡ true
  litTrue A with valFrom Ats a A in e
  ... | true  = e
  ... | false = cong ¬ᵇ_ e

  chiTrue : (P : Formula) -> valFrom Ats a (chi P (skelVec P)) ≡ true
  chiTrue P = ⋀True (map (litOf P (skelVec P)) (subformulas P)) conj
    where
      conj : ∀ⁱ[ C ∈ map (litOf P (skelVec P)) (subformulas P) ]
               valFrom Ats a C ≡ true
      conj {C} m = fromSig (map-mem-inv (litOf P (skelVec P)) (subformulas P) m)
        where
          fromSig : (∃[ A ∈ subformulas P ] C ≡ litOf P (skelVec P) A)
                 -> valFrom Ats a C ≡ true
          fromSig (A , mA , eq) =
            subst (λ D -> valFrom Ats a D ≡ true) (sym eq)
                  (subst (λ b -> valFrom Ats a (lit A b) ≡ true)
                         (sym (valOfSkelVec P A (nub-sub (sub P) mA)))
                         (litTrue A))

  ----------------------------------------------------------------------
  -- It is a state, given (S2) in row a at the eventualities.

  s2Skel : (P : Formula) -> S2At (eventualities P)
        -> ∀[ B ∈ eventualities P ] s2At P (skelVec P) B ≡ true
  s2Skel P s2 B mB =
    trans (cong₂ _⇒ᵇ_ (valOfSkelVec P (□ B) m□)
                      (valOfSkelVec P B (sub-□ P m□)))
          (s2 B mB)
    where
      m□ : □ B ∈ sub P
      m□ = evSub P mB

  memStSkel : (P : Formula) -> S2At (eventualities P) -> skelVec P ∈ St P
  memStSkel P s2 =
    filter-true (isState P) (allVecs (length (stateAtoms P)))
                (allVecs-complete (length (stateAtoms P)) (skelVec P)
                                  (map-length (valFrom Ats a) (stateAtoms P)))
                (all-intro (s2At P (skelVec P)) (eventualities P)
                           (s2Skel P s2))

  -- Hence beta P (St P) is true in any row satisfying (S2): chi P (skelVec
  -- P) is a disjunct (memStSkel) and is true (chiTrue).

  betaSkel : (P : Formula) -> S2At (eventualities P)
          -> valFrom Ats a (beta P (St P)) ≡ true
  betaSkel P s2 =
    ⋁True (map (chi P) (St P)) (memMap (chi P) (memStSkel P s2)) (chiTrue P)

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

tautChi : (Q : Formula) (w : Val)
       -> valOf (¬ Q) w (¬ Q) ≡ false
       -> isTaut ((chi (¬ Q) w) ⇒ Q) ≡ true
tautChi Q w ev =
  isTaut-intro F λ a ->
    ⇒ᵇ-intro (valFrom Ats a (chi R w)) (valFrom Ats a Q)
             (λ ec -> ¬ᵇ¬ᵇ-true (valFrom Ats a Q)
                                (⋀ProjTrue Ats a (map (litOf R w) (subformulas R)) mneg ec))
  where
    R : Formula
    R = ¬ Q

    F : Formula
    F = (chi R w) ⇒ Q

    Ats : List Formula
    Ats = atomsOf F

    -- the conjunct  lit R false , i.e.  ¬ ¬ Q
    mneg : ¬ R ∈ map (litOf R w) (subformulas R)
    mneg = subst (λ b -> lit R b ∈ map (litOf R w) (subformulas R)) ev
                 (memMap (litOf R w) (nub-mem (sub R) (sub-self R)))
