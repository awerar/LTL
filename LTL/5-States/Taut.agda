{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.5-States.Taut -- Boolean facts about how the skeleton evaluation
-- propValue reads lit, ⋀, ⋁, chi and beta.  They are the side conditions of the pc
-- nodes built in LTL.5-States.CompletePC, LTL.5-States.StepLemma and
-- LTL.8-Procedures.Decide.  The one derivation here is mpChain, which
-- discharges the premises of □Chain.
--
-- Every lemma fixes one reading ρ of the atoms (the module block below), so
-- each holds under every ρ, which is what Statement's Tautology asks; the
-- callers turn that into isTaut by isTaut-complete.
--
-- The central fact: ρ gives a valuation of P, skelVec P, that reads every
-- subformula of P as ρ does, and it is a state as soon as the (S2) instances
-- hold under ρ.  So beta P (St P) is true under every reading satisfying
-- (S2), which is state completeness as a Boolean fact.  Conversely, a reading
-- that makes chi v true reads every subformula of P as v does (chiReads), so
-- chi v implies the literal of any subformula (tautProj).

module LTL.5-States.Taut where

open import LTL.5-States.Common

-- Taut states its lemmas for any formula P, so it opens State unapplied, and
-- privately: a P-module that opens Taut has State at its own P.
open import LTL.5-States.State
open import LTL.5-States.Reach using (Val)

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
-- Readings under one reading ρ of the atoms.

module _ (ρ : Formula -> Bool) where

  ----------------------------------------------------------------------
  -- ⋁ is true as soon as one disjunct is, ⋀ exactly when all conjuncts are.
  -- The empty ⋀ is ⊤, which is  var 0 ⇒ var 0 ; the empty ⋁ is ⊥ = ¬ ⊤.
  -- The skeleton reads C ∨ D = ¬ C ⇒ D and C ∧ D = ¬ (C ⇒ ¬ D).

  ⋁True : (Cs : List Formula) {C : Formula}
       -> C ∈ Cs -> propValue ρ C ≡ true
       -> propValue ρ (⋁ Cs) ≡ true
  ⋁True []       ()        e
  ⋁True (D ∷ Cs) here      e =
    ¬ᵇ⇒ᵇ-introˡ (propValue ρ D) (propValue ρ (⋁ Cs)) e
  ⋁True (D ∷ Cs) (there m) e =
    ⇒ᵇ-const (¬ᵇ propValue ρ D) (propValue ρ (⋁ Cs)) (⋁True Cs m e)

  ⋀True : (Cs : List Formula)
       -> (∀ⁱ[ C ∈ Cs ] propValue ρ C ≡ true)
       -> propValue ρ (⋀ Cs) ≡ true
  ⋀True []       h = ⇒ᵇ-refl (propValue ρ (var zero))
  ⋀True (D ∷ Cs) h =
    ¬ᵇ⇒ᵇ¬ᵇ-intro (propValue ρ D) (propValue ρ (⋀ Cs))
                  (h here) (⋀True Cs (λ m -> h (there m)))

  ⋀ProjTrue : (Cs : List Formula) {C : Formula}
           -> C ∈ Cs -> propValue ρ (⋀ Cs) ≡ true
           -> propValue ρ C ≡ true
  ⋀ProjTrue []       ()        e
  ⋀ProjTrue (D ∷ Cs) here      e =
    ¬ᵇ⇒ᵇ¬ᵇ-trueˡ (propValue ρ D) (propValue ρ (⋀ Cs)) e
  ⋀ProjTrue (D ∷ Cs) (there m) e =
    ⋀ProjTrue Cs m (¬ᵇ⇒ᵇ¬ᵇ-trueʳ (propValue ρ D) (propValue ρ (⋀ Cs)) e)

  -- (L5): walk the disjunction to a true disjunct and use the premise there.

  ⋁ElimTrue : (Cs : List Formula) (C : Formula)
           -> (∀ⁱ[ D ∈ Cs ] propValue ρ (C ⇐ D) ≡ true)
           -> propValue ρ (⋁ Cs) ≡ true -> propValue ρ C ≡ true
  ⋁ElimTrue []       C k e =
    emptyElim (true≢false (trans (sym e)
                                 (cong ¬ᵇ_ (⇒ᵇ-refl (propValue ρ (var zero))))))
  ⋁ElimTrue (D ∷ Ds) C k e with propValue ρ D in eb
  ... | true  = ⇒ᵇ-mp (propValue ρ D) (propValue ρ C) (k here) eb
  -- with D false, e already says that ⋁ Ds holds
  ... | false = ⋁ElimTrue Ds C (λ m -> k (there m)) e

  -- ⇒Chain: reading a chain as true is assuming its premises.

  ⇒Chain : (As : List Formula) (C : Formula)
        -> ((∀ⁱ[ A ∈ As ] propValue ρ A ≡ true)
              -> propValue ρ C ≡ true)
        -> propValue ρ (⇒List As C) ≡ true
  ⇒Chain []       C h = h (λ ())
  ⇒Chain (A ∷ As) C h =
    ⇒ᵇ-intro (propValue ρ A) (propValue ρ (⇒List As C))
             (λ eA -> ⇒Chain As C (λ g -> h (more eA g)))
    where
      more : propValue ρ A ≡ true
          -> (∀ⁱ[ X ∈ As ] propValue ρ X ≡ true)
          -> ∀ⁱ[ X ∈ A ∷ As ] propValue ρ X ≡ true
      more eA g here      = eA
      more eA g (there m) = g m

  ----------------------------------------------------------------------
  -- (S2) holds under ρ at each B of As: □ B true implies B true.  It does
  -- not hold under every reading, since □ B and B are independent atoms, so
  -- it is a premise of the formula the pc node proves; □Chain is ⇒Chain at
  -- its instances.

  S2At : List Formula -> Set
  S2At As = ∀[ B ∈ As ] propValue ρ (□ B) ⇒ᵇ propValue ρ B ≡ true

  □Chain : (As : List Formula) (C : Formula)
        -> (S2At As -> propValue ρ C ≡ true)
        -> propValue ρ (⇒List (map s2Fml As) C) ≡ true
  □Chain As C h =
    ⇒Chain (map s2Fml As) C (λ g -> h (λ B mB -> g (∈-map⁺ s2Fml mB)))

  ----------------------------------------------------------------------
  -- The valuation of P that ρ gives: P's own atoms read by ρ.  It reads
  -- every subformula of P as ρ does (rowOf-reads).

  skelVec : (P : Formula) -> Val P
  skelVec P = rowOf ρ (stateAtoms P)

  valOfSkelVec : (P : Formula)
              -> ∀[ A ∈ sub P ] valOf P (skelVec P) A ≡ propValue ρ A
  valOfSkelVec P = rowOf-reads ρ P

  ----------------------------------------------------------------------
  -- Its chi is true under ρ: every literal is.

  litTrue : (A : Formula) -> propValue ρ (lit A (propValue ρ A)) ≡ true
  litTrue A with propValue ρ A in e
  ... | true  = e
  ... | false = cong ¬ᵇ_ e

  chiTrue : (P : Formula) -> propValue ρ (chi P (skelVec P)) ≡ true
  chiTrue P = ⋀True (map (litOf P (skelVec P)) (stateAtoms P)) conj
    where
      conj : ∀ⁱ[ C ∈ map (litOf P (skelVec P)) (stateAtoms P) ]
               propValue ρ C ≡ true
      conj {C} m = fromSig (∈-map⁻ (litOf P (skelVec P)) (stateAtoms P) m)
        where
          fromSig : (∃[ A ∈ stateAtoms P ] C ≡ litOf P (skelVec P) A)
                 -> propValue ρ C ≡ true
          fromSig (A , mA , eq) =
            subst (λ D -> propValue ρ D ≡ true) (sym eq)
                  (subst (λ b -> propValue ρ (lit A b) ≡ true)
                         (sym (valOfSkelVec P A (atomSub P mA)))
                         (litTrue A))

  ----------------------------------------------------------------------
  -- Conversely, a reading that makes chi v true reads every subformula of P
  -- as v does: the literals of chi v fix P's atoms (litBit), and
  -- propValue-cong does the rest.  This holds for any v, state or not.

  litBit : (A : Formula) (b : Bool) -> propValue ρ (lit A b) ≡ true
        -> propValue ρ A ≡ b
  litBit A true  e = e
  litBit A false e = ¬ᵇ-true (propValue ρ A) e

  chiReads : (P : Formula) (v : Val P) -> propValue ρ (chi P v) ≡ true
          -> ∀[ A ∈ sub P ] valOf P v A ≡ propValue ρ A
  chiReads P v e = propValue-cong (atomBit v) ρ P atAt
    where
      atAt : ∀[ X ∈ sub P ] (isAtom X ≡ true -> atomBit v X ≡ ρ X)
      atAt X m eX =
        trans (sym (propValue-atom (atomBit v) X eX))
              (trans (sym (litBit X (valOf P v X)
                             (⋀ProjTrue (map (litOf P v) (stateAtoms P))
                                        (∈-map⁺ (litOf P v) (∈-atoms⁺ P X m eX)) e)))
                     (propValue-atom ρ X eX))

  ----------------------------------------------------------------------
  -- It is a state, given (S2) under ρ at the eventualities.

  s2Skel : (P : Formula) -> S2At (eventualities P)
        -> ∀[ B ∈ eventualities P ] s2At P (skelVec P) B ≡ true
  s2Skel P s2 B mB =
    trans (cong₂ _⇒ᵇ_ (valOfSkelVec P (□ B) m□)
                      (valOfSkelVec P B (sub-□ P m□)))
          (s2 B mB)
    where
      m□ : □ B ∈ sub P
      m□ = evSub P mB

  skelVec∈St : (P : Formula) -> S2At (eventualities P) -> skelVec P ∈ St P
  skelVec∈St P s2 =
    ∈-filter⁺ (isState P) (rows (stateAtoms P))
              (rows-complete (stateAtoms P) (skelVec P))
                (all-intro (s2At P (skelVec P)) (eventualities P)
                           (s2Skel P s2))

  -- Hence beta P (St P) is true under any reading satisfying (S2): chi P (skelVec
  -- P) is a disjunct (skelVec∈St) and is true (chiTrue).

  betaSkel : (P : Formula) -> S2At (eventualities P)
          -> propValue ρ (beta P (St P)) ≡ true
  betaSkel P s2 =
    ⋁True (map (chi P) (St P)) (∈-map⁺ (chi P) (skelVec∈St P s2)) (chiTrue P)

------------------------------------------------------------------------
-- The derivation half of □Chain: one modus ponens against one instance of
-- (S) per premise, left to right.  A chain rather than a conjunction of the
-- (S2) instances: a conjunction is built by (L2) through ∧Pair, about 239
-- constructors per instance, while each premise of a chain costs one modus
-- ponens.

mpChain : (As : List Formula) {C : Formula}
       -> ⊢ ⇒List (map s2Fml As) C -> ⊢ C
mpChain []       d = d
mpChain (A ∷ As) d = mpChain As (mp d □Elim)

------------------------------------------------------------------------
-- (L5) as one pc node.  ⋁Elim (LTL.3-Rules.PropList) derives
-- (C1 ∨ ... ∨ Cn) ⇒ C  at about 426 constructors per disjunct; its implication
-- ⋁⇒Fml is a tautology of its skeleton, so betaElimPC is one pc node with the
-- n branches discharged by modus ponens.

taut⋁Elim : (Cs : List Formula) (C : Formula) -> isTaut (⋁⇒Fml Cs C) ≡ true
taut⋁Elim Cs C =
  isTaut-complete (⋁⇒Fml Cs C) λ ρ ->
    ⇒Chain ρ (map (C ⇐_) Cs) (⋁ Cs ⇒ C) λ g ->
      ⇒ᵇ-intro (propValue ρ (⋁ Cs)) (propValue ρ C)
               (⋁ElimTrue ρ Cs C (λ mD -> g (∈-map⁺ (C ⇐_) mD)))

------------------------------------------------------------------------
-- Projecting chi, as one node.  chi v has a literal per atom only, but
-- chi v ⇒ lit A (valOf v A) is a skeleton tautology for every A in sub P,
-- atom or not: a reading that makes chi v true reads A as v does (chiReads).

tautProj : (P : Formula) (v : Val P)
        -> ∀ⁱ[ A ∈ sub P ] isTaut ((chi P v) ⇒ (litOf P v A)) ≡ true
tautProj P v {A} m =
  isTaut-complete ((chi P v) ⇒ (litOf P v A)) λ ρ ->
    ⇒ᵇ-intro (propValue ρ (chi P v)) (propValue ρ (litOf P v A))
             (λ e -> subst (λ b -> propValue ρ (lit A b) ≡ true)
                           (sym (chiReads ρ P v e A m))
                           (litTrue ρ A))

-- A state w of ¬ Q with the bit at ¬ Q false reads Q as true, so
-- chi_w ⇒ Q  is tautProj at Q.

tautChi : (Q : Formula) (w : Val (¬ Q))
       -> valOf (¬ Q) w (¬ Q) ≡ false
       -> isTaut ((chi (¬ Q) w) ⇒ Q) ≡ true
tautChi Q w ev =
  subst (λ b -> isTaut ((chi (¬ Q) w) ⇒ (lit Q b)) ≡ true)
        (¬ᵇ-false (valOf (¬ Q) w Q) ev)
        (tautProj (¬ Q) w (there (sub-self Q)))
