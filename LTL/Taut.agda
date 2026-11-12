{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Taut -- G31 and G32 of FORMALISATION-PLAN.md, boolean half.
--
-- (PC) asks that a formula be a tautology of its own skeleton: isTaut A runs
-- valFrom over the truth table of atomsOf A (LTL.Skel).  The two formulas
-- Phase 9 wants to feed it are built by the list constructions of LTL.Val --
-- lit, ⋀, ⋁, chi and beta -- so what is needed is how valFrom reads
-- those, and that is all this module is.  No derivation appears in it.
--
-- Two things to keep in mind while reading, both of them warnings.
--
-- ONE ATOM LIST.  valFrom Ats a X depends on Ats: indexOf picks a FIRST
-- occurrence, so two atom lists give two different readings of the same formula
-- and there is no transport between them.  Every lemma here therefore takes
-- Ats and a as parameters and fixes them; each caller in LTL.CompletePC
-- instantiates them with atomsOf of the single formula its pc step is about,
-- and nothing is ever moved from one atom list to another.
--
-- NOT mkV.  LTL.Closure does the same construction with Ats := atoms (sub P) --
-- mkV, atomBits, valFromEq, mkV_id -- and those are the wrong lemmas here: the
-- atom list of a (PC) formula is a different, larger list, if only because
-- ⋀ [] is ⊤ and so contributes var 0.  They would appear to typecheck and
-- then fail on an indexOf.  valOfSkelVec below is the bridge that is actually
-- wanted, and it is one instance of atomLook.
--
-- The last section is the point.  Fix Ats and a; then
--
--     skelVec Ats a P  =  map (valFrom Ats a) (sub P)
--
-- is a STATE of P as soon as the (S2) instances hold under the same reading:
-- (S1) and coherence come for free, because valFrom is compositional on neg and
-- imp BY DEFINITION and because valOfSkelVec makes the bit at a position depend
-- on the formula there rather than on the position.  That is the whole content
-- of the short Lemma 2.6, and the (S2) proviso is exactly the premise -- the E
-- P of section 7 -- that LTL.CompletePC discharges with |□Args| instances of
-- (T), one modus ponens each.

module LTL.Taut where

open import LTL.State public

------------------------------------------------------------------------
-- Booleans.  (⇒IntroB, ⇒TrueB, notTrue and filter_true live in LTL.Prelude,
-- which both branches of the import graph see.)

boolSelf : (b : Bool) -> b ⇒ᵇ b ≡ true
boolSelf true  = refl
boolSelf false = refl

boolImpR : (x y : Bool) -> y ≡ true -> x ⇒ᵇ y ≡ true
boolImpR true  y e = e
boolImpR false y e = refl

boolEqRefl : (b : Bool) -> b ⇔ᵇ b ≡ true
boolEqRefl true  = refl
boolEqRefl false = refl

boolEqOf : (x y : Bool) -> x ≡ y -> x ⇔ᵇ y ≡ true
boolEqOf x y refl = boolEqRefl x

------------------------------------------------------------------------
-- Membership, as a boolean.
--
-- The converse of ∈ᶠ-tail: LTL.Skel proves what a true A ∈ᶠ As gives, and this
-- is what gives one.  It is what turns a membership proof into the side condition of
-- atomLook, so it is the only thing standing between A ∈ sub P and the
-- bridge below.

∈ᶠ-mem : (As : List Formula) {A : Formula} -> A ∈ As -> A ∈ᶠ As ≡ true
∈ᶠ-mem []       ()
∈ᶠ-mem (B ∷ Bs) here     = orL (B ≡ᶠ B) (B ∈ᶠ Bs) (≡ᶠ-refl B)
∈ᶠ-mem (B ∷ Bs) {A} (there m) =
  orR (B ≡ᶠ A) (A ∈ᶠ Bs) (∈ᶠ-mem Bs m)

------------------------------------------------------------------------
-- The skeleton reads ∨ and ∧ as one expects.
--
-- C ∨ D is ¬ C ⇒ D and C ∧ D is ¬ (C ⇒ ¬ D), so these two are
-- boolean identities and not inductions; they are stated at the shapes the list
-- constructions produce, so that ⋁True and ⋀True below are two lines
-- each.

skel∨Inl : (x y : Bool) -> x ≡ true -> ¬ᵇ x ⇒ᵇ y ≡ true
skel∨Inl true  y e = refl
skel∨Inl false y ()

skel∧Intro : (x y : Bool) -> x ≡ true -> y ≡ true
          -> ¬ᵇ (x ⇒ᵇ ¬ᵇ y) ≡ true
skel∧Intro true  true  e1 e2 = refl
skel∧Intro true  false e1 ()
skel∧Intro false y     () e2

------------------------------------------------------------------------
-- ⋁ and ⋀ under the skeleton.
--
-- ⋁ is true as soon as one disjunct is and ⋀ as soon as all conjuncts
-- are.  The empty cases are the convention of Lemma 1.1: ⋁ [] is ⊥, which
-- never has to be true, and ⋀ [] is ⊤, which is  var 0 ⇒ var 0  and so
-- true by boolSelf whatever the atom list makes of var 0.

⋁True : (Ats : List Formula) (a : Val) (Cs : List Formula) {C : Formula}
        -> C ∈ Cs -> valFrom Ats a C ≡ true
        -> valFrom Ats a (⋁ Cs) ≡ true
⋁True Ats a []       ()       e
⋁True Ats a (D ∷ Cs) here     e =
  skel∨Inl (valFrom Ats a D) (valFrom Ats a (⋁ Cs)) e
⋁True Ats a (D ∷ Cs) (there m) e =
  boolImpR (¬ᵇ valFrom Ats a D) (valFrom Ats a (⋁ Cs))
           (⋁True Ats a Cs m e)

⋀True : (Ats : List Formula) (a : Val) (Cs : List Formula)
        -> ({C : Formula} -> C ∈ Cs -> valFrom Ats a C ≡ true)
        -> valFrom Ats a (⋀ Cs) ≡ true
⋀True Ats a []       h = boolSelf (valFrom Ats a (var zero))
⋀True Ats a (D ∷ Cs) h =
  skel∧Intro (valFrom Ats a D) (valFrom Ats a (⋀ Cs))
             (h here) (⋀True Ats a Cs (λ m -> h (there m)))

------------------------------------------------------------------------
-- The characteristic formula of the row the assignment itself gives.
--
-- Read the atoms by a, read every formula of As by the skeleton, and collect
-- the answers: the literals of the resulting chi are true one by one, since
-- lit A true is A and lit A false is ¬ A and valFrom is ¬ᵇ at neg.  So
-- chi of that row is true -- which is the witness disjunct for both of the
-- tautologies of LTL.CompletePC.

litTrue : (Ats : List Formula) (a : Val) (A : Formula)
       -> valFrom Ats a (lit A (valFrom Ats a A)) ≡ true
litTrue Ats a A = go (valFrom Ats a A) refl
  where
    go : (b : Bool) -> valFrom Ats a A ≡ b
      -> valFrom Ats a (lit A b) ≡ true
    go true  e = e
    go false e = cong ¬ᵇ_ e

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
-- The bridge: the vector a truth-table row gives, read by valOf.
--
-- skelVec is mkV of LTL.Closure with the atom list left free, and valOfSkelVec
-- is the corresponding valFromEq.  The proof is not an induction at all: valOf
-- looks a formula up by indexOf, skelVec is a map, and atomLook (LTL.Skel) is
-- exactly the round trip between those two, needing only that the formula
-- occurs -- which ∈ᶠ-mem supplies.

skelVec : List Formula -> Val -> Formula -> Val
skelVec Ats a P = map (valFrom Ats a) (sub P)

valOfSkelVec : (P : Formula) (Ats : List Formula) (a : Val) (A : Formula)
            -> A ∈ sub P
            -> valOf P (skelVec Ats a P) A ≡ valFrom Ats a A
valOfSkelVec P Ats a A m =
  atomLook (valFrom Ats a) (sub P) A (∈ᶠ-mem (sub P) m)

------------------------------------------------------------------------
-- skelVec is a state, given (S2).
--
-- (S1) at neg and at imp, and coherence at every position, hold for no reason
-- at all: valOfSkelVec says the bit at A is valFrom's reading of A, and valFrom
-- IS ¬ᵇ at neg and ⇒ᵇ at imp.  This is the same observation that makes the
-- (PC) case of soundness one line (LTL.Sound) -- there against evalAt, here
-- against the vector's own valOf.
--
-- (S2) is the one clause that is not free, and it is not free because it is not
-- true of an arbitrary row: □ A and A are two independent atoms of the
-- skeleton.  So it is assumed, as □Ok, and the caller pays for it.

-- The instance □ A ⇒ A of (S2) as a formula.

s2Fml : Formula -> Formula
s2Fml A = □ A ⇒ A

□Ok : List Formula -> Val -> Formula -> Set
□Ok Ats a P = (B : Formula) -> □ B ∈ sub P
             -> valFrom Ats a (□ B) ⇒ᵇ valFrom Ats a B ≡ true

okAtSkel : (Ats : List Formula) (a : Val) (P : Formula) (A : Formula)
        -> A ∈ sub P -> □Ok Ats a P
        -> okAt P (skelVec Ats a P) A ≡ true
okAtSkel Ats a P (var n)   m boxOk = refl
okAtSkel Ats a P (○ B)   m boxOk = refl
okAtSkel Ats a P (¬ B)   m boxOk =
  boolEqOf (valOf P (skelVec Ats a P) (¬ B))
           (¬ᵇ valOf P (skelVec Ats a P) B)
           (trans (valOfSkelVec P Ats a (¬ B) m)
                  (cong ¬ᵇ_
                        (sym (valOfSkelVec P Ats a B (sub_¬ P m)))))
okAtSkel Ats a P (B ⇒ C) m boxOk =
  boolEqOf (valOf P (skelVec Ats a P) (B ⇒ C))
           (valOf P (skelVec Ats a P) B ⇒ᵇ valOf P (skelVec Ats a P) C)
           (trans (valOfSkelVec P Ats a (B ⇒ C) m)
                  (cong₂ _⇒ᵇ_
                         (sym (valOfSkelVec P Ats a B (sub_⇒L P m)))
                         (sym (valOfSkelVec P Ats a C (sub_⇒R P m)))))
okAtSkel Ats a P (□ B)   m boxOk =
  trans (cong₂ _⇒ᵇ_ (valOfSkelVec P Ats a (□ B) m)
                    (valOfSkelVec P Ats a B (sub_□ P m)))
        (boxOk B m)

allOkSkel : (Ats : List Formula) (a : Val) (P : Formula) (As : List Formula)
         -> ({A : Formula} -> A ∈ As -> A ∈ sub P) -> □Ok Ats a P
         -> allOk P (skelVec Ats a P) As ≡ true
allOkSkel Ats a P []       sb boxOk = refl
allOkSkel Ats a P (A ∷ As) sb boxOk =
  andIntro (okAt P (skelVec Ats a P) A) (allOk P (skelVec Ats a P) As)
           (okAtSkel Ats a P A (sb here) boxOk)
           (allOkSkel Ats a P As (λ m -> sb (there m)) boxOk)

-- Coherence.  The bit at position i is the skeleton's reading of the formula
-- AT position i, by nth_map, and the bit at the first occurrence of that same
-- formula is the same reading, by valOfSkelVec.  So the two agree, which is
-- what cohAt asks; the vector represents a function on the SET Sub(P), which is
-- the clause of FORMALISATION-PLAN.md section 0.

cohAtSkel : (Ats : List Formula) (a : Val) (P : Formula) (i : Nat)
         -> i < length (sub P)
         -> cohAt P (skelVec Ats a P) i ≡ true
cohAtSkel Ats a P i l =
  boolEqOf (bitAt (skelVec Ats a P) i)
           (valOf P (skelVec Ats a P) (nth (sub P) i ⊥))
           (trans (nth_map (valFrom Ats a) (sub P) i l ⊥ false)
                  (sym (valOfSkelVec P Ats a (nth (sub P) i ⊥)
                                     (nth_mem (sub P) i l ⊥))))

allCohSkel : (Ats : List Formula) (a : Val) (P : Formula) (n : Nat)
          -> ((i : Nat) -> i < n -> i < length (sub P))
          -> allCoh P (skelVec Ats a P) n ≡ true
allCohSkel Ats a P zero    h = refl
allCohSkel Ats a P (suc n) h =
  andIntro (cohAt P (skelVec Ats a P) n) (allCoh P (skelVec Ats a P) n)
           (cohAtSkel Ats a P n (h n (ltNSucN n)))
           (allCohSkel Ats a P n (λ i l -> h i (ltWeak l)))

isStateSkel : (Ats : List Formula) (a : Val) (P : Formula) -> □Ok Ats a P
           -> isState P (skelVec Ats a P) ≡ true
isStateSkel Ats a P boxOk =
  andIntro (allOk P (skelVec Ats a P) (sub P))
           (allCoh P (skelVec Ats a P) (length (sub P)))
           (allOkSkel Ats a P (sub P) (λ m -> m) boxOk)
           (allCohSkel Ats a P (length (sub P)) (λ i l -> l))

memStSkel : (Ats : List Formula) (a : Val) (P : Formula) -> □Ok Ats a P
         -> skelVec Ats a P ∈ St P
memStSkel Ats a P boxOk =
  filter_true (isState P) (allVecs (length (sub P)))
              (allVecs_complete (length (sub P)) (skelVec Ats a P)
                                (map_length (valFrom Ats a) (sub P)))
              (isStateSkel Ats a P boxOk)

------------------------------------------------------------------------
-- Hence beta_{St P} is true under any row satisfying (S2).
--
-- chi P (skelVec Ats a P) is one of its disjuncts, by memStSkel, and it is
-- true, by chiRowTrue at As := sub P.  That is Lemma 2.6 as a boolean fact,
-- and LTL.CompletePC turns it into a one-node derivation.

betaSkel : (Ats : List Formula) (a : Val) (P : Formula) -> □Ok Ats a P
        -> valFrom Ats a (beta P (St P)) ≡ true
betaSkel Ats a P boxOk =
  ⋁True Ats a (map (chi P) (St P))
           (memMap (chi P) (memStSkel Ats a P boxOk))
           (chiRowTrue Ats a (sub P))

------------------------------------------------------------------------
-- The (S2) instances, discharged one at a time.
--
-- (S2) is assumed above, so it has to appear as a premise of the formula the
-- pc node proves.  section 7 makes it a CONJUNCTION over □Args (sub P); an
-- implication chain is better, and measurably so.  A conjunction has to be
-- built by (L2), and ⋀Intro goes through ∧Pair, which goes through
-- ¬IntroU and dne: 239 constructors to conjoin a single instance of (T)
-- against the 47 the instance itself costs.  An iterated implication is
-- discharged by one modus ponens per premise, so the certificate is
--
--     |□Args (sub P)| * (1 + |□Elim|) + 1
--
-- exactly, with no propositional glue at all.  That is the linear-in-the-
-- eventualities figure the phase is after, and it is why ⋀ does not appear
-- here even though the note's (L2) would have supplied it.
--
-- ⇒Chain is the boolean half, and it says the only thing an implication
-- chain ever says: reading it as true is the same as assuming its premises.
-- □Chain is that at As := map s2Fml (□Args (sub P)), where the premises are
-- (S2); the caller turns a box-subformula into a member with □Args_of.

⇒List : List Formula -> Formula -> Formula
⇒List []       C = C
⇒List (A ∷ As) C = A ⇒ (⇒List As C)

⇒Chain : (Ats : List Formula) (a : Val) (As : List Formula) (C : Formula)
        -> ((({A : Formula} -> A ∈ As -> valFrom Ats a A ≡ true)
              -> valFrom Ats a C ≡ true))
        -> valFrom Ats a (⇒List As C) ≡ true
⇒Chain Ats a []       C h = h (λ ())
⇒Chain Ats a (A ∷ As) C h =
  ⇒IntroB (valFrom Ats a A) (valFrom Ats a (⇒List As C))
          (λ eA -> ⇒Chain Ats a As C (λ g -> h (more eA g)))
  where
    more : valFrom Ats a A ≡ true
        -> ({X : Formula} -> X ∈ As -> valFrom Ats a X ≡ true)
        -> {X : Formula} -> X ∈ A ∷ As -> valFrom Ats a X ≡ true
    more eA g here      = eA
    more eA g (there m) = g m

-- (S2) holds in row a at each B of As: □ B true implies B true.  It is □Ok
-- indexed by a list.

S2At : List Formula -> Val -> List Formula -> Set
S2At Ats a As = (B : Formula) -> B ∈ As
             -> valFrom Ats a (□ B) ⇒ᵇ valFrom Ats a B ≡ true

□Chain : (Ats : List Formula) (a : Val) (As : List Formula) (C : Formula)
        -> (S2At Ats a As -> valFrom Ats a C ≡ true)
        -> valFrom Ats a (⇒List (map s2Fml As) C) ≡ true
□Chain Ats a As C h =
  ⇒Chain Ats a (map s2Fml As) C (λ g -> h (λ B mB -> g (memMap s2Fml mB)))

------------------------------------------------------------------------
-- (L5), as a boolean.
--
-- This is the same move again, one level down, and it is where the certificate
-- actually is.  ⋁Elim (LTL.PropList) proves  (C1 ∨ ... ∨ Cn) ⇒ C  from
-- the n implications Ci -> C, and it is the note's own (L5): A ∨ B is
-- ¬ A ⇒ B, so the elimination has to contrapose and double-negate at every
-- cons, which measures 426 constructors PER DISJUNCT.  For the certificate that
-- is the dominant cost -- 1280 of the 1529 for □ p ⇒ p -- and it grows with
-- the number of states.
--
-- But the implication it proves is a tautology of its own skeleton, exactly as
-- Lemma 2.6's is, so it can be one pc node with the n branches discharged by
-- modus ponens.  What follows is its truth: given the premises and a true
-- disjunction, walk the disjunction until a true disjunct is found and use the
-- premise there.  The empty case is (L0) -- ⋁ [] is ⊥, which cannot be
-- true, and boolSelf is what says so.

infixl 20 _⇐_

_⇐_ : Formula -> Formula -> Formula
C ⇐ D = D ⇒ C

⋁ElimTrue : (Ats : List Formula) (a : Val) (Cs : List Formula) (C : Formula)
            -> ({D : Formula} -> D ∈ Cs
                  -> valFrom Ats a (C ⇐ D) ≡ true)
            -> valFrom Ats a (⋁ Cs ⇒ C) ≡ true
⋁ElimTrue Ats a Cs C h =
  ⇒IntroB (valFrom Ats a (⋁ Cs)) (valFrom Ats a C) (go Cs h)
  where
    go : (Ds : List Formula)
      -> ({D : Formula} -> D ∈ Ds -> valFrom Ats a (C ⇐ D) ≡ true)
      -> valFrom Ats a (⋁ Ds) ≡ true -> valFrom Ats a C ≡ true
    go []        k e =
      emptyElim (true≢false (trans (sym e)
                                   (cong ¬ᵇ_
                                         (boolSelf (valFrom Ats a (var zero))))))
    go (D ∷ Ds) k e = onD (valFrom Ats a D) refl
      where
        onD : (b : Bool) -> valFrom Ats a D ≡ b -> valFrom Ats a C ≡ true
        onD true  eb = ⇒TrueB (valFrom Ats a D) (valFrom Ats a C) (k here) eb
        onD false eb =
          go Ds (λ m -> k (there m))
             (⇒TrueB (¬ᵇ valFrom Ats a D) (valFrom Ats a (⋁ Ds)) e
                     (cong ¬ᵇ_ eb))

------------------------------------------------------------------------
-- G34 of PHASE10-PLAN.md: the branch as one node.
--
-- The last term of the certificate that is neither constant nor linear-with-
-- constant-one is the 67 constructors per state -- the two easy cases of
-- provableEach, which project  ¬ ¬ Q  out of chi_w by (L2), 39, then
-- cancel the double negation, 23, then (L1), 5.
--
-- But  chi_w ⇒ Q  is a TAUTOLOGY OF ITS OWN SKELETON whenever w does not
-- contain ¬ Q, and for the same reason the derivation works: chi_w is a
-- conjunction one of whose conjuncts is  lit (¬ Q) (valOf (¬ Q) w (¬ Q))
-- -- and the hypothesis says that bit is false, so the conjunct is
-- ¬ ¬ Q.  A conjunction implies its conjuncts, and valFrom is ¬ᵇ at
-- neg by definition, so a row making chi_w true makes  not not Q  true and
-- hence Q.  Nothing about Q's own structure is used; Q is read by the skeleton
-- like anything else.
--
-- So this is the same move as G31 and G32 one more time, at the last place it
-- had not been made: a propositional step DECIDED rather than derived.

------------------------------------------------------------------------
-- ∧, read out rather than built up.  skel∧Intro above is the introduction; a
-- projection needs the two eliminations.

skel∧Fst : (x y : Bool) -> ¬ᵇ (x ⇒ᵇ ¬ᵇ y) ≡ true
        -> x ≡ true
skel∧Fst true  y e = refl
skel∧Fst false y ()

skel∧Snd : (x y : Bool) -> ¬ᵇ (x ⇒ᵇ ¬ᵇ y) ≡ true
        -> y ≡ true
skel∧Snd true  true  e = refl
skel∧Snd true  false ()
skel∧Snd false y     ()

boolNotNot : (x : Bool) -> ¬ᵇ ¬ᵇ x ≡ true -> x ≡ true
boolNotNot true  e = refl
boolNotNot false ()

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
-- The literal of P itself inside chi P w.
--
-- sub P begins with P (LTL.Sub) and P ≡ᶠ P is true, so indexOf finds it at
-- position zero, which is also where sub_self points.  The five clauses are
-- the five clauses of sub_self, and each is the same one line: nothing is
-- proved by induction, only that the head of sub P is P.

idxSelf : (P : Formula) -> indexOf (sub P) P ≡ index (sub_self P)
idxSelf (var n)   = cong (λ b -> indexOfCons b (indexOf [] (var n))) (≡ᶠ-refl (var n))
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
        (litList_mem (sub P) w len (sub_self P))

------------------------------------------------------------------------
-- G34.
--
-- The state w is one of Sub (¬ Q)'s valuations and it does not contain
-- ¬ Q; then  chi_w ⇒ Q  is a skeleton tautology, so (PC) proves it in one
-- node where the projection-and-double-negation proof takes 67.

tautChi : (Q : Formula) (w : Val) -> length w ≡ length (sub (¬ Q))
       -> valOf (¬ Q) w (¬ Q) ≡ false
       -> isTaut ((chi (¬ Q) w) ⇒ Q) ≡ true
tautChi Q w len ev =
  all_intro (λ a -> valFrom Ats a F) (allVecs (length Ats)) row
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
    row {a} m = ⇒IntroB (valFrom Ats a (chi R w)) (valFrom Ats a Q) step
      where
        step : valFrom Ats a (chi R w) ≡ true -> valFrom Ats a Q ≡ true
        step ec =
          boolNotNot (valFrom Ats a Q)
                     (⋀ProjTrue Ats a (litList (sub R) w) mneg ec)

------------------------------------------------------------------------
-- G35 of PHASE10-PLAN.md: chi over atoms, boolean half.
--
-- chi P v is a conjunction of |Sub P| literals where |atoms (sub P)| would do:
-- (S1) determines the bit at ¬ A from the bit at A and the bit at A ⇒ B
-- from those at A and B, so the literals at the non-atomic positions are
-- redundant.  For ¬ (□ p ⇒ □ ○ p) that is 7 conjuncts against 4, with
-- ¬ bnb listed twice and p twice; for ¬ axK5fwd it is 22 against 8.
--
-- What is needed to exploit that is one fact -- a row of the skeleton table
-- that agrees with a state on the ATOMS agrees with it everywhere -- and it is
-- skelEval (LTL.Skel) with the assignment left free instead of being map f Ats.
-- The five clauses are skelEval's five clauses; only the hypothesis changes.

boolContra : (x y : Bool) -> (y ≡ true -> x ≡ true)
          -> ¬ᵇ x ⇒ᵇ ¬ᵇ y ≡ true
boolContra true  y     h = refl
boolContra false true  h = emptyElim (true≢false (sym (h refl)))
boolContra false false h = refl

∈ᶠ-sound : (As : List Formula) (A : Formula) -> A ∈ᶠ As ≡ true -> A ∈ As
∈ᶠ-sound []       A ()
∈ᶠ-sound (B ∷ Bs) A e = go (B ≡ᶠ A) refl
  where
    go : (b : Bool) -> B ≡ᶠ A ≡ b -> A ∈ B ∷ Bs
    go true  eb = subst (λ X -> X ∈ B ∷ Bs) (≡ᶠ-sound B A eb) here
    go false eb = there (∈ᶠ-sound Bs A (∈ᶠ-tail B Bs A e eb))

-- the atoms of a list are members of it

insFIn : (A : Formula) (Bs : List Formula) {X : Formula}
      -> X ∈ insF A Bs -> X ≡ A ⊎ X ∈ Bs
insFIn A Bs {X} m = go (A ∈ᶠ Bs) refl
  where
    go : (b : Bool) -> A ∈ᶠ Bs ≡ b -> X ≡ A ⊎ X ∈ Bs
    go true  e = inr (subst (λ c -> X ∈ filterCons (¬ᵇ c) A Bs) e m)
    go false e = onM (subst (λ c -> X ∈ filterCons (¬ᵇ c) A Bs) e m)
      where
        onM : X ∈ A ∷ Bs -> X ≡ A ⊎ X ∈ Bs
        onM here      = inl refl
        onM (there k) = inr k

atomsIn : (As : List Formula) {X : Formula} -> X ∈ atoms As -> X ∈ As
atomsIn []             ()
atomsIn (var n   ∷ As) {X} m =
  sumElim (λ e -> subst (λ Y -> Y ∈ var n ∷ As) (sym e) here)
          (λ k -> there (atomsIn As k)) (insFIn (var n) (atoms As) m)
atomsIn (¬ B   ∷ As)     m = there (atomsIn As m)
atomsIn (B ⇒ C ∷ As)     m = there (atomsIn As m)
atomsIn (○ B   ∷ As) {X} m =
  sumElim (λ e -> subst (λ Y -> Y ∈ ○ B ∷ As) (sym e) here)
          (λ k -> there (atomsIn As k)) (insFIn (○ B) (atoms As) m)
atomsIn (□ B   ∷ As) {X} m =
  sumElim (λ e -> subst (λ Y -> Y ∈ □ B ∷ As) (sym e) here)
          (λ k -> there (atomsIn As k)) (insFIn (□ B) (atoms As) m)

------------------------------------------------------------------------
-- Literals, read in both directions.

litOfEq : (Ats : List Formula) (a : Val) (A : Formula) (b : Bool)
       -> valFrom Ats a A ≡ b -> valFrom Ats a (lit A b) ≡ true
litOfEq Ats a A true  e = e
litOfEq Ats a A false e = cong ¬ᵇ_ e

litSound : (Ats : List Formula) (a : Val) (A : Formula) (b : Bool)
        -> valFrom Ats a (lit A b) ≡ true -> valFrom Ats a A ≡ b
litSound Ats a A true  e = e
litSound Ats a A false e = notTrue (valFrom Ats a A) e

litMapMem : (f : Formula -> Bool) (As : List Formula) {X : Formula}
         -> X ∈ As -> lit X (f X) ∈ litList As (map f As)
litMapMem f []       ()
litMapMem f (A ∷ As) here      = here
litMapMem f (A ∷ As) (there m) = there (litMapMem f As m)

litMapOk : (Ats : List Formula) (a : Val) (f : Formula -> Bool) (As : List Formula)
        -> ((A : Formula) -> A ∈ As -> valFrom Ats a A ≡ f A)
        -> {C : Formula} -> C ∈ litList As (map f As)
        -> valFrom Ats a C ≡ true
litMapOk Ats a f []       h ()
litMapOk Ats a f (A ∷ As) h here      = litOfEq Ats a A (f A) (h A here)
litMapOk Ats a f (A ∷ As) h (there m) =
  litMapOk Ats a f As (λ B mB -> h B (there mB)) m

------------------------------------------------------------------------
-- The fact G35 turns on.
--
-- A row that agrees with a state on the atoms of Sub P agrees with it on all of
-- Sub P.  This is skelEval with the assignment a free rather than map f Ats:
-- the induction is the same, and the two non-atomic clauses are (S1) read out
-- of allOk, exactly as valFromEq (LTL.Closure) does.

skelAgree : (Ats : List Formula) (a : Val) (P : Formula) (v : Val)
         -> allOk P v (sub P) ≡ true
         -> ((X : Formula) -> X ∈ sub P -> isAtomB X ≡ true
               -> valFrom Ats a X ≡ valOf P v X)
         -> (A : Formula) -> A ∈ sub P
         -> valFrom Ats a A ≡ valOf P v A
skelAgree Ats a P v ok at (var n)   m = at (var n) m refl
skelAgree Ats a P v ok at (○ A)   m = at (○ A) m refl
skelAgree Ats a P v ok at (□ A)   m = at (□ A) m refl
skelAgree Ats a P v ok at (¬ A)   m =
  trans (cong ¬ᵇ_ (skelAgree Ats a P v ok at A (sub_¬ P m)))
        (sym (⇔ᵇ-sound (valOf P v (¬ A)) (¬ᵇ valOf P v A)
                       (allOk_at P v (sub P) m ok)))
skelAgree Ats a P v ok at (A ⇒ B) m =
  trans (cong₂ _⇒ᵇ_ (skelAgree Ats a P v ok at A (sub_⇒L P m))
                    (skelAgree Ats a P v ok at B (sub_⇒R P m)))
        (sym (⇔ᵇ-sound (valOf P v (A ⇒ B))
                       (valOf P v A ⇒ᵇ valOf P v B)
                       (allOk_at P v (sub P) m ok)))
