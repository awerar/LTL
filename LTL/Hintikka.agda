{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Hintikka -- G27 of FORMALISATION-PLAN.md.
--
--   "and by induction on formulas, using (T1) for Next, (S2) and (T2) for
--    Always A in v_i, and Lemma 5.4 for Always A not in v_i, that
--    A in v_i  iff  [[A]]_{v_i} = 1   (A in Sub(phi)),
--    which is Hintikka's lemma."                           -- m4.tex section 5
--
-- Stated as an equality of Booleans rather than as a biconditional, which is
-- the same thing here and saves carrying two implications through five cases:
--
--   valOf P (state at pos) A  =  evalAt P c0 c1 A pos       for A in Sub(P).
--
-- The five cases are the note's, one apparatus each:
--
--   var       nothing to do -- evalAt reads the state through valOf.
--   neg, imp  (S1), through okAt at a state of U_inf.
--   ○ (T1), through allStep_at at the transition posStep supplies.
--   box       both halves.  If □ A is in the state, (T2) carries it along the
--             run -- □Along -- and (S2) turns it into A at each stage, and
--             every position of the orbit is such a stage.  If □ A is not in
--             the state, Lemma 5.4 hands over a position of the orbit at which
--             A fails, and one false conjunct refutes the conjunction.
--
-- Both halves of the box case use exactly one lemma each from Phase 6: carry
-- (T2) and globalFulfil (G24).  Nothing else in the development is needed.

module LTL.Hintikka where

open import LTL.Sound   public
open import LTL.Extract public

------------------------------------------------------------------------
-- Reading (S1) and (S2) off a survivor

stateOk : (P : Formula) (s : Val) -> s ∈ Uinf P -> {A : Formula}
       -> A ∈ sub P -> okAt P s A ≡ true
stateOk P s m mA =
  allOk_at P s (sub P) mA
           (andTrueL (allOk P s (sub P)) (allCoh P s (length (sub P)))
                     (uinfState P s m))

-- (S2)
□S2 : (P : Formula) (s : Val) -> s ∈ Uinf P -> (B : Formula)
     -> □ B ∈ sub P -> valOf P s (□ B) ≡ true -> valOf P s B ≡ true
□S2 P s m B mb e =
  ⇒TrueB (valOf P s (□ B)) (valOf P s B) (stateOk P s m mb) e

⇒Cong : {a a' b b' : Bool} -> a ≡ a' -> b ≡ b'
       -> a ⇒ᵇ b ≡ a' ⇒ᵇ b'
⇒Cong refl refl = refl

------------------------------------------------------------------------
-- (T2) along the run, and its consequence at every position of an orbit

□Along : (P : Formula) (b c0 : Val) (c1 : List Val)
        -> c0 ∈ Uinf P -> Walk P (Uinf P) c0 c1 b -> step P b c0 ≡ true
        -> (B : Formula) -> □ B ∈ sub P
        -> (t : Nat) (pos : Pos) -> ValidPos P b pos
        -> valOf P (posState pos) (□ B) ≡ true
        -> valOf P (posState (posIter c0 c1 t pos)) (□ B) ≡ true
□Along P b c0 c1 mc0 wc stb B mb zero    pos vp e = e
□Along P b c0 c1 mc0 wc stb B mb (suc t) pos vp e =
  □Along P b c0 c1 mc0 wc stb B mb t (nextPos c0 c1 pos)
           (fst (posStep P b c0 c1 mc0 wc stb vp))
           (carry P (posState pos) (posState (nextPos c0 c1 pos)) B mb
                  (snd (posStep P b c0 c1 mc0 wc stb vp)) e)

□True : (P : Formula) (b c0 : Val) (c1 : List Val)
       -> c0 ∈ Uinf P -> Walk P (Uinf P) c0 c1 b -> step P b c0 ≡ true
       -> (B : Formula) -> □ B ∈ sub P
       -> (pos q : Pos) -> ValidPos P b pos -> q ∈ orbitOf c0 c1 pos
       -> valOf P (posState pos) (□ B) ≡ true
       -> valOf P (posState q) B ≡ true
□True P b c0 c1 mc0 wc stb B mb pos q vp m e =
  fromIter (orbitOf_iter c0 c1 pos q m)
  where
    fromIter : (Σ[ t ∈ Nat ] posIter c0 c1 t pos ≡ q)
            -> valOf P (posState q) B ≡ true
    fromIter (t , et) =
      subst (λ r -> valOf P (posState r) B ≡ true) et
            (□S2 P (posState (posIter c0 c1 t pos))
                   (posIn P b (posIterValid P b c0 c1 mc0 wc stb t pos vp))
                   B mb (□Along P b c0 c1 mc0 wc stb B mb t pos vp e))

------------------------------------------------------------------------
-- Hintikka's lemma

hint : (P : Formula) (b c0 : Val) (c1 : List Val)
    -> c0 ∈ Uinf P -> Walk P (Uinf P) c0 c1 b -> step P b c0 ≡ true
    -> b ∈ c0 ∷ c1
    -> ((s : Val) -> s ∈ b ∷ c0 ∷ c1
          -> (A : Formula) -> A ∈ □Args (sub P)
          -> valOf P s (□ A) ≡ false -> Fulfil P A b (c0 ∷ c1))
    -> (A : Formula) -> A ∈ sub P
    -> (pos : Pos) -> ValidPos P b pos
    -> valOf P (posState pos) A ≡ evalAt P c0 c1 A pos

hint P b c0 c1 mc0 wc stb mbc cyc (var n) mA pos vp = refl

hint P b c0 c1 mc0 wc stb mbc cyc (¬ B) mA pos vp =
  trans (boolEq_sound (valOf P (posState pos) (¬ B))
                      (¬ᵇ valOf P (posState pos) B)
                      (stateOk P (posState pos) (posIn P b vp) mA))
        (cong ¬ᵇ_
              (hint P b c0 c1 mc0 wc stb mbc cyc B (sub_¬ P mA) pos vp))

hint P b c0 c1 mc0 wc stb mbc cyc (B ⇒ C) mA pos vp =
  trans (boolEq_sound (valOf P (posState pos) (B ⇒ C))
                      (valOf P (posState pos) B ⇒ᵇ valOf P (posState pos) C)
                      (stateOk P (posState pos) (posIn P b vp) mA))
        (⇒Cong (hint P b c0 c1 mc0 wc stb mbc cyc B (sub_⇒L P mA) pos vp)
                 (hint P b c0 c1 mc0 wc stb mbc cyc C (sub_⇒R P mA) pos vp))

hint P b c0 c1 mc0 wc stb mbc cyc (○ B) mA pos vp =
  trans (boolEq_sound (valOf P (posState pos) (○ B))
                      (valOf P (posState (nextPos c0 c1 pos)) B)
                      (allStep_at P (posState pos)
                                  (posState (nextPos c0 c1 pos)) (sub P) mA
                                  (snd (posStep P b c0 c1 mc0 wc stb vp))))
        (hint P b c0 c1 mc0 wc stb mbc cyc B (sub_○ P mA)
              (nextPos c0 c1 pos) (fst (posStep P b c0 c1 mc0 wc stb vp)))

hint P b c0 c1 mc0 wc stb mbc cyc (□ B) mA pos vp =
  on□ (valOf P (posState pos) (□ B)) refl
  where
    ih : (q : Pos) -> ValidPos P b q
      -> valOf P (posState q) B ≡ evalAt P c0 c1 B q
    ih q vq = hint P b c0 c1 mc0 wc stb mbc cyc B (sub_□ P mA) q vq

    -- □ B holds: (T2) carries it, (S2) delivers B at every stage
    allTrue : valOf P (posState pos) (□ B) ≡ true
           -> evalAt P c0 c1 (□ B) pos ≡ true
    allTrue e =
      allB_intro (evalAt P c0 c1 B) (orbitOf c0 c1 pos) (λ {q} m -> atQ q m)
      where
        atQ : (q : Pos) -> q ∈ orbitOf c0 c1 pos -> evalAt P c0 c1 B q ≡ true
        atQ q m =
          trans (sym (ih q (orbitValid P b c0 c1 mc0 wc stb pos q vp m)))
                (□True P b c0 c1 mc0 wc stb B mA pos q vp m e)

    -- □ B fails: Lemma 5.4 supplies the false conjunct
    allFalse : valOf P (posState pos) (□ B) ≡ false
            -> evalAt P c0 c1 (□ B) pos ≡ false
    allFalse e =
      fromGF (globalFulfil P b c0 c1 mbc cyc vp B (□Args_of (sub P) mA) e)
      where
        fromGF : (Σ[ q ∈ Pos ] q ∈ orbitOf c0 c1 pos ×
                                   valOf P (posState q) B ≡ false)
              -> evalAt P c0 c1 (□ B) pos ≡ false
        fromGF (q , mq , eq) =
          eval□_false P c0 c1 B pos q mq
            (trans (sym (ih q (orbitValid P b c0 c1 mc0 wc stb pos q vp mq)))
                   eq)

    on□ : (x : Bool) -> valOf P (posState pos) (□ B) ≡ x
         -> valOf P (posState pos) (□ B) ≡ evalAt P c0 c1 (□ B) pos
    on□ true  e = trans e (sym (allTrue e))
    on□ false e = trans e (sym (allFalse e))

------------------------------------------------------------------------
-- Hintikka's lemma on a run, at every stage and at the start

hintRun : (P : Formula) (v0 : Val) (r : Run P v0) (A : Formula) -> A ∈ sub P
       -> (i : Nat) -> valOf P (stateAt P v0 r i) A ≡ eval P v0 r A i
hintRun P v0 (mkRun b c0 c1 mc0 wc stb mbc cyc rest mv0 wr) A mA i =
  hint P b c0 c1 mc0 wc stb mbc cyc A mA
       (posIter c0 c1 i (v0 , rest))
       (posIterValid P b c0 c1 mc0 wc stb i (v0 , rest) (vpos v0 rest mv0 wr))

hintStart : (P : Formula) (v0 : Val) (r : Run P v0) (A : Formula) -> A ∈ sub P
         -> valOf P v0 A ≡ eval P v0 r A 0
hintStart P v0 (mkRun b c0 c1 mc0 wc stb mbc cyc rest mv0 wr) A mA =
  hint P b c0 c1 mc0 wc stb mbc cyc A mA (v0 , rest) (vpos v0 rest mv0 wr)

------------------------------------------------------------------------
-- What the two lemmas together say.
--
-- If a surviving state contains the formula the procedure was run on, that
-- formula is not refutable: Hintikka gives [[P]] = 1 at stage 0 of the lasso,
-- and soundness would give [[¬ P]] = 1 there too.  This is the countermodel
-- half of Theorem 6.1, with only the packaging left for G28.

clash : (x : Bool) -> x ≡ true -> ¬ᵇ x ≡ true -> Empty
clash true  ex ()
clash false () en

notRefutable : (P : Formula) (v0 : Val) (r : Run P v0)
            -> valOf P v0 P ≡ true -> ⊢ ¬ P -> Empty
notRefutable P v0 (mkRun b c0 c1 mc0 wc stb mbc cyc rest mv0 wr) e d =
  clash (evalAt P c0 c1 P (v0 , rest)) holds negated
  where
    r : Run P v0
    r = mkRun b c0 c1 mc0 wc stb mbc cyc rest mv0 wr

    holds : evalAt P c0 c1 P (v0 , rest) ≡ true
    holds = trans (sym (hintStart P v0 r P (sub_self P))) e

    negated : ¬ᵇ evalAt P c0 c1 P (v0 , rest) ≡ true
    negated = soundRun P v0 r d 0

-- and in the form the decision procedure produces it: if the procedure reports
-- P satisfiable -- some surviving state contains P -- then ¬ P is not
-- derivable in L.  No enumeration of derivations is involved; the lasso through
-- that state is the certificate.

notRefutableSat : (P : Formula) -> satB P ≡ true -> ⊢ ¬ P -> Empty
notRefutableSat P e d = go (anyL_true (λ v -> valOf P v P) (Uinf P) e)
  where
    go : (Σ[ v ∈ Val ] v ∈ Uinf P × valOf P v P ≡ true) -> Empty
    go (v , m , ev) = notRefutable P v (runOf P v m (lasso P v m)) ev d

------------------------------------------------------------------------
-- Checkpoint.
--
-- ◇ p is consistent: ¬ ◇ p has no derivation in L.  This is a THEOREM,
-- not a computation -- the certificate is the two-state lasso of LTL.Lasso, and
-- the proof is Hintikka's lemma at stage 0 against soundness.

◇P_consistent : ⊢ ¬ ◇P -> Empty
◇P_consistent = notRefutableSat ◇P satB_◇P
