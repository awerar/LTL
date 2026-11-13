{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.VecBar -- valuations of a given length are inductively finite, and the
-- guard that makes the searches over them cheap.  This is the Val-specific half
-- of what was LTL.Bar: the generic half (Bar and its closure lemmas) is
-- LTL.Bar, and the inductive finiteness of a list (barOfList, listBar) is
-- LTL.Nodes, instantiated at Val in LTL.Reach.

module LTL.VecBar where

open import LTL.Reach public

------------------------------------------------------------------------
-- Vectors of a given length are inductively finite -- in O(n), not 2^n.
--
-- This is the point of the file.  A valuation of length n+1 is a Bool paired
-- with a valuation of length n, so barProd applies, and barPull transports the
-- result back along uncons.  The recursion is on n; allVecs never appears.

-- v has length n, as a boolean predicate (so that it can be a Bar's E).

hasLength : Nat -> Val -> Bool
hasLength n v = length v ≡ⁿ n

headV : Val -> Bool
headV []      = false
headV (b ∷ v) = b

tailV : Val -> Val
tailV []      = []
tailV (b ∷ v) = v

unconsV : Val -> Bool × Val
unconsV v = headV v , tailV v

lenZero : (v : Val) -> length v ≡ⁿ zero ≡ true -> v ≡ []
lenZero []      e = refl
lenZero (b ∷ v) ()

lenTail : (m : Nat) (v : Val) -> hasLength (suc m) v ≡ true
       -> hasLength m (tailV v) ≡ true
lenTail m []      ()
lenTail m (b ∷ v) e = e

deMorgan : (a b : Bool) -> ¬ᵇ (a ∧ᵇ b) ≡ true
        -> ¬ᵇ a ∨ᵇ ¬ᵇ b ≡ true
deMorgan true  true  ()
deMorgan true  false e = refl
deMorgan false b     e = refl

unconsNeq : (m : Nat) (y z : Val) -> hasLength (suc m) y ≡ true
         -> hasLength (suc m) z ≡ true -> y ≢ᵛ z ≡ true
         -> prodRel _≢ᵇ_ _≢ᵛ_ (unconsV y) (unconsV z) ≡ true
unconsNeq m []      z       () ez e
unconsNeq m (b ∷ v) []      ey () e
unconsNeq m (b ∷ v) (c ∷ w) ey ez e = deMorgan (b ⇔ᵇ c) (v ≡ᵛ w) e

vecIFin : (n : Nat) -> IFin (hasLength n)
vecIFin zero =
  cBar (λ x ex -> cBar (λ y ey ->
    emptyElim (clash x y ex (andTrueL (hasLength zero y) (x ≢ᵛ y) ey)
                            (andTrueR (hasLength zero y) (x ≢ᵛ y) ey))))
  where
    clash : (x y : Val) -> hasLength zero x ≡ true -> hasLength zero y ≡ true
         -> x ≢ᵛ y ≡ true -> Empty
    clash x y ex ey e = true≢false (sym nil2)
      where
        -- both are [], and [] ≢ᵛ [] is false
        nil2 : [] ≢ᵛ [] ≡ true
        nil2 = subst (λ u -> u ≢ᵛ [] ≡ true) (lenZero x ex)
                     (subst (λ u -> x ≢ᵛ u ≡ true) (lenZero y ey) e)
vecIFin (suc m) =
  barMono (λ v ev -> andIntro (hasLength (suc m) v)
                              (prodPred (λ b -> true) (hasLength m) (unconsV v))
                              ev (lenTail m v ev))
          (barPull unconsV (hasLength (suc m)) (unconsNeq m)
                   (barProd boolIFin (vecIFin m)))


------------------------------------------------------------------------
-- Members of allVecs n have length n.
--
-- Needed to hand guardedVecBar the states: St P is a subset of allVecs
-- (length (sub P)), so the length-n predicate is a correct E for it, and then
-- the search never touches the enumeration.

allVecs-len : (n : Nat) {v : Val} -> v ∈ allVecs n -> hasLength n v ≡ true
allVecs-len zero    here      = refl
allVecs-len zero    (there ())
allVecs-len (suc n) m =
  sumElim (fromHalf true) (fromHalf false)
          (memAppCase (map (λ bs -> true  ∷ bs) (allVecs n))
                      (map (λ bs -> false ∷ bs) (allVecs n)) m)
  where
    fromHalf : {v : Val} (b : Bool) -> v ∈ map (λ bs -> b ∷ bs) (allVecs n)
            -> hasLength (suc n) v ≡ true
    fromHalf {v} b mv = fromSig (map-mem-inv (λ bs -> b ∷ bs) (allVecs n) mv)
      where
        fromSig : (Σ[ w ∈ Val ] w ∈ allVecs n × v ≡ b ∷ w)
               -> hasLength (suc n) v ≡ true
        fromSig (w , mw , ew) =
          subst (λ u -> hasLength (suc n) u ≡ true) (sym ew) (allVecs-len n mw)

stAllSat : (P : Formula) -> AllSat (hasLength (length (sub P))) (St P)
stAllSat P x m =
  allVecs-len (length (sub P))
              (filter-sub (isState P) (allVecs (length (sub P))) m)

------------------------------------------------------------------------
-- The guard of Barras, refined by Gonthier (siles.pdf, section 5).
--
-- The paper's point is that one computes with the decision procedure DIRECTLY,
-- as a type-theoretic boolean function, without extracting to ML.  It also
-- records the price: a function defined by recursion on a well-foundedness
-- proof forces that proof as it runs, "and this computation is heavy, and
-- furthermore seems irrelevant, since the accessibility predicate has only one
-- constructor".
--
-- Their fix transfers, and the reason it transfers is worth stating.  Barras's
-- guard works on `well_founded`, a Pi-type, so a guarded proof can produce a
-- constructor without ever applying the proof it wraps.  Bar R E at a FIXED E
-- is a tree, not a function, and admits no such trick -- but vecIFin gives the
-- Pi-form we need, since every subset of the length-n vectors is Bar by
-- barMono.  guardBar k then supplies 2^k constructors lazily, so a search of
-- depth below 2^k never touches vecIFin at all.

AllBar : Nat -> Set
AllBar n = (E : Pred)
        -> ((v : Val) -> E v ≡ true -> hasLength n v ≡ true) -> IFin E

allVecBar : (n : Nat) -> AllBar n
allVecBar n E sb = barMono sb (vecIFin n)

guardBar : (n k : Nat) -> AllBar n -> AllBar n
guardBar n zero    w = w
guardBar n (suc k) w =
  λ E sb -> cBar (λ x ex ->
    guardBar n k (guardBar n k w)
             (λ y -> E y ∧ᵇ (x ≢ᵛ y))
             (λ v ev -> sb v (andTrueL (E v) (x ≢ᵛ v) ev)))

-- The guard depth is n itself, and that is not a cosmetic choice.
--
-- Two things fix it.  A search that keeps choosing DISTINCT vectors of length n
-- runs for at most 2^n steps, and guardBar n k supplies 2^k constructors, so
-- k = n is exactly enough: for |Sub P| = 13 the guard alone carries 8192 peels
-- and vecIFin is never reached.
--
-- More importantly, a literal depth is unusable.  guardBar n k unfolds to 2^k
-- copies of what it wraps, so with k a literal the NORMAL FORM of the guarded
-- Bar has 2^k nodes -- and Agda normalises the constructor types of a data
-- declaration, so every data type whose constructors mention U_infinity
-- (SuccInUinf, Escape, Walk, Round, Lasso, Run, ValidPos: most of Phases 5 and
-- 6) would normalise it.  With k = n and P a variable the match on k is
-- blocked, the guard stays folded, and the explosion cannot happen; on a closed
-- formula n reduces and the guard does its job.  Laziness has to be arranged
-- in the term, not merely relied on in the evaluator.

guardedVecBar : (n : Nat) -> AllBar n
guardedVecBar n = guardBar n n (allVecBar n)
