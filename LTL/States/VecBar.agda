{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.States.VecBar -- valuations of a given length are inductively finite,
-- and the guard that keeps the searches over them cheap.

module LTL.States.VecBar where

open import LTL.States.Reach public

------------------------------------------------------------------------
-- Vectors of a given length are inductively finite -- in O(n), not 2^n.  A
-- valuation of length n+1 is a Bool paired with one of length n, so barProd
-- applies, and barPull transports the result back along uncons.  allVecs never
-- appears.

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

unconsNeq : (m : Nat) (y z : Val) -> hasLength (suc m) y ≡ true
         -> hasLength (suc m) z ≡ true -> y ≢ᵛ z ≡ true
         -> prodRel _≢ᵇ_ _≢ᵛ_ (unconsV y) (unconsV z) ≡ true
unconsNeq m []      z       () ez e
unconsNeq m (b ∷ v) []      ey () e
unconsNeq m (b ∷ v) (c ∷ w) ey ez e = ¬ᵇ-∧ᵇ (b ⇔ᵇ c) (v ≡ᵛ w) e

vecIFin : (n : Nat) -> IFin (hasLength n)
vecIFin zero =
  cBar (λ x ex -> cBar (λ y ey ->
    emptyElim (clash x y ex (∧ᵇ-trueˡ (hasLength zero y) (x ≢ᵛ y) ey)
                            (∧ᵇ-trueʳ (hasLength zero y) (x ≢ᵛ y) ey))))
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
  barMono (λ v ev -> ∧ᵇ-intro (hasLength (suc m) v)
                              (prodPred (λ b -> true) (hasLength m) (unconsV v))
                              ev (lenTail m v ev))
          (barPull unconsV (hasLength (suc m)) (unconsNeq m)
                   (barProd boolIFin (vecIFin m)))


------------------------------------------------------------------------
-- Members of allVecs n have length n, so the length-n predicate is a correct
-- Bar predicate for St P, and the search never touches the enumeration.

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
-- The guard of Barras, refined by Gonthier (Coquand and Siles, section 5).
--
-- A function defined by recursion on a Bar forces the Bar as it runs.  vecIFin
-- gives the Pi-form a guard needs (every subset of the length-n vectors is Bar
-- by barMono), and guardBar k supplies 2^k constructors lazily, so a search of
-- depth below 2^k never touches vecIFin.

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
             (λ v ev -> sb v (∧ᵇ-trueˡ (E v) (x ≢ᵛ v) ev)))

-- The guard depth is n itself.  A search choosing distinct vectors of length n
-- runs at most 2^n steps, so k = n is exactly enough.  A literal depth would
-- be worse: guardBar k unfolds to 2^k copies, and Agda normalises the
-- constructor types of data types that mention U_inf (Walk, Lasso, Run,
-- ValidPos).  With k = n and P a variable the match on k is blocked and the
-- guard stays folded; on a closed formula n reduces and the guard does its
-- job.

guardedVecBar : (n : Nat) -> AllBar n
guardedVecBar n = guardBar n n (allVecBar n)
