{-# OPTIONS --safe --without-K --exact-split #-}

-- LTL.Proj -- the bridge from the boolean world to the derivation world.
--
-- Everything in Phase 4 has the same shape: a boolean condition fails, so some
-- conjunct of chi P v carries a particular literal, so chi P v is refutable.
-- The three ingredients are here:
--
--   * searching a false conjunction for the offending index (allOk_false,
--     allCoh_false, both now in LTL.State), and the corresponding projections;
--   * cohLookup, which says that under coherence the bit at ANY occurrence of
--     a formula equals valOf, so positional chi and lookup-based conditions
--     talk about the same bits;
--   * chiProj / chiProjPos, which turn a membership proof or a position into
--     ⊢ chi P v ⇒ <literal>.

module LTL.Proj where

open import LTL.Temporal public
open import LTL.State    public

------------------------------------------------------------------------
-- Refutation from a formula and its negation

refute : {C B : Formula} -> ⊢ C ⇒ B -> ⊢ C ⇒ ¬ B -> ⊢ ¬ C
refute f g = mp (¬IntroU (liftP f) (liftP g)) deriv⊤

------------------------------------------------------------------------
-- Under coherence, every occurrence of A carries the bit valOf P v A

cohLookup : (P : Formula) (v : Val)
         -> allCoh P v (length (sub P)) ≡ true
         -> {A : Formula} (h : A ∈ sub P)
         -> bitAt v (index h) ≡ valOf P v A
cohLookup P v ch {A} h =
  trans (boolEq_sound (bitAt v (index h))
                      (valOf P v (nth (sub P) (index h) ⊥))
                      (allCoh_at P v (length (sub P)) (index h)
                                 (index_length h) ch))
        (cong (valOf P v) (index_nth h ⊥))

------------------------------------------------------------------------
-- Projection of a conjunct out of chi

chiProjRaw : (P : Formula) (v : Val)
          -> length v ≡ length (sub P)
          -> {A : Formula} (h : A ∈ sub P)
          -> ⊢ (chi P v) ⇒ (lit A (bitAt v (index h)))
chiProjRaw P v len h =
  ⋀Proj (litList (sub P) v) (litList_mem (sub P) v len h)

chiProj : (P : Formula) (v : Val)
       -> length v ≡ length (sub P)
       -> allCoh P v (length (sub P)) ≡ true
       -> {A : Formula} (h : A ∈ sub P)
       -> ⊢ (chi P v) ⇒ (lit A (valOf P v A))
chiProj P v len ch {A} h =
  subst (λ b -> ⊢ (chi P v) ⇒ (lit A b))
        (cohLookup P v ch h)
        (chiProjRaw P v len h)

------------------------------------------------------------------------
-- Positional projection, for the coherence-failure case, where cohLookup is
-- exactly what is NOT available.

litList_nth : (As : List Formula) (v : Val) (i : Nat)
           -> i < length As -> length v ≡ length As
           -> lit (nth As i ⊥) (bitAt v i) ∈ litList As v
litList_nth []       v       i       ()        len
litList_nth (A ∷ As) []      i       lt        ()
litList_nth (A ∷ As) (b ∷ v) zero    lt        len = here
litList_nth (A ∷ As) (b ∷ v) (suc i) (ltSuc l) len =
  there (litList_nth As v i l (sucInj len))

chiProjPos : (P : Formula) (v : Val)
          -> length v ≡ length (sub P)
          -> (i : Nat) -> i < length (sub P)
          -> ⊢ (chi P v) ⇒ (lit (nth (sub P) i ⊥) (bitAt v i))
chiProjPos P v len i lt =
  ⋀Proj (litList (sub P) v) (litList_nth (sub P) v i lt len)

------------------------------------------------------------------------
-- The first-occurrence index is a genuine position carrying its formula.
--
-- valOf P v X is the bit at position  idx (sub P) X , so to project the
-- literal of X signed by valOf, without coherence, we need that this position
-- is in range and carries X.

idx_lt : (xs : List Formula) {X : Formula} -> X ∈ xs -> idx xs X < length xs
idx_lt []       ()
idx_lt (B ∷ Bs) here     = aux (formEq B B) (formEq_refl B)
  where
    aux : (b : Bool) -> b ≡ true -> idxCons b (idx Bs B) < suc (length Bs)
    aux true  e  = ltZero
    aux false ()
idx_lt (B ∷ Bs) {X} (there m) = aux (formEq B X)
  where
    aux : (b : Bool) -> idxCons b (idx Bs X) < suc (length Bs)
    aux true  = ltZero
    aux false = ltSuc (idx_lt Bs m)

idx_nth : (xs : List Formula) {X : Formula} -> X ∈ xs
       -> nth xs (idx xs X) ⊥ ≡ X
idx_nth []       ()
idx_nth (B ∷ Bs) here     = aux (formEq B B) (formEq_refl B)
  where
    aux : (b : Bool) -> b ≡ true
       -> nth (B ∷ Bs) (idxCons b (idx Bs B)) ⊥ ≡ B
    aux true  e  = refl
    aux false ()
idx_nth (B ∷ Bs) {X} (there m) = aux (formEq B X) (formEq_sound B X)
  where
    aux : (b : Bool) -> (b ≡ true -> B ≡ X)
       -> nth (B ∷ Bs) (idxCons b (idx Bs X)) ⊥ ≡ X
    aux true  f = f refl
    aux false f = idx_nth Bs m

-- Projection signed by valOf, available without coherence.

chiProjVal : (P : Formula) (v : Val)
          -> length v ≡ length (sub P)
          -> {X : Formula} (m : X ∈ sub P)
          -> ⊢ (chi P v) ⇒ (lit X (valOf P v X))
chiProjVal P v len {X} m =
  subst (λ Y -> ⊢ (chi P v) ⇒ (lit Y (bitAt v (idx (sub P) X))))
        (idx_nth (sub P) m)
        (chiProjPos P v len (idx (sub P) X) (idx_lt (sub P) m))
