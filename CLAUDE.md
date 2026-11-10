# CLAUDE.md

Constructive LTL decision procedures in Agda. Given `Q : Formula`, the
procedures return `Sum (Deriv Q) (LassoCountermodel Q)`: a Hilbert-style
derivation or a certified finite lasso countermodel.

## Ground rules

- Agda 2.8.0, **no standard library**. Every file starts with
  `{-# OPTIONS --safe --without-K --exact-split #-}`. Keep it that way: no
  postulates, holes, or termination pragmas.
- Typecheck from the repository root, e.g. `agda -i . LTL/DecideSCC.agda`
  (see README for the full list). `Examples`, `Compare`, `Lecture`, `Proofs`
  are benchmarks and are slow; the core proof modules should stay fast.
- Language: `var n`, `¬ A`, `A ⇒ B`, `○ A` (next), `□ A` (always). `A ∧ B`,
  `A ∨ B`, `A ⇔ B`, `◇ A`, `⊥`, `⊤` are abbreviations (`LTL/Formula.agda`;
  `⋀`/`⋁` over lists in `LTL/Val.agda`). Implication is `⇒` because Agda
  reserves `→`. Lemma names use the same symbols (`⇒Trans`, `□Elim`, `k□`).
  **Until is not implemented** (it is the thesis goal).
- Module headers cite goals G1–G40 of `FORMALISATION-PLAN.md` /
  `PHASE11-PLAN.md` (gitignored, not in the repo) and the lemma/theorem numbers
  of `m4.tex` / `m5.tex`. Keep that comment style: long header comments that
  tie the code to the note.

## Documents

- `docs/ltl-master-thesis.tex` — thesis proposal (learn LTL, clarify the proof,
  add Until, semantics, readable proofs).
- `m4.tex` — elimination-based procedure: system L (§1), states/transitions
  (§2), elimination (§3), extraction Thm 4.1 (§4), lasso branch (§5),
  decidability Thm 6.1 (§6).
- `m5.tex` — SCC / fair-graph certificate procedure and comparison with m4.

## Module index (`LTL/`, in dependency order)

1. **Foundations** — `Base` (Nat, Bool, Empty, Unit, Eq); `Prelude` (Sum,
   Sigma, Prod, List, Mem, index/nth, Boolean lemmas).
2. **Syntax and proof system** — `Formula` (datatype, abbreviations, decidable
   `formEq`); `Sub` (subformula list `sub`); `Skel` (propositional skeleton,
   `isTaut` for (PC)); `Deriv` (`data Deriv`: 10 constructors + optional `pc`).
3. **Derived rules (m4 Lemmas 1.1–1.2)** — `Prop` (L0–L7 via
   `identP`/`liftP`/`mpU`, no deduction theorem); `PropList` (`⋁Elim`,
   `⋁Drop`, `splitD`); `Temporal` (D1–D6, `expConv`, `indRule`).
4. **States and transitions (m4 §2)** — `Val` (valuations, `chi`, `beta`);
   `State` (`isState`, `St P`); `Step` (`step`, `succs`, T1–T3); `Taut`
   (Boolean facts about chi/beta for (PC)); `Proj`, `NonState`, `Complete`
   (`stateComplete`, Lemmas 2.5–2.6); `StepLemma` (Lemmas 2.7–2.8).
5. **Finite search infrastructure** — `Reach`, `Sets` (set ops,
   reachability); `Bar` (inductively finite sets after Coquand–Siles; all
   searches recurse on a Bar); `Closure` (`Ust`, the explored state set).
6. **Elimination / provable branch (m4 §3–4)** — `Gfp` (set W, `Path`);
   `Elim` (R1/R2, `Uinf`, `satB`); `Trace` (removal reasons); `Extract`
   (`extract`, `provable`, Thm 4.1).
7. **Lasso countermodel branch (m4 §5)** — `Walk`; `Fix` (Lemma 5.1); `Round`;
   `Lasso` (Prop 5.3); `Run`; `Global` (Lemma 5.4); `Eval`; `Sound`; `Hintikka`.
8. **Decision procedures** — `Decide` (`decide`, Thm 6.1); `Graph` (generic
   `fairGraph` certificate theorem, largest module); `SccLasso`, `SccExtract`,
   `SccTrap` (graph ↔ logic translation); `DecideSCC` (`decideSCC`);
   `CompletePC`, `ShortPC` (`decidePC`, short certificates via (PC)).
9. **Examples and benchmarks** — `Examples` (46 formulas, Schmitt &
   Goubault-Larrecq Fig. 11); `Lecture` (`F a ∧ F b → F(a∧b)`); `Compare`
   (decide vs decideSCC on 47 formulas); `Proofs` (prints and measures
   certificates).

## Public API

- `decide` (`LTL/Decide.agda`), `decideSCC` (`LTL/DecideSCC.agda`),
  `decidePC` (`LTL/ShortPC.agda`) — all of type
  `(Q : Formula) -> Sum (Deriv Q) (LassoCountermodel Q)`.

## Adding Until (expected touch points)

`Formula` → `Sub` → `Deriv` → `State`/`Step` → eventualities in `Elim`
(currently indexed by box-subformulas) → `Eval`/`Sound`/`Hintikka` → the SCC
fairness predicates in `SccLasso`.
