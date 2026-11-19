# CLAUDE.md

Constructive LTL decision procedures in Agda. Given `Q : Formula`, the
procedures return `⊢ Q ⊎ LassoCountermodel Q`: a Hilbert-style
derivation or a certified finite lasso countermodel.

## Ground rules

- `LTL/Trusted.agda` is the user's hand-checked specification (LTL
  semantics, `valid`, `LassoCounterModel`, `DecisionProcedure`). **Never edit
  it**; if it needs a change, tell the user. `Formula` is its datatype
  (re-exported by `LTL/Syntax/Formula.agda` with this development's fixities), and
  `Bool`/`List` are Agda's builtins, so its `Instant`/`Period` use our types.
  Import it qualified (`import LTL.Trusted as T`) because its other names clash.
- Agda 2.8.0, **no standard library**. Every file starts with
  `{-# OPTIONS --safe --without-K --exact-split #-}`. Keep it that way: no
  postulates, holes, or termination pragmas. Agda's own `Agda.Builtin.*`
  modules are fine (`Base` re-exports `Agda.Builtin.Nat`).
- Typecheck from the repository root, e.g. `agda -i . LTL/Correct.agda`
  (see README for the full list). The modules in `LTL/Benchmarks/`
  (`Examples`, `Lecture`) are slow; the core proof
  modules should stay fast.
- Language: `var n`, `¬ A`, `A ⇒ B`, `○ A` (next), `□ A` (always). `A ∧ B`,
  `A ∨ B`, `A ⇔ B`, `◇ A`, `⊥`, `⊤` are abbreviations (`LTL/Syntax/Formula.agda`;
  `⋀`/`⋁` over lists in `LTL/States/Val.agda`). Implication is `⇒` because Agda
  reserves `→`. Lemma names use the same symbols (`⇒Trans`, `□Elim`, `k□`).
  **Until is not implemented** (it is the thesis goal).
- Prelude notation follows Agda's standard library: `x ≡ y` (`sym`, `trans`,
  `cong`, `subst`), `A ⊎ B` (`inl`/`inr`), `Σ[ x ∈ A ] B` and `A × B` (both
  built with `_,_`; `fst`/`snd`), `x ∷ xs`, `xs ++ ys`, `x ∈ xs`
  (`here`/`there`), `xs ⊆ ys`, `m < n`, `m ≤ n`, `m + n`, `m ∸ n`,
  `if b then x else y`, and list helpers `filter any all null concat`.
  Boolean-valued operators carry a superscript naming their domain:
  connectives `∧ᵇ ∨ᵇ ¬ᵇ ⇒ᵇ ⇔ᵇ ≢ᵇ` on Bool (the plain symbols are the LTL
  connectives); tests `n ≡ⁿ m`, `n ≤ⁿ m` on Nat, `v ≡ᵛ w`, `v ≢ᵛ w`,
  `v ∈ᵛ us` on nodes (`LTL/Lib/Nodes.agda`; valuations at the `Val` instance made in
  `LTL/States/Reach.agda`), `A ≡ᶠ B`, `A ∈ᶠ As` on formulas (all `infix 4.5`,
  so `v ∈ᵛ us ≡ true` needs no parentheses). Lemmas about a symbol use the
  stdlib hyphen style (`∈ᵛ-sound`, `≡ᶠ-refl`); never `foo_bar`, which Agda
  reads as a mixfix operator. The Boolean lemmas, all in the "Boolean lemmas"
  section of `LTL/Lib/Prelude.agda`, follow one scheme: `∧ᵇ-trueˡ`, `∧ᵇ-split`,
  `∨ᵇ-introʳ`, `¬ᵇ-true`, `⇒ᵇ-mp`, `⇔ᵇ-complete`; add new ones there. `⊢ A` (`data ⊢_` in
  `LTL/Syntax/Deriv.agda`) is derivability. `Empty`/`Unit` keep their names, because
  `⊥`/`⊤` are formulas. Function types and lambdas stay ASCII (`->`) apart from
  `λ`.
- Signatures: use the named hypotheses instead of spelling them out:
  `Pred`/`Edges` (`Node -> Bool`, `Node -> Node -> Bool`), `xs ⊆ ys`,
  `Closed ws G C`, `NoneSat f C`, `HoldsOutside R ws`, `AllSat`/`Avail`
  (all `LTL/Lib/Nodes.agda`), `FulfilledAt`/`AllFulfilled`
  (`LTL/Countermodel/Walk.agda`). A run of lemmas that share leading arguments, passed on
  unchanged, sits in a `module _ (ws : List Val) (G : Edges) where` block, so
  callers outside see the same arguments.
- Names: prefer a readable name to an abbreviation. Names that follow the notes
  (`St`, `Ust`, `Uinf`, `r1`/`r2`, `gfpW`, `wZero`, `chi`, `beta`) stay, with a
  comment at the definition. The search conventions (`fooGo`/`fooFind`, the
  `sb`/`bar`/`av` binders) are explained above `AllSat` in `LTL/Lib/Nodes.agda`.
- Module headers cite goals G1–G40 of `FORMALISATION-PLAN.md` /
  `PHASE11-PLAN.md` (gitignored, not in the repo; `docs/plan-index.md` lists
  where each goal and checkpoint lives) and the lemma/theorem numbers of
  `m4.tex` / `m5.tex`. Keep that comment style: long header comments that tie
  the code to the note. Describe the code as it is, not how it got there:
  development history belongs in git, not in comments.
- Computational `refl` checks go in `LTL/Tests/Checks.agda` (one section per module)
  or `LTL/Tests/GraphExamples.agda`, not in the proof modules.

## Documents

- `docs/ltl-master-thesis.tex` — thesis proposal (learn LTL, clarify the proof,
  add Until, semantics, readable proofs).
- `docs/m4.tex` — elimination-based procedure: system L (§1), states/transitions
  (§2), elimination (§3), extraction Thm 4.1 (§4), lasso branch (§5),
  decidability Thm 6.1 (§6).
- `docs/m5.tex` — SCC / fair-graph certificate procedure and comparison with m4.
- `docs/methodology.md` — how the project is worked on, and how AI is used.

## Module index (`LTL/`, in dependency order)

Each layer lives in its own folder, and a module's name follows its path
(`LTL/Syntax/Formula.agda` is `LTL.Syntax.Formula`). The `LTL/` root holds
only `Trusted`, `Semantics`, `Correct` and `Pretty`. Folder names never equal
a module name.

0. **Specification** (root) — `Trusted` (read-only, see above).
1. **Foundations** (`Lib/`) — `Base` (Nat and Bool from `Agda.Builtin`, Empty, Unit,
   `≡`); `Prelude` (`⊎`, `Σ`, `×`, List from `Agda.Builtin.List`, `∈`, `⊆`,
   `<`, index/nth, Boolean connectives and all Boolean lemmas, `refuteTrue`).
   Generic set layer, importing only `Prelude` and used by the graph layer at
   any node type: `Sets` (`≤`, `FindResult`, filter/any/all lemmas); `Bar`
   (inductively finite sets after Coquand–Siles, closure lemmas; all searches
   recurse on a Bar); `Nodes` (parameterised by a node type and a sound,
   reflexive equality test `_≡ᵛ_`: `∈ᵛ`, `≢ᵛ`, `IFin`, `listBar`, the
   hypothesis names).
2. **Syntax and proof system** (`Syntax/`) — `Formula` (`Trusted`'s datatype,
   abbreviations, decidable `≡ᶠ`); `Sub` (subformula list `sub`); `Skel` (propositional skeleton,
   `isTaut` for (PC)); `Deriv` (`data ⊢_`: 10 constructors + optional `pc`).
3. **Derived rules (m4 Lemmas 1.1–1.2)** (`Rules/`) — `Prop` (L0–L7 via
   `⇒Refl`/`liftP`/`mpU`, no deduction theorem); `PropList` (`⋁Elim`,
   `⋁Drop`, `splitD`); `Temporal` (D1–D6, `expConv`, `indRule`).
4. **States and transitions (m4 §2)** (`States/`, with layer 5) — `Val` (valuations, `chi`, `beta`);
   `State` (`isState`, `St P`); `Step` (`step`, `succs`, T1–T3); `Taut`
   (Boolean facts about chi/beta for (PC)); `Proj`, `NonState`, `Complete`
   (`stateComplete`, Lemmas 2.5–2.6); `StepLemma` (Lemmas 2.7–2.8).
5. **Finite search infrastructure** (`States/`) — `Reach` (`≡ᵛ` on valuations, the
   `Val` instance of `Nodes`, successor lists); `VecBar` (valuations of a given
   length are inductively finite, `guardedVecBar`); `Closure` (`Ust`, the
   explored state set).
6. **Elimination (m4 §3–4)** (`Elimination/`) — `Gfp` (set W, `Path`);
   `Elim` (R1/R2, `Uinf`; survivors are states); `Extract` (`betaElim`,
   `Refuted`, `extractR1`: the pieces of Thm 4.1 that `SccExtract` reuses).
   The elimination is only run in the fair branch of `decideSCC`, to place the
   countermodel's loop inside `Uinf` (`uinfTrap`).
7. **Lasso countermodel branch (m4 §5)** (`Countermodel/`) — `Orbit` (positions `(s , rest)`,
   `nextPos`, forward orbits; parameterised by the state type, mirroring
   `Trusted`'s `Position`/`step`); `LassoEval` (Boolean `evalAt` and its
   soundness on a lasso of any state type, parameterised by `read`); `Walk`;
   `Lasso` (the record of Prop 5.3); `Run` (`Orbit` at `Val`);
   `Global` (Lemma 5.4); `Eval` (`LassoEval` at `Val`); `Sound`; `Hintikka`.
8. **Decision procedure** — in `SCC/` (m5): `Graph` (the `fairGraph`
   certificate theorem, largest module; parameterised like `Nodes`, imports
   only the generic layer, instantiated at `Val` in `SccLasso`); `SccLasso`,
   `SccExtract` (`provableSCC`, closed with (PC)), `SccTrap` (graph ↔ logic
   translation). In `Procedures/`: `CompletePC` (`stateCompletePC`,
   `betaElimPC`: Lemma 2.6 and (L5) via (PC)); `Answer` (`LassoCountermodel`,
   `isProof`, `lassoOf`, `cmFrom`, `derivCounts`); `DecideSCC` (`decideSCC`,
   Thm 6.1; `traceOf`, `shapeOf`). At the root:
   `Semantics` (`evalAt` agrees with `Trusted`'s `⊨`; `⊢-valid`,
   `toCounterModel`, `fromDecider`); `Correct` (`decideSCC` as a
   `Trusted.DecisionProcedure`).
9. **Examples and benchmarks** — in `Tests/` (fast): `Checks` (the core
   modules' `refl` checks and example formulas: `benAri`, `◇P`, `bnb`, `c5`,
   …); `GraphExamples` (Graph's computational checks, at `Node = Nat`). In
   `Benchmarks/` (slow): `Examples` (46 formulas, Schmitt & Goubault-Larrecq
   Fig. 11); `Lecture` (`F a ∧ F b → F(a∧b)`).
10. **Readable output** (root) — `Pretty` (`prove`, `proveTree`, `proveLines`:
   decideSCC results as numbered Hilbert proofs, trees, or lasso countermodels,
   rendered to `Agda.Builtin.String`; this is why `Base` takes `Nat` from
   `Agda.Builtin.Nat`). `tools/show-proof` runs it from the terminal via
   `agda --interaction-json`. Rendering is slow for large certificates.

## Public API

- `decideSCC` (`LTL/Procedures/DecideSCC.agda`) — of type
  `(Q : Formula) -> ⊢ Q ⊎ LassoCountermodel Q` (`LTL/Procedures/Answer.agda`).
- `decideSCCCorrect` (`LTL/Correct.agda`) — the same procedure as a
  `Trusted.DecisionProcedure`. Any procedure of the type above gets one from
  `fromDecider` (`LTL/Semantics.agda`).

## Adding Until (expected touch points)

`Trusted` (the constructor and its `⊨` clause; the user must make that change)
→ `Formula` → `Sub` → `Deriv` → `State`/`Step` → eventualities in `Elim`
(currently indexed by box-subformulas) → `LassoEval`/`Semantics`/`Hintikka` →
the SCC fairness predicates in `SccLasso`.
