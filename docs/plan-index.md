# Index of plan citations

The module headers and comments cite the working plans of the original
development: goals G0–G40 and sections of `FORMALISATION-PLAN.md`, and of
`PHASE10-PLAN.md` and `PHASE11-PLAN.md` for the later goals, together with
phases (1–10) and checkpoints (C1–C8). The plans are not part of this
repository. This index lists, for each citation, the modules that implement or
measure it. The one-line descriptions are read off those modules, not copied
from the plans. Plan sections cited in comments (for example "section 4g") are
not reproduced here.

## Goals

| Goal | What it is in the code | Modules |
|---|---|---|
| G0 | the benchmark formulas | `Examples` |
| G1 | formulas, abbreviations, decidable `≡ᶠ` | `Formula` |
| G2 | subformula list `sub`; the index/nth round-trip | `Sub`, `Prelude`, `Skel`, `Val` |
| G3 | derivations `⊢_` (system L) | `Deriv` |
| G4 | valuations, `chi`, `beta` | `Val` |
| G5 | states and the duplicate-coherence clause | `State` |
| G6 | the transition relation (T1)–(T3) | `Step` |
| G7 | `Reach_U(v)`; replaced by the greatest fixed point of `Gfp` | `Reach`, `Gfp` |
| G8 | the elimination (R1)/(R2), `Uinf`, `satB` | `Elim` |
| G9, G10 | Lemma 1.1, list-free part: (L0), (L1), (L3), (L4), (L7) | `Prop` |
| G11–G13 | Lemma 1.1, list part: (L2), (L5), (L6) | `PropList` |
| G14, G15 | Lemma 1.2: (D1)–(D6) | `Temporal` |
| G16 | Lemma 2.5: non-states are refutable | `NonState` |
| G17 | Lemma 2.6: state completeness | `Complete`, `Closure` |
| G18, G19 | Lemmas 2.7 and 2.8: the step lemma, persistence | `StepLemma` |
| G20 | why each state was removed | `Trace` |
| G21 | Theorem 4.1: extraction | `Extract` |
| G22 | rounds | `Round`, `Walk` |
| G23 | Proposition 5.3: the lasso | `Lasso`, `Walk` |
| G24 | Lemma 5.4; runs and their orbits | `Global`, `Run`, `Orbit` |
| G25 | evaluation on a run, and on any lasso | `Eval`, `LassoEval` |
| G26 | soundness; against `Trusted`'s semantics | `Sound`, `LassoEval`, `Semantics` |
| G27 | Hintikka's lemma | `Hintikka` |
| G28 | Theorem 6.1: `decide` | `Decide` |
| G29 | searches by recursion on a Bar | `Bar`, `Nodes`, `Gfp`, `Elim`, `Fix`, `Lasso` |
| G30 | the explored state set `Ust` | `Closure` |
| G31, G32 | (PC) and the short Lemma 2.6 | `Taut`, `CompletePC` |
| G34 | the provable branch as one (PC) node | `ShortPC` |
| G35 | `chi` over atoms | `ShortPC` |
| G37 | the finite fair-graph certificate theorem | `Graph` |
| G38 | an accepting component gives a lasso | `SccLasso` |
| G39 | a certificate gives refutations | `SccExtract` |
| G40 | `decideSCC` | `DecideSCC`, `SccTrap` |

No module cites G33 or G36.

## Checkpoints

| Checkpoint | Where it is checked |
|---|---|
| C1 | the elimination on small examples (`Checks`, section `LTL.Elim`) |
| C2 | double negation as a derivation (`Proofs`) |
| C4 | `decide` on Ben-Ari's formula and `□ p ⇒ □ ○ p` (`Checks`, section `LTL.Decide`) |
| C5 | the C5 formula, decided by computation (`Checks`, section `LTL.Decide`) |
| C6 | `decide` against `decidePC` certificates (`Proofs`) |
| C8 | `decide` against `decideSCC` (`Compare`) |

## Phases

The phases are the order in which the goals were done. A comment that says
"Phase 8" or "Phase 9" refers to the work on the goals listed below.

| Phase | Goals |
|---|---|
| 1–7 | G1–G28, roughly in the order of `m4.tex` (Phase 3 is the temporal rules, Phase 4 the lemmas of section 2) |
| 8 | G29, G30: Bar-based searches and the explored state set |
| 9 | G31, G32: (PC) and short certificates |
| 10 | G34, G35 (`PHASE10-PLAN.md`) |
| 11 | G37–G40: the SCC procedure (`PHASE11-PLAN.md`) |
