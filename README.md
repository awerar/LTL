# Constructive LTL decision procedures in Agda

This development constructs a decision procedure, `decide`, returning either
a derivation of a temporal formula or a certified lasso countermodel. It
searches the state graph for fair strongly connected components (m5). Its
derivations use a checked propositional-consequence rule, which keeps the
certificates short.

The current language has propositional variables, negation `¬`, implication
`⇒`, **next** `○`, and **always** `□`. Eventually `◇` and the other Boolean
connectives (`∧`, `∨`, `⇔`, `⊤`, `⊥`) are abbreviations. **Until is not yet
implemented.**

## Start here

- [Master's thesis proposal](docs/ltl-master-thesis.pdf)
  ([LaTeX source](docs/ltl-master-thesis.tex)): learn LTL, understand the existing
  proof, extend it with Until, and study execution and readable certificates.
- [Proof extraction from a failed LTL tableau](docs/m4.pdf)
  ([LaTeX](docs/m4.tex)): the state-elimination argument.
- [The SCC decision procedure](docs/m5.pdf)
  ([LaTeX](docs/m5.tex)): the graph certificate argument and comparison.
- [LTL/Statement.agda](LTL/Statement.agda): the specification, a small
  hand-checked module stating the LTL semantics and what a decision procedure
  must prove. [LTL/Correct.agda](LTL/Correct.agda) proves it for the
  procedure.
- [LTL/8-Procedures/Decide.agda](LTL/8-Procedures/Decide.agda): the public
  decision procedure, [LTL/8-Procedures/Answer.agda](LTL/8-Procedures/Answer.agda):
  what it returns, and [LTL/8-Procedures/Inspect.agda](LTL/8-Procedures/Inspect.agda):
  how to look inside an answer.

## Check the development

Tested with **Agda 2.8.0**. No Agda standard library is needed. From the repository
root (`LTL.agda-lib` supplies the include path; interfaces go to `_build/`):

```sh
agda LTL/Correct.agda
agda LTL/Pretty.agda
agda LTL/9-Tests/Checks.agda
agda LTL/9-Tests/GraphExamples.agda
agda LTL/9-Tests/Figure11.agda
agda LTL/9-Benchmarks/Examples.agda
agda LTL/9-Benchmarks/Lecture.agda
```

`Checks` and `GraphExamples` hold the computational checks of the core
modules. `Examples` decides 46 formulas from Schmitt and Goubault-Larrecq.
`Lecture` examines a worked example. These benchmark modules take longer than
the core proofs.
Timings quoted in the source comments depend on the machine and evaluation
method.

The files use `--safe --without-K --exact-split`. There are no postulates,
unfinished goals, or termination overrides. The procedures return a derivation
or a finite lasso countermodel. `LTL/Correct.agda` connects this to the
semantics of `LTL/Statement.agda`: `decide` is a `DecisionProcedure`.
When it answers true, the formula is valid, meaning true at time 0 of every
lasso (ultimately periodic) interpretation. When it answers false, it returns a
lasso on which the formula is false. Validity on arbitrary infinite words is
not stated. The proposal discusses that distinction.

## Viewing proofs

[LTL/Pretty.agda](LTL/Pretty.agda) prints the result of `decide` in a
readable form. For a valid formula you get a numbered Hilbert proof, where
each line is an axiom or follows from earlier lines by MP or Gen. For an
invalid one you get the lasso countermodel: the variables true at each time
point, and where the loop starts. `∧`, `⇔` and `◇` are printed as
abbreviations; `∨`, `⊤` and `⊥` are not, so `¬ A ⇒ B` and `p ⇒ p` read as
written.

From a terminal (needs Python 3):

```sh
tools/show-proof 'G p -> p'                 # numbered proof
tools/show-proof '□ pv ⇒ pv'                # the same, in Agda syntax
tools/show-proof --tree 6 'G p -> p'        # proof tree, to depth 6
tools/show-proof 'F p & F q -> F (p & q)'   # countermodel
tools/show-proof --raw 'F p'                # formula without abbreviations
tools/show-proof --expr 'renderDeriv (dne {pv})'   # any String expression
```

The formula can be written in ASCII or in Agda syntax, or a mix of both. The
ASCII forms are:

| ASCII | Means |
|---|---|
| `~`, `!`, `not` | `¬` |
| `X`, `next` | `○` |
| `G`, `[]`, `always` | `□` |
| `F`, `<>`, `eventually` | `◇` |
| `&`, `/\`, `and` | `∧` |
| `\|`, `\/`, `or` | `∨` |
| `->`, `=>` | `⇒` |
| `<->`, `<=>` | `⇔` |
| `true`, `false` | `⊤`, `⊥` |

The variables `p q r s t` and `x0`, `x1`, … are `var 0` to `var 4` and `var N`,
which are also the names used in the output. Precedence is Agda's: prefix
operators bind tightest, then `∧`, `∨`, `⇒` (right associative), `⇔`. The
formula is evaluated with `LTL.Pretty` and `LTL.9-Tests.Figure11` open, so `pv`, `qv`,
`axT`, … can also be used. `tools/show-proof --help` lists all of this. Set
`AGDA` to choose the Agda binary. Quote the formula: unquoted, the shell reads
the `>` in `->` as a redirection. The first run after an edit rechecks the
modules `LTL.Pretty` depends on, which can take a minute.

In an editor, load `LTL/Pretty.agda`, then:

- Emacs: `C-u C-u C-c C-n prove (□ pv ⇒ pv)` prints the text with real line
  breaks. Plain `C-c C-n` shows a quoted string with `\n` escapes.
- Editors that talk to Agda over `--interaction-json` (for example the VS Code
  extensions) always show a quoted string. `C-c C-n proveLines (□ pv ⇒ pv)`
  gives one quoted string per line.

Other functions: `proveTree n Q`, `renderDeriv d` and `renderTree n d` for any
derivation `d`, `showFormula` and `showFormulaRaw`.

Limitations: rendering is computed by Agda's normaliser, so it is only
practical for small certificates.

## Reviewing the proof

`tools/proof-map` shows the development as a tree of definitions under
`decideCorrect`, read from Agda's own cross-references (`agda --html`). It
also records which definitions have been reviewed:

```sh
tools/proof-map tree --depth 2           # the top of the tree
tools/proof-map tree sccGraph --open     # a subtree, reviewed parts folded
tools/proof-map next                     # open definitions with a reviewed user
tools/proof-map next provableSCC         # ... only inside that branch
tools/proof-map next --up                # open definitions whose uses are reviewed
tools/proof-map tree closure --up        # who uses closure, upwards
tools/proof-map show provableSCC --src   # uses, users and source
tools/proof-map done decide -m "note"    # mark as reviewed
tools/proof-map done LTL/1-Lib/Bar.agda    # mark a whole file (or LTL.1-Lib.Bar)
tools/proof-map status                   # progress per module
tools/proof-map stale --diff             # reviews that are out of date, and what changed
```

Marks can be made in any order, so a review can work top down from
`decideCorrect` (`next`), bottom up from the foundations (`next --up`; a group
of mutually recursive definitions becomes ready together), or from both ends.
`status` then also counts the open definitions left between a reviewed
definition above and one below, where the two meet.

The next lists are grouped by branch (the children of the root), the branch
with the most open definitions first. Inside a branch they follow the tree,
heaviest subtree first, so a review finishes one part before moving on
rather than jumping around. To review one part of the proof on its own, give
its top definition as the root: `next provableSCC` lists only what lies
under `provableSCC`. `--order weight` gives a single list ranked by what each
definition carries, `--order tree` a single list in tree order.

Review marks are kept in `docs/review.tsv` (written by the first `done`), with a
hash of each definition's source (comments and spacing are ignored). When the
code of a reviewed definition changes, its mark shows as stale (`~`) until it
is marked again. `stale` lists these, and also marks whose definition no
longer exists (renamed or removed), with the definition it was most likely
renamed to; `undo` with the old full name removes such a mark.

`Statement` (the hand-checked specification) and Agda's builtins are not
tracked. `Base` and `Prelude` are tracked but folded: they are used almost
everywhere, so the tree and the next lists do not go into them from the rest
of the proof. Review them by file (`done LTL/1-Lib/Prelude.agda`, or the
CodeLenses and badges in VS Code), or focus on one of their definitions to
see its tree within the library. `status` counts them with the proof that
uses them.

### In VS Code

[tools/vscode-proof-map](tools/vscode-proof-map) is a small extension that
shows the same map in VS Code. It is a front end to `tools/proof-map` and
needs no npm packages or build step. It adds:

- a **Proof Map** view in the activity bar: the tree under the root, with a
  checkbox per definition (ticking it runs `done` or `undo`), the number of
  open definitions below each node, and a filter that hides fully reviewed
  subtrees. Right-click a node to focus on its branch (*Focus on This
  Branch*, also in the editor's context menu for the definition at the
  cursor) or to add a note. While focused, the tree, both next lists and the
  status bar count cover only that branch, and the view shows where it sits
  (`decideCorrect › decide › provableSCC`). The go-to-file button in each
  view's title, or a click on the status bar count, opens the focused
  definition. To unfocus, use the × button in any view's title or beside the
  status bar count, *Unfocus* in the editor's context menu, or *Proof Map:
  Unfocus* in the command palette.
  *Show Users* switches the tree to the definitions that use a node, upwards
  (as `tree --up`); the home button returns to the main tree.
- **Next, top down** and **Next, bottom up** lists (`next` and `next --up`),
  grouped by branch the same way, each entry showing its weight.
- above each definition in an Agda file, its review status (click to toggle),
  how many definitions it uses (click to reveal it in the tree) and how many
  use it (click for its users). The editor's context menu has *Reveal in
  Proof Map* and *Show Users*.
- at the top of each Agda file, how many of its definitions are reviewed;
  click to mark them all. *Mark File Reviewed* is also in the explorer's,
  the editor tab's and the tree's context menus, with an Undo button
  afterwards; *Remove File's Review Marks* asks first.
- in the explorer and on editor tabs, a badge per Agda file and folder: the
  number of open definitions (`9+` beyond 99), a green `✓` when all are
  reviewed, a yellow `~` when some changed since their review; the tooltip
  gives the counts. Partly reviewed files keep git's colours. The setting
  `proofMap.explorerBadges` turns this off.
- the overall count in the status bar; its tooltip gives the number of open
  definitions between reviewed ones.
- out-of-date reviews, shown clearly: a **Changed since review** view
  (only when there are some, with a count badge) lists definitions whose
  code changed since their review, and marks of definitions that no longer
  exist. Click an entry to open it; a mark whose definition was renamed is
  matched, by its reviewed code, to the likely new name, which a click opens
  (right-click to remove the old mark). In the editor only what changed
  since the review is marked: changed text on a yellow background, a dashed
  line where lines were removed, the reviewed text on hover, and a mark in
  the scroll bar. This compares with a copy of each reviewed definition that
  `proof-map` keeps in `_build/proof-map-reviewed/` (or, failing that, with
  git); without either, only the name is marked. In the tree their names are
  highlighted and described as changed; the status bar turns yellow with
  the count and opens the view. Ticking a checkbox, or the CodeLens above
  the definition, marks it reviewed again.

The map is rebuilt when an `.agda` file is saved and when `docs/review.tsv`
changes. If Agda fails, the last checked state is shown, with a warning.
To install it, run *Developer: Install Extension from Location…* from the
command palette and choose `tools/vscode-proof-map`. `test/suite.js` drives
the extension in a separate VS Code instance; the command is at its top.

## Repository layout

The notes (`m4`, `m5`), the thesis proposal and the methodology are in
[docs/](docs). The Agda modules are grouped by the part of the argument they
formalise. A module's name follows its path, so `LTL/2-Syntax/Formula.agda` is
`LTL.2-Syntax.Formula`.

| Folder | Modules | What it is |
|---|---|---|
| `LTL/` | `Statement`, `Correct`, `Pretty` | the specification; the proof that the Boolean evaluation is its semantics (so derivable formulas are valid) and that the procedure is a `DecisionProcedure`; readable output |
| `LTL/1-Lib/` | `Base`, `Prelude`, `Sets`, `Bar`, `Nodes`, `Graph`, `FairGraph`, `CertStep` | foundations without the standard library; inductively finite sets; graph search and the generic fair-graph certificate theorem of m5 |
| `LTL/2-Syntax/` | `Formula`, `Skel`, `Deriv`, `Val` | syntax and deductive rules (`⊢ A`: A is derivable), m4 §1 |
| `LTL/3-Rules/` | `Prop`, `PropList`, `Temporal` | derived rules, m4 Lemmas 1.1–1.2 |
| `LTL/4-Semantics/` | `Orbit`, `OrbitEval` | positions on a lasso and Boolean evaluation of formulas there |
| `LTL/5-States/` | `Reach`, `Common`, `State`, `Step`, `Taut`, `CompletePC`, `StepLemma`, `VecBar`, `Closure`, `Extract` | states, transitions, the finite state space, and the building blocks of extraction, m4 §2 and §4 |
| `LTL/6-Countermodel/` | `Walk`, `Lasso`, `Hintikka` | finite lasso countermodels and their correctness, m4 §5 |
| `LTL/7-SCC/` | `SccLasso`, `SccExtract`, `SccSeed` | graph certificates applied to temporal logic, m5 |
| `LTL/8-Procedures/` | `Answer`, `Inspect`, `Decide`, `Everything` | the decision procedure and its answer type, m4 Thm 6.1; functions that look inside an answer |
| `LTL/9-Tests/` | `Checks`, `GraphExamples` | computational checks of the core modules |
| `LTL/9-Benchmarks/` | `Examples`, `Lecture` | slow benchmarks |

The modules that work over one fixed formula P (most of `5-States/`,
and all of `6-Countermodel/` and `7-SCC/`) take it as a module parameter,
so P is not passed around inside them. `Decide` is parameterised the same way
by the input Q, and opens them at `¬ Q`. `LTL/8-Procedures/Everything.agda`
opens all of these modules without arguments for everyone else, so there
every name takes its formula first: `St P`, `Lasso (¬ Q) v0`, `decide Q`.

The textbook and external papers used during the original development are not
included in this repository; bibliographic links are provided in the proposal.
