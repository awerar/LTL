# Tools

Helpers for reading and reviewing the development. Run them from the
repository root. They need Python 3 and Agda on the `PATH`; set `AGDA` to
choose another Agda binary.

| Tool | What it does | More |
|---|---|---|
| [`show-proof`](show-proof) | Decides a formula and prints the result readably: a numbered Hilbert proof, a proof tree, or a lasso countermodel. Formulas may be written in ASCII (`'G p -> p'`) or in Agda syntax. | [Viewing proofs](../README.md#viewing-proofs) |
| [`proof-map`](proof-map) | Shows the proof as a tree of definitions, top down from `statement` in `LTL/Main.agda` or upwards from any definition. Records which definitions are reviewed in `docs/review.tsv` and marks one as stale when its code changes. | [Reviewing the proof](../README.md#reviewing-the-proof) |
| [`vscode-proof-map/`](vscode-proof-map) | A VS Code extension that runs `proof-map`: the tree with checkboxes, lists of what to review next, and review status above each definition. | [In VS Code](../README.md#in-vs-code) |

```sh
tools/show-proof 'F p & F q -> F (p & q)'   # countermodel
tools/proof-map tree --depth 2              # the top of the proof
tools/proof-map next                        # what to review next, top down
tools/proof-map next --up                   # ... and bottom up
```

Each script prints its full usage with `--help`. `proof-map` writes Agda's
HTML to `_build/proof-map/`, which is not tracked. To install the extension,
run *Developer: Install Extension from Location…* in VS Code and choose
`tools/vscode-proof-map`.
