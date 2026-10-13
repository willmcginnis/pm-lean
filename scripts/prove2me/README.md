# Export to Prove2Me

The generator of the files this repository exports to [Prove2Me](https://prove2.me), a platform of Lean
theorem cards, and the checks run on them before upload. It makes no network call and needs no
credentials: uploading, and reading the result back, are done separately. What was exported, when, and
in which state is recorded in [docs/EXPORT_LOG.md](../../docs/EXPORT_LOG.md); names follow
[docs/NAMING.md](../../docs/NAMING.md), releases [docs/VERSIONING.md](../../docs/VERSIONING.md).

| File | What |
|---|---|
| `config.json` | the export: release, platform environment, source modules, which declarations become cards |
| `export.py` | the platform tree from a commit: definition bundles, statement files, solutions, `manifest.json` |
| `metadata.py` | each card's title, description and proof explanation (`metadata.json`) |
| `verify.py` | the checks below, with the platform's Lean |
| `extract_commands.lean` | every top-level command of a file with its syntax kind, and an inductive type's constructors |
| `render_formulas.lean` | the statement formulas of ✱1–✱5 as LaTeX and text, from the elaborated definitions |

Names come from the repository's data, never from the exporter: a card is named by
[data/export_names.json](../../data/export_names.json), a definition bundle by
[data/naming/definition_bundles.json](../../data/naming/definition_bundles.json), and a card's Lean or
Mathlib counterpart is read from [data/naming/counterparts.json](../../data/naming/counterparts.json).

## Running it

```
python3 scripts/prove2me/export.py all --platform-scripts DIR [--commit REF]
python3 scripts/prove2me/metadata.py
python3 scripts/prove2me/verify.py
```

`DIR` is a checkout of [prove2me/prove2me_workspace](https://github.com/prove2me/prove2me_workspace) at the
commit pinned in `config.json` (`78989800`): its `scripts/extract_decl_graph.lean` and
`scripts/extract_sketch_info.lean` are Stages 1 and 2 of the method and are not copied here. The exporter
reads everything from the commit exported (`git archive`, default `HEAD`) and builds that copy with the
platform's toolchain (Lean v4.33.1, elan installs it on demand), in `.lake/prove2me/` (ignored by git); the
tree is written to `.lake/prove2me/out/`, the report to `.lake/prove2me/verify_report.json`. A clean run
takes about two minutes.

## Method

Prove2Me's own playbook for a whole project (`references/upload_full_project.md`, "skeleton subtraction"):
each generated file is a source file with the commands not selected deleted; the ones kept are copied byte
for byte. Every fact about the code comes from Lean: the declaration graph, declaration spans and every
reference to a constant (Prove2Me's Stages 1 and 2), and every top-level command with its kind
(`extract_commands.lean`). The edits, each at a range Lean reported, are listed in `export.py`'s docstring.
The ones a reader may notice:

- **Names.** A card is `theorem <export name>` (`PM.star2_06_syll`), and in solutions a reference to
  another card's declaration is renamed to that card's export name (`t2_05` becomes `PM.star2_05_syll`):
  the platform knows a card by its export name only.
- **✱1·2–✱1·6** are the constructors of `PM.Thm`, not theorems. Their cards state each constructor's
  binders and type as declared in PM/Basic.lean, and are proved by the constructor.
- **Macros.** The platform refuses `macro` in a submission, and a macro naming theorems cannot go in a
  bundle, which comes before them. Each use of the repository's two tactic macros (`intro_`, `split_iff`)
  is replaced by the macro's own expansion, in parentheses; the solution's header counts them.
- **Every proposition of ✱1–✱5 is a card**, whatever its proof length (PM's numbering is the
  decomposition), plus soundness, completeness, and the check of ✱1·4's transcription. Other theorems a
  proof needs are copied into each solution that uses it (the playbook's inline helpers); definitions go
  into the bundle of their module.

## Checks (`verify.py`)

With the platform's Lean, in a workspace that has its option `autoImplicit false`:

1. every generated module compiles; no `sorry` outside the statement files; no file sets `autoImplicit`;
2. per card: the statement is a `sorry` stub; `solution` has exactly its type; the solution does not
   import its own card; its axioms, not counting imported cards, are within `propext`,
   `Classical.choice` and `Quot.sound`; no file declares a global macro, syntax, notation or elaborator;
3. the type of each card equals the type of its declaration in the repository, built with the same Lean;
4. each card's statement digest and definitions digest, computed from the uploaded files by
   [Checks/Canon.lean](../../Checks/Canon.lean) exactly as `scripts/export_names.py` computes them from the
   repository, equal those of data/export_names.json, to which the lock binds the card's name.

`verify.py --tree DIR` runs the same checks on another tree with a manifest, such as one read back from the
platform after upload, so that a proof found there is checked here before it is trusted.
