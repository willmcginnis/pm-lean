# Export log

A dated public log of exports to formalization platforms and of fixes to the export tooling, newest
last. Names and release numbers follow [NAMING.md](NAMING.md) and [VERSIONING.md](VERSIONING.md).

| Date | What |
|---|---|
| 2026-10-12 | A private pilot exported ✱1–✱5 to Prove2Me: 4 definition bundles and 196 theorems (✱1·2–✱1·6, the 188 theorems of ✱2–✱5, and three results about the system: soundness, completeness, and that the one-letter variant of ✱1·4 in the Gutenberg transcription is not a theorem). All 196 were proved on the platform, in its Lean v4.33.1 environment. The pilot used the repository's own Lean names (`PM.t2_01`, …), not the export names of NAMING.md, and it is not a release. |
| 2026-10-12 | The platform refuses `macro` in submissions, so the pilot's exporter (not yet in this repository) expands the repository's two tactic macros in the proofs it submits. |
| 2026-10-12 | One exported declaration, `upd_self` in PM/Complete.lean, relied on an auto-bound implicit (`b`); fixed in the repository on 2026-10-13 by declaring the binder `{b : Bool}`. |
