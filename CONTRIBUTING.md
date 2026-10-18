# Contributing / Building notes

This repository formalizes the paper *A shape theorem for exploding sandpiles*: 22 of its
29 registered statements are proved, and the remaining 7 are cited results carried as
explicit hypotheses; six of those seven are also proved in this repository (see
[`ASSUMPTIONS.md`](ASSUMPTIONS.md)).  It is primarily a finished artifact rather than an
actively solicited collaborative project, but issues and pull requests are welcome.

The shared lattice library comes from the separate
[`Lattice-Probability`](https://github.com/nitromannitol/Lattice-Probability) library, which
`lakefile.lean` requires as a `git` dependency pinned to an exact commit; Lake materializes it
under `.lake/packages/`.  It is read-only for this project: lattice objects that do not
depend on this paper belong in that library, extensions specific to the paper belong under
`Exploding/`, and contributors must not edit the dependency's sources.

## Building locally

```bash
lake exe cache get        # first time: prebuilt mathlib oleans
lake build                # the dependencies and the project
lake build ExplodingAudit # the Mathlib-only comparator surface
```

The production build is required to emit no Lean or linter warnings.  The sole exception is
`ExplodingAudit/LimitShape/Challenge.lean`, which contains one documented statement-level
`sorry`, checked against its completed solution by `leanprover/comparator`.

A few practical notes for working with this development:

- **Never run `lake clean`.**  It wipes the `mathlib` and `Lattice-Probability` oleans and
  forces a multi-hour rebuild from source.  To force a project-only rebuild, remove the
  project build artifacts under `.lake/build/lib/lean/Exploding` (and the corresponding
  `.lake/build/ir/Exploding`) and re-run `lake build`.

- **Per-file rebuilds.**  Lake invalidates by content hash, not mtime, so `touch` does
  nothing; delete the specific `.olean` under `.lake/build/lib/lean/` and rebuild the module.

- **Frozen statements.**  The text between `-- FROZEN-STATEMENT-BEGIN` and
  `-- FROZEN-STATEMENT-END` in `Exploding/Frozen/` is pinned by the SHA-256 recorded in
  `ledger/manifest.yaml`.  A change there shows up in `python3 tools/check_manifest.py` and
  must be recorded in the manifest (`python3 tools/freeze.py` computes the hash); proofs after
  the end marker may be changed freely.

- **Cited results.**  A result the paper quotes from the literature is stated as a
  proposition in `Exploding/External/`, registered as `FROZEN`, and taken as an explicit
  hypothesis by the theorems whose proofs use it; it is never an `axiom`.  Regenerate
  `ASSUMPTIONS.md` with `python3 tools/assumptions.py` after adding one.

- **Generated documentation.**  The status block and the paper map of `README.md` and the
  frozen-surface table of `CORRESPONDENCE.md` are generated from the manifest:
  `python3 tools/sync_docs.py` checks them and `python3 tools/sync_docs.py --write`
  regenerates them.

- **The main results** are in `Exploding/MainTheorems.lean`; the axiom report is
  included in the default build and is also built explicitly by
  `lake build Exploding.Meta.AxiomsAudit` in the CI workflow. A theorem restated there
  is added to `Exploding/Meta/AxiomsAudit.lean`. `python3 tools/verify.py` runs every checker.

- **The comparator surface** under `ExplodingAudit/` is deliberately not a default target.
  Run `bash ExplodingAudit/check_standalone.sh --vocabulary` after editing a challenge or its
  `SolutionBasic.lean`; the two vocabulary blocks must stay byte-identical.

## Elaboration policy for new files

- Close arithmetic goals with named monotonicity lemmas and `calc`, not with `nlinarith`
  on goals involving `Real.rpow` or `Real.exp`.  When a nonlinear fact is needed, hoist it
  into a small `private` lemma over abstract real variables so that `rpow` and `exp` terms
  never enter a numeric tactic.
- Prefer the explicit `mul_le_mul_of_nonneg_*` / `add_le_add_*` lemmas to `gcongr` on goals
  over `ℝ`.
- Use `positivity` for sign goals only.
- Before `ring` or `field_simp` on an expression built with `set`, run `clear_value` on the
  bound names; otherwise the let-bodies are unfolded inside the tactic.
- Profile before restructuring: do not split a file, narrow its imports, or add an instance
  cache "for performance" without a warm profile before and after
  (`lake env lean --profile <file>`).
- Never raise `maxHeartbeats`.  A default-budget failure is a design signal, usually a wrong
  lemma orientation or a `set`-bound term, not a budget problem.
- Keep Lean files under 1500 lines.
- Never run `lake clean`.
