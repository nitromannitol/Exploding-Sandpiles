# Contributing / Building notes

This repository is a formalization in progress: 5 of its 29 registered statements are
proved, and none of the paper's main results is yet.  Issues and pull requests are welcome.

## Building locally

```bash
lake exe cache get   # first time: prebuilt Mathlib
lake build           # compile the project
```

The production build is required to emit no Lean or linter warnings other than one
`declaration uses 'sorry'` warning for each open registered statement
(`python3 tools/check_warnings.py`).  A `sorry` anywhere else, or a second one in an open
node's file, fails `python3 tools/check_manifest.py`.

A few practical notes for working with this development:

- **Never run `lake clean`.**  It wipes the Mathlib oleans and forces a
  multi-hour rebuild from source.  To force a project-only rebuild, remove the
  project build artifacts under `.lake/build/lib/lean/Exploding` (and the
  corresponding `.lake/build/ir/Exploding`) and re-run `lake build`.

- **Per-file rebuilds.**  Lake invalidates by content hash, not mtime, so
  `touch` does nothing; delete the specific `.olean` under
  `.lake/build/lib/lean/` and rebuild the module.

- **Frozen statements.**  The text between `-- FROZEN-STATEMENT-BEGIN` and
  `-- FROZEN-STATEMENT-END` in `Exploding/Frozen/` is pinned by the SHA-256
  recorded in `ledger/manifest.yaml`.  A change there shows up in
  `python3 tools/check_manifest.py` and must be recorded in the manifest;
  proofs after the end marker may be changed freely.

- **Closing an open node.**  Replace the node's `sorry` by a proof, confirm with
  `python3 tools/check_axioms.py` that its axiom closure no longer contains `sorryAx`,
  set its `state` to `SEALED` in the manifest, and regenerate the documentation with
  `python3 tools/sync_docs.py --write`.  When a main theorem is sealed, restate it in
  `Exploding/MainTheorems.lean`, add it to `Exploding/Meta/AxiomsAudit.lean`, and add its
  comparator challenge under `Audit/`.

- **Cited results.**  A result the paper quotes from the literature is stated as a
  proposition in `Exploding/External/`, registered as `FROZEN`, and taken as an explicit
  hypothesis by the theorems whose proofs use it; it is never an `axiom`.  Regenerate
  `ASSUMPTIONS.md` with `python3 tools/assumptions.py` after adding one.

- **Library lemmas.**  Lattice objects that do not depend on this paper belong in the
  shared library Lattice-Probability.

- **The proved results** are in `Exploding/MainTheorems.lean`; the axiom audit is
  `lake build Exploding.Meta.AxiomsAudit`.  `python3 tools/verify.py` runs every checker.
