# Contributing and building

This repository is mainly a finished artifact, the formalization of one paper, but issues and
pull requests are welcome.

## Building locally

```bash
lake exe cache get          # prebuilt Mathlib oleans
lake build                  # the dependencies and the library
lake build ExplodingAudit   # the comparator surface, not a default target
```

The toolchain is in `lean-toolchain`, and [elan](https://github.com/leanprover/elan) manages it.
The library builds with no Lean or linter warning. The only `sorry` in the audit surface is the
statement-level one in `ExplodingAudit/LimitShape/Challenge.lean`, which its solution is checked
against by `leanprover/comparator`.

The dependency `Lattice-Probability` is a `git` dependency fixed to one commit in
`lake-manifest.json`; Lake materializes it under `.lake/packages/`. Do not edit it. Lattice objects
that do not depend on this paper belong in that library, and extensions specific to the paper belong
under `Exploding/`.

- **Never run `lake clean`.** It deletes the Mathlib and Lattice-Probability builds and forces a
  rebuild of several hours. To rebuild the project alone, remove `.lake/build/lib/lean/Exploding`
  and `.lake/build/ir/Exploding`, then run `lake build`.
- **Per-file rebuilds.** Lake invalidates by content hash, not by modification time, so `touch`
  does nothing. Delete the `.olean` of the module and build again.

## The main results and the axiom audit

The main results are in `Exploding/MainTheorems.lean`, and each is derived from the statement in
`Exploding/Frozen/` that it names. The axiom reports come from `Exploding/Meta/AxiomsAudit.lean`:

```bash
lake build Exploding.Meta.AxiomsAudit 2>&1 | tee axioms-audit.log
python3 scripts/check_axioms.py axioms-audit.log
```

`scripts/check_axioms.py` requires one report for each theorem in its explicit list, and each report
must consist of exactly `propext`, `Classical.choice` and `Quot.sound`. A theorem added to
`MainTheorems.lean` is also added to `Exploding/Meta/AxiomsAudit.lean` and to that list.

## Conventions

- Nothing in `Exploding/` may contain `sorry`, `admit`, `native_decide`, a new `axiom` or
  `set_option maxHeartbeats`. Never raise `maxHeartbeats`: a failure at the default budget usually
  means a wrong lemma orientation or a term fixed by `set`.
- Keep statements faithful to the corrected edition. Refer to a result by its number and LaTeX
  label, as [`CORRESPONDENCE.md`](CORRESPONDENCE.md) does, and never by a line number, since line
  numbers change with every edit of the paper.
- A result the paper quotes from the literature is a proposition in `Exploding/External/`, and the
  theorems whose proofs use it take it as an explicit hypothesis. It is never an `axiom`. After
  adding one, run `python3 tools/assumptions.py` to regenerate [`ASSUMPTIONS.md`](ASSUMPTIONS.md).
- Keep new Lean files under 1500 lines; split a file that grows past that. Three older files
  (`Support/SubPen.lean`, `Support/ReductionShift.lean`, `Support/CrossingTimeAux.lean`) are longer.
- Close arithmetic goals with named monotonicity lemmas and `calc`, not with `nlinarith` on goals
  involving `Real.rpow` or `Real.exp`. Profile before splitting a file, narrowing imports or adding
  an instance cache: `lake env lean --profile <file>` before and after the change.
- Before `ring` or `field_simp` on an expression built with `set`, run `clear_value` on the bound
  names; otherwise the let-bodies are unfolded inside the tactic.

## Comparators

Each pair under `ExplodingAudit/` has a Mathlib-only `Challenge.lean`, a `Solution.lean` that
proves the same statement from the library, and a `comparator.json` that permits exactly
`propext`, `Classical.choice` and `Quot.sound`. The only pair is `ExplodingAudit/LimitShape/`.
Do not add to a challenge a declaration that its statement does not need, and do not change a
challenge without checking it against the paper's statement. After editing a challenge or
`SolutionBasic.lean`, run `bash ExplodingAudit/check_standalone.sh --vocabulary`; the two vocabulary
blocks must stay byte-identical. The [README](README.md#running-the-comparators) describes how to
run the comparator. A missing tool or a failed kernel check is a failure.

## Checks

`python3 tools/verify.py` runs the checkers below in turn, stops at the first failure, and then
compares the axiom closure of every statement with the manifest. It needs PyYAML, which
`python3 -m pip install -r tools/requirements.txt` installs.

- `check_manifest.py`: the statement hashes recorded in [`ledger/manifest.yaml`](ledger/manifest.yaml).
- `check_coverage.py`: every theorem-like statement of the paper is formalized.
- `check_clauses.py` and `check_exponents.py`: how much each paper statement asserts, and each
  exponent in it, against its Lean statement.
- `check_constants.py`: every constant depends only on the dimension.
- `paper_anchors.py` and `paper_citations.py`: the paper locations recorded in the manifest and the
  citations of the paper in the Lean sources.
- `sync_docs.py`: the status block of `README.md` and the generated tables of
  [`CORRESPONDENCE.md`](CORRESPONDENCE.md) agree with the manifest. `python3 tools/sync_docs.py --write`
  regenerates them.
- `assumptions.py --check`: [`ASSUMPTIONS.md`](ASSUMPTIONS.md) is current.
- `check_warnings.py`: the build of `Exploding` emits no warning.
- `tools/check_axioms.py`: the axiom closure of each statement agrees with the manifest. This is
  not the same script as `scripts/check_axioms.py`, which checks the printed report of the axiom audit.

## Continuous integration

`.github/workflows/build.yml` runs on each push to `main` that changes code, build files or tools
(Markdown, `paper/`, `formalization.yaml` and `CITATION.cff` are ignored), and on manual dispatch. It
builds the library with the zero-warning check, runs the axiom audit with `scripts/check_axioms.py`,
builds `ExplodingAudit`, and runs `tools/verify.py`.

`.github/workflows/comparator.yml` runs on manual dispatch only. It builds `leanprover/comparator`,
`lean4export`, `landrun` and `nanoda` at the revisions in its `env` block, checks that the sandbox
refuses a write outside it, and runs the comparator on each `ExplodingAudit/*/comparator.json`. A
pair without a `Solution.lean` fails the job. The logs are uploaded as the `comparator-logs` artifact.
