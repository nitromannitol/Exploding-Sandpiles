# Theorem 1.4 version 4: corrected-source marker and staged registration

18 October 2026. The manifest advances `thm-explosive` from version 3, the journal statement at
`exploding.tex:265-268`, to version 4 on the corrected arXiv-format v10 source,
`paper/corrected-arxiv/exploding-corrected-arxiv.tex:123-129`, label `theorem:explosive`. The
bytes between the FROZEN-STATEMENT markers do not change. The closure hash, the provider, the
state and the proof body are unchanged. This receipt records the exact identities, the
source-partition change and the checks run on this commit. It does not certify the Lean proof
on this commit, the paper, or any statement beyond the cited-input boundary described below.

## Status of this registration

This commit changes manifest metadata and gap records, generated and manual reporting, the
source-reporting fixtures, and one Lean docstring above the frozen block. It does not change
any byte between the markers, any proof, any other node, or any paper source.

Not established by this commit:

- the locked full build and the axiom closures of `Exploding.Frozen.explosive` and
  `Exploding.explosive` on this tree; `check_axioms.py` and `check_warnings.py` need the Lean
  toolchain and cannot run in this source-only tree;
- the nonvacuity module described under "Required at integration";
- an independent final-byte review of the integrated tree.

The generated state wording "proved, independently audited" is the tool's convention for every
`PROVED` row. For this version it is ahead of the final-byte review listed above.

## Exact identities

| Identity | Bytes | SHA-256 |
|---|---:|---|
| Corrected-v10 source, whole file | | `59b5ac1a5cdf80c5b550dfc1738414892e0aa3f8cdb0bf03d00c74685a3e1be2` |
| Corrected-v10 `defs.tex` input | | `9aba2c73246d79e3c6b87cb1f01cf3e2f636e27c8afd97ccb8ba5c032a9ee65b` |
| Corrected theorem paragraph, lines 123–129 | 283 | `7f8a37ca9eb5f7b7cdca20432b3478bfae47974d90d310538a9da15baf0f4994` |
| Version 4 marker, the bytes between the FROZEN-STATEMENT markers | 323 | `8132c02216ac6b502b1b4e6bb898ead2d8aaeea4a7b9da2795b1f83af4b403ed` |
| Source-level closure | | `9aab685c9ae56d183558908b6885a177a84707a133f5bb13aa1b6296e92a701e`, unchanged |
| Historical journal paragraph, `exploding.tex:265-268` | 241 | `67156828b4f2c7557a3f9ab5eca17f5dc362921fbd19845031f79329f88a44c8` |
| Official arXiv paragraph, `exploding-arxiv.tex:120-123` | 241 | `67156828b4f2c7557a3f9ab5eca17f5dc362921fbd19845031f79329f88a44c8` |

The version 3 and version 4 markers are the same 323 bytes, so `frozen_sha256` is unchanged.
The version 3 identity, the journal pin `paper/exploding.tex` (SHA-256 `1d7c2010d8bd29e7…`)
and the journal lines 265–268, is retained only as history. Its text states the product law
without a single common marginal; the corrected source states one probability law `ν` at every
site. The 2026-10-03 journal-source audit of the version 3 identity does not apply to version 4.
`tools/sync_docs.py` and `tools/check_clauses.py` keep the version 3 readings as recorded
history. The source-reporting tests check that a version 4 node pinned back to the journal
source fails the historical identity check.

## Statement correspondence

Corrected-v10 lines 123–129 state: for `d ≥ 2`, a probability measure `ν` on `ℤ` with
`ν({m ∈ ℤ : m ≥ d}) = 1` and `ν({2d − 1}) > 0`; if `β : ℤ^d → ℤ` has law `⊗_{x ∈ ℤ^d} ν`,
then `β` is explosive with probability 1.

| Source text | Lean | Class |
|---|---|---|
| `d ≥ 2` | `(d : ℕ) (hd : 2 ≤ d)` | typing and source |
| `ν` a probability measure on `ℤ` | `(ν : Measure ℤ) (hν : IsProbabilityMeasure ν)` | typing and source |
| `ν({m ∈ ℤ : m ≥ d}) = 1` | `(hlow : ν {m : ℤ \| (d : ℤ) ≤ m} = 1)` | source |
| `ν({2d − 1}) > 0` | `(hhit : 0 < ν {(2 * (d : ℤ) - 1)})` | source |
| `β` has law `⊗_{x ∈ ℤ^d} ν` | `Measure.infinitePi fun _ : Site d => ν` | source |
| `β` explosive with probability 1 | `∀ᵐ β ∂(…), Explosive β` | conclusion |
| Schonmann's bound, Proposition 7.4, cited | `(hSch : Exploding.External.SchonmannBootstrap)` | cited input |

The outer binders fall into four classes: typing `d` and `ν` (2); source `hd`, `hν`, `hlow`
and `hhit` (4); the cited input `hSch` (1); standing and excess (0). The cited input is not
stated in the corrected theorem. It is the explicit cited-input binder that version 3 already
carried, and the repository uses this form for every cited Schonmann input. It is not a new
premise.

`Explosive` is `¬Robust`, and `Robust` quantifies over `Stabilizable (η + nδ₀)` for `n ≥ 1`,
with stabilizability defined by eventual constancy of the parallel toppling odometer. An
independent refute-first source and statement audit of this binding, dated 18 October 2026,
returned PASS for source and statement design. That audit did not run Lean and does not certify
the proof.

## Caveats carried, not resolved here

- `SchonmannBootstrap` (`Exploding/External/Schonmann.lean:23-27`) is stated for `0 < p < 1`.
  Proposition 7.4 states `p > 0`. The Lean hypothesis is weaker than the cited proposition, so
  it assumes no more than the cited result. The audit reports that the endpoint `p = 1` is
  handled without `hSch` (`bc_layers_prob_one`); that was not re-verified here.
- The exact dynamics and exponential rate of Proposition 7.4 have not been checked against
  Schonmann's 1992 text. The operative justification in this repository is the in-repository
  proof `Exploding.xsr_schonmann`. The manifest checker's sorry and axiom scan of the production
  tree passes on this commit.
- Inherited and non-blocking: the source audit notes that the binders `hL`, `hstat`, `herg`
  and `hrec` of `prop-explosion-criteria` are not consumed by its proof
  (`Exploding/Frozen/ExplosionCriteria.lean`, unused-binder line). This does not change the
  statement of Theorem 1.4, which uses only that criterion through its own hypotheses.

## Source partition and raw counts

| Pin | Before: rows (theorem / definition), coverage | After: rows (theorem / definition), coverage |
|---|---|---|
| journal `paper/exploding.tex` | 25 (18 / 7), 14/24 (12/22 paper-owned) | 24 (17 / 7), 13/24 (11/22 paper-owned) |
| official arXiv `paper/exploding-arxiv.tex` | 5 (5 / 0), 5/24 (5/22) | 5 (5 / 0), 5/24 (5/22) |
| corrected-v10 | 9 (5 / 4), 5/24 (5/22) | 10 (6 / 4), 6/24 (6/22) |

Raw states across the 39 rows are 28 `PROVED`, 11 `FROZEN` (7 cited inputs and 4 literal
definitions), and zero `SEALED`. These are per-source coverage fractions. They are not
whole-paper completion and must not be added together.

Allowed gaps: the journal group adds line 265 `theorem:explosive`; the corrected group removes
line 123; the official group keeps line 120 `theorem:explosive` unclaimed, and its reason names
the version 4 successor. In the manifest, only the `thm-explosive` node changes. Its version
changes from 3 to 4, its source changes to the corrected line range, and it gains an explicit
`source_pin` and this `audit_receipt`. The `approved` field keeps its original value,
`2026-09-24`, for the marker bytes; the version 4 source binding is recorded here.

## Fixtures

`tools/test_source_reporting.py` now expects the 24/5/10 partition, 17 journal and 6 corrected
theorem rows, and `thm-explosive` among the corrected theorems. Its live coverage expectations
are 13/24, 6/24 and 5/24. The historical fixture restores the version 3 identity, the journal
pin and the matching allowed-gap sets, so the historical-world expectations are unchanged. One
test was added: `test_theorem_1_4_v4_excludes_its_v3_historical_reading`.

## Checks on this commit

| Check | Exit | Result |
|---|---:|---|
| `tools/check_manifest.py` (no `--emit`) | 0 | 39 nodes, 0 unsealed, closure checked for 39; pins corrected 10, journal 24, official 5 |
| `tools/check_coverage.py` | 0 | journal 13/24, corrected 6/24, official 5/24; OK within the explicit partial scopes |
| `tools/check_clauses.py` | 0 | 13 historical-source statements, 26 explicitly excluded |
| `tools/check_constants.py` | 0 | 39 statements |
| `tools/check_exponents.py` | 0 | 19 historical-source statements, 20 explicitly excluded |
| `tools/paper_anchors.py` | 0 | 13 anchors resolved |
| `tools/paper_citations.py` | 0 | 9 correct, 0 stale, 0 unresolvable |
| `tools/sync_docs.py` | 0 | README and CORRESPONDENCE agree with the manifest |
| `tools/assumptions.py --check` | 0 | ASSUMPTIONS.md is current |
| `python3 -m unittest tools.test_source_reporting` | 0 | 29 tests |
| `python3 -m unittest tools.test_source_tools` | 0 | 16 tests |

Not run here: Lean and Lake, `tools/check_axioms.py`, `tools/check_warnings.py`, the full
locked build, and `#print axioms`. This source-only worktree has no `.lake` directory.

## Required at integration

1. A nonvacuity module under `Exploding/Support/`, imported from the root module. At `d = 2`
   with `ν = Measure.dirac 3`, it proves the exact `hlow` and `hhit`, discharges `hSch` by
   `Exploding.xsr_schonmann`, and checks an actual expanding front of the ordinary odometer under
   the all-high law. It should also cover the strict two-height law at `p = 1/2`, which consumes
   `hSch`. This module is not part of this commit.
2. The locked full build, `#print axioms` for `Exploding.Frozen.explosive`,
   `Exploding.explosive` and `Exploding.xsr_schonmann`, `tools/check_axioms.py` and
   `tools/check_warnings.py`.
3. The sorry and axiom fields in `formalization.yaml` for `Exploding.Frozen.explosive` are carried
   from an earlier build. They should be confirmed on the integrated tree.
4. An independent final-byte review of the integrated union.

`wip/decomp/ExplosiveAux.lean` still carries the earlier docstring wording. It is outside the
build and was not edited here.
