# Theorem 1.4 version 4: corrected-source marker and staged registration

18 October 2026. The manifest advances `thm-explosive` from version 3, the journal statement at
`exploding.tex:265-268`, to version 4 on the corrected arXiv-format v10 source,
`paper/corrected-arxiv/exploding-corrected-arxiv.tex:123-129`, label `theorem:explosive`. The
bytes between the FROZEN-STATEMENT markers do not change. The closure hash, the provider, the
state and the proof body are unchanged. This receipt records the exact identities, the
source-partition change and the included nonvacuity check. Full build and axiom gates are
required before this version receives corrected-source credit; the paper as a whole is open.

## Status of this registration

This version changes manifest metadata and gap records, generated and manual reporting,
source-reporting fixtures and source docstrings. It adds an imported Support theorem tying
the all-high product law to `Exploding.Frozen.explosive` and an expanding ordinary-odometer
front, together with its axiom-audit line. It does not change any byte between the markers,
any paper theorem proof, any other manifest node, or any paper source.

Required before corrected-source credit:

- a fresh full build and the axiom closures of `Exploding.Frozen.explosive`,
  `Exploding.explosive`, `Exploding.xsr_schonmann`, and
  `Exploding.explosive_all_high_nonvacuity`;
- all configured repository checks on the final tree and independent statement review.

The generated state wording "proved, independently audited" is the tool's convention for every
`PROVED` row. This receipt distinguishes that registry state from the required integrated checks.

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
The version 3 identity, the journal pin `paper/exploding.tex` (SHA-256
`1d7c2010d8bd29e7fb83e93f19c9ebe0e8aef201f93559b2b18f5ca0dc049b44`)
and the journal lines 265–268, is retained only as history. Its text states the product law
without a single common marginal; the corrected source states one probability law `ν` at every
site. The 2026-10-03 journal-source audit in
`ledger/audits/2026-10-03-refute-first-A.md` of the version 3 identity does not apply to version 4.
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
| `β` explosive with probability 1 | `∀ᵐ β ∂(Measure.infinitePi fun _ : Site d => ν), Explosive β` | conclusion |
| Schonmann's bound, Proposition 7.4, cited | `(hSch : Exploding.External.SchonmannBootstrap)` | cited input |

The five-bin audit classifies the outer binders as TYPING `d` and `ν` (2), SOURCE `hd`,
`hν`, `hlow` and `hhit` (4), RULED cited input `hSch` (1), STANDING (0), and EXCESS (0).
The corrected theorem does not state `hSch`; this explicit cited-input binder was already
present in version 3 and remains subject to the cited-input boundary.

`Explosive` is `¬Robust`, and `Robust` quantifies over `Stabilizable (η + nδ₀)` for `n ≥ 1`,
with stabilizability defined by eventual constancy of the parallel toppling odometer. An
independent refute-first source and statement audit of this binding, dated 18 October 2026,
returned PASS for source and statement design (audit SHA-256
`19a5489562f77b8bbf96bf7a27d63b24189e3929667e32e230d886bc8844988f`). It did not run Lean
and does not certify the proof.

## Caveats carried, not resolved here

- `SchonmannBootstrap` (`Exploding/External/Schonmann.lean:23-27`) is stated for `0 < p < 1`.
  Proposition 7.4 states `p > 0`. The Lean hypothesis is weaker than the cited proposition, so
  it assumes no more than the cited result. The audit reports that the endpoint `p = 1` is
  handled without `hSch` (`bc_layers_prob_one`); that was not re-verified here.
- The exact dynamics and exponential rate of Proposition 7.4 have not been checked against
  Schonmann's 1992 text. The operative justification in this repository is the in-repository
  proof `Exploding.xsr_schonmann`. The manifest checker's sorry and axiom scan passes on the
  source/manifest postimage recorded below.
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

## Source checks on the source/manifest postimage

The table records the source checks on commit `edb1b596101abc5c64760e9d4817c3ecb0592e45`
(tree `f460d1eb4d4384e506c745b16bbeaf467799b981`), whose paper and manifest bytes are
unchanged in this version. `tools/verify.py` checks the final tree.

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

The source checks above do not replace the fresh full build, axiom probes, or warning checks.

## Proof and gate obligations

1. The imported `Exploding.Support.ExplosiveVacuity` theorem proves the exact `hlow` and
   `hhit` for the Dirac law at `2d-1`, discharges `hSch` by
   `Exploding.xsr_schonmann`, and checks an expanding ordinary-odometer front. The strict
   two-height law separately consumes `hSch` through
   `Exploding.LSProof.ls_flp_from_explosive` for every `0 < p < 1`, including `p = 1/2`.
   The expanding-front clause checks the dynamics at the endpoint; the theorem's explosion
   clause follows by applying `Exploding.Frozen.explosive` to that same product law.
2. Before credit, run the full build, `#print axioms` for the Frozen/public theorem,
   `Exploding.xsr_schonmann` and the nonvacuity theorem, and the configured axiom and warning
   checks. The axiom-audit module prints the nonvacuity theorem's closure explicitly.
3. Confirm the `formalization.yaml` sorry and axiom fields against that fresh build and record
   the verification result separately.
4. Complete independent final-byte review of the integrated tree.
