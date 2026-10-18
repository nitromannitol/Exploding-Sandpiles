# Theorem 1.2 version 5: corrected-source marker and staged registration

18 October 2026. The manifest advances `thm-limit-shape` from version 4, the journal
statement at `exploding.tex:246-254` with `0 < p < 1`, to version 5 on the corrected
arXiv-format v10 source, `paper/corrected-arxiv/exploding-corrected-arxiv.tex:104-112`,
label `theorem:limit_shape`. The only change to the frozen statement is the endpoint
hypothesis, `hp1 : p < 1` becoming `hp1 : p ≤ 1`. This receipt records the exact marker
and source identities, the source-partition change and the checks run on this commit. It
does not certify the Lean proof, the installed marker or the paper.

## Status of this registration

This commit changes metadata and reporting only. It does not install the version 5 marker
in `Exploding/Frozen/LimitShape.lean` and does not add the proof. Until the exact
proof-plus-metadata union is assembled, the manifest's `frozen_sha256` for
`thm-limit-shape` names bytes that are not yet in the tree, and `check_manifest.py`
reports that mismatch. The node keeps state `PROVED` so that the registry counts stay at
28 PROVED, 11 FROZEN and zero SEALED. That state is not evidence that the theorem is
proved on this commit.

Pending before the registration can be credited:

- the exact proof-plus-metadata union, with the version 5 marker installed and no other
  Frozen byte changed;
- re-emission of `closure_sha256` on that union with `tools/check_manifest.py --emit`,
  which must leave all 39 values unchanged;
- consumer probes at `p = 1/2` and at `p = 1`, including a nonvacuity check of the
  ordinary odometer front at `p = 1`, each with its axiom closure reported;
- an independent committed-byte source, body and consumer audit of the union;
- the locked full build and every configured gate, including `check_axioms.py` and
  `check_warnings.py`, which cannot run in this metadata-only tree;
- raw-log SHA-256 values for the final source checks, recorded with the union;
- the Frozen docstring source address and the direct callers listed below.

## Exact identities

| Identity | UTF-8 bytes | SHA-256 |
|---|---:|---|
| Version 4 marker, historical journal reading | 650 | `7a9bc664298b2adfc0b528e3f1d6ba565efdcb2da1d055eb6e222032e835b44b` |
| Version 5 marker, exact proposed payload | 652 | `3f3707ff2dfa461558934c748b614a3b4472f338425ddf883b0ff4485e72f6d9` |
| Marker delta, `hp1 : p < 1` to `hp1 : p ≤ 1` | 418 | `b9139bd25e73fffa853edfe22465a31e406c2c70dc00fda7439e294c86816c50` |
| Whole Frozen file at the base commit | — | `223f05b79bf2a0301d6b2c6d440905e57527c7abb6c2c2a8386be579ebe06fe7` |
| Whole Frozen file, version 5 | — | pending union |
| Source-level declaration closure | — | `9452aef58fe5be3d2e73376b97502f1c15e8a83ac7db608683db47c60398c6a8`, unchanged |

The version 4 block between the FROZEN markers at the base commit is 650 bytes and is
byte-identical to the historical marker. The delta is a one-token change. The binder
order, the deterministic convex set `B` chosen before the realization `η`, the conjunction
`Convex ℝ B ∧ IsOpen B ∧ B.Nonempty`, the actual support `podo (explodingPile η)`,
`nearestSite`, the Lebesgue symmetric difference and convergence to zero are unchanged.

The closure is a source-level tripwire over the indexed Exploding declarations that the
statement references. The version 5 statement references the same declarations. A scratch
copy with the exact version 5 block spliced into its Frozen file re-emitted all 39 closure
values, and every value matched the manifest. That scratch check does not elaborate Lean.

## Source and outer-input classification

Corrected-v10 lines 104–112 carry the environment. Its theorem paragraph is corrected lines
104–111, which is 300 bytes including the header line and has SHA-256
`3609d8455968de7a959e1d723378fd140f106e64163a35f188fad8603305f585`. The official arXiv
paragraph at lines 101–108 is byte-identical. The corrected source is selected because its
standing displayed law, lines 85–94, fixes `0 < p ≤ 1` and the product law at every
lattice site.

The outer inputs of version 5 fall into five bins. Typing: `d` and `p` (2). Standing:
`2 ≤ d`, `0 < p` and `p ≤ 1` (3). Inherited cited inputs: `hLSSB`, `hHole`, `hChem` and
`hSch` (4), retained exactly. Source-specific premises: 0. Excess binders: 0. No new External
declaration is introduced, and no binder assumes the limit-shape event itself.

## Source partition and raw counts

The registry has 39 rows. Before this commit it was 26 journal, five official arXiv and
eight corrected-v10 rows. It is now 25, 5 and 9.

| Pin | Rows | Theorem rows | Definition rows | Theorem coverage | Allowed gaps |
|---|---:|---:|---:|---|---|
| journal `paper/exploding.tex` | 25 | 18 | 7 | 14/24 (12/22 paper-owned) | line 246 `theorem:limit_shape` is an allowed gap |
| official arXiv `paper/exploding-arxiv.tex` | 5 | 5 | 0 | 5/24 (5/22) | line 101 `theorem:limit_shape` remains unclaimed |
| corrected-v10 | 9 | 5 | 4 | 5/24 (5/22) | line 104 `theorem:limit_shape` is claimed by version 5 |

Raw states remain 28 PROVED, 11 FROZEN and zero SEALED. The manifest diff touches only the
`thm-limit-shape` entry and the two gap blocks. Every other node keeps its version, state,
source pin and closure hash, and every External registration is unchanged.

## Fixtures

The source-reporting fixtures restore the historical version 4 identity and marker bytes
and reject their reuse. A version change, a byte change to the journal block or a rehashed
block fails the historical audit with exit status 2. The version 5 fixtures assert the
exact proposed bytes and the single delta, and they check that three wrong markers do not
match the manifest hash: the retained strict endpoint, a dropped `hSch` binder and a
dropped conclusion conjunct. Coverage controls require the journal line 246 allowance,
reject a stale corrected line 104 allowance and require the official line 101 to remain an
allowed gap. Pin and citation controls fail `sync_docs.py`, `assumptions.py`,
`check_clauses.py` and `check_exponents.py` with exit status 2.

## Checks on this commit, without Lean

| Check | Exit | Result |
|---|---:|---|
| `check_manifest.py` | 1 | Expected pre-union failure: `thm-limit-shape` Frozen bytes hash `7a9bc664…` against manifest `3f3707ff…`. No other node fails, and the closure check passes for all 39 nodes. |
| `check_coverage.py` | 0 | Journal 14/24, official arXiv 5/24, corrected-v10 5/24. OK within the explicit partial scopes. |
| `check_clauses.py` | 0 | 14 historical-source statements, 25 explicitly excluded. |
| `check_constants.py` | 0 | 39 statements. |
| `check_exponents.py` | 0 | 20 historical-source statements, 19 explicitly excluded. |
| `paper_anchors.py` | 0 | 14 anchors resolved. |
| `paper_citations.py` | 0 | 10 correct, 0 stale, 0 unresolvable. |
| `sync_docs.py --check` | 0 | README and CORRESPONDENCE agree with the manifest after regeneration. |
| `assumptions.py --check` | 0 | ASSUMPTIONS.md is current. |
| `python3 -m unittest tools.test_source_reporting` | 1 | 28 tests; 4 fail until the version 5 bytes are installed: three successor-restoration tests and `test_live_limitshape_v5_frozen_bytes_are_installed`. |
| `python3 -m unittest tools.test_source_tools` | 0 | 16 tests. |

A scratch copy of this tree, with the exact version 5 block spliced into its Frozen file,
passes all nine configured source checks, the 28 reporting tests and the 16 tool tests.
It shows that the metadata, the docs and the fixtures agree with the exact marker. It is
not Lean evidence: the copy's proof body is still the version 4 proof, and nothing has been
elaborated or axiom-checked.

## Changes the union must make outside this commit

- `Exploding/Frozen/LimitShape.lean` line 14: the docstring source address should cite
  corrected-v10 lines 104–112. The marker payload is exact.
- `Exploding/MainTheorems.lean` lines 137 and 150: the public wrapper restates `hp1 : p < 1`.
  It should take `p ≤ 1`, because the corrected statement has no strict bound.
- `ExplodingAudit/LimitShape/Solution.lean` line 54: the call passes `hp1`. It needs `hp1.le`
  while the comparator challenge keeps the historical `p < 1` statement.
- `Exploding/Support/LSProofAux.lean`: the endpoint helpers that the version 5 assembly calls
  must accept `p ≤ 1`.
- `ExplodingAudit/README.md`: the comparator restates the historical journal statement, and
  the library theorem is version 5.

The generated surface row renders every `PROVED` node as "proved, independently audited"
through `tools/sync_docs.py`. For `thm-limit-shape` that wording is ahead of its independent
audit, which is pending.
