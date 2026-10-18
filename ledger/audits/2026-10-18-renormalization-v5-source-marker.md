# Proposition 2.2 version 5: corrected-source declaration and consumer evidence

18 October 2026. The manifest advances `prop-renormalization` from version 4 to
version 5 and changes its effective source pin from the journal copy to corrected
arXiv-format v10. This receipt records the exact source marker, whole Frozen file,
source-level declaration closure and guarded proof-consumer results. It is scoped to
this one registration; it does not certify the rest of either source or the full paper.

## Exact source and statement

The pinned source is
`paper/corrected-arxiv/exploding-corrected-arxiv.tex:352-367`, label
`prop:renormalization_properties`, SHA-256
`59b5ac1a5cdf80c5b550dfc1738414892e0aa3f8cdb0bf03d00c74685a3e1be2`. Its `defs.tex`
input has SHA-256
`9aba2c73246d79e3c6b87cb1f01cf3e2f636e27c8afd97ccb8ba5c032a9ee65b`. The official
arXiv paragraph is text-identical, but the corrected source is selected because it
carries the repaired homogeneous law and delivered-initialization definitions needed
for the `p = 1` endpoint. Neither the official source nor either abstract was edited.

The sole input change from version 4 is `hp1 : p < 1` to `hp1 : p ≤ 1`. The type
retains all three cited-input binders, LSS bounded-degree domination, Mathieu's hole
bound (`hHole`) and Antal–Pisztora chemical distance. It preserves the existing
infinite-good-set, whole-complement finite-hole with strict logarithmic power `5/2`,
and complete induced-chemical-distance clauses, including the unrestricted second
endpoint `y`. For the same `Cinf`, it also states that `Cinf` is an actual component of
the full good-site set and that every infinite full good-site component equals it.
The `hHole` cited binder remains in the theorem type but is unused in this proof; the
hole obligation is proved through in-repository `Exploding.xmf_proved`. No new
`External` declaration is introduced.

| Identity | UTF-8 bytes | SHA-256 |
|---|---:|---|
| Historical version 4 marker | 1,078 | `79b4e8c59d8d852b23963f9f48ecd2a4c39a6d1e66163c3eaa41f57c08ade127` |
| Version 5 marker | 1,298 | `5e3c8b09f9ce732c2cad76168fa1d455e515ea8a08ae74716d43967e8e623b21` |
| Marker delta | — | `aad76db026ad6f8ee492c9e0a07689a2d68a2711bedb9ffc2a024c449983e816` |
| Version 5 whole Frozen file | — | `cbac18d694757154f8a5851ef51c4c40d4fb7c84aa18b1cc439a0177154791d5` |
| Source-level declaration closure | — | `e1fbda039f229cc3970c40943ccbabd91047436071447c13c923fe0c65e916fd` |

The source-level closure was recomputed in the exact proof-plus-metadata union using
`tools/check_manifest.py --emit`. All 39 closure values matched, so no closure hash
changed and no other manifest node was re-versioned. The checker indexed 516 explicit
`Exploding` declarations. The closure digest is a source dependency tripwire; it does
not replace Lean typechecking or axiom checking.

## Guarded proof and consumer checks

Proof commit `97cafd7b6dcc86b205a4030e521da358f9a22dcd` is based on gated private main
`343d66fe7722ca68b1e80d1a4c3fa0020ceeb522`. Its guarded
`Exploding.MainTheorems` build completed 8,957 jobs with exit status 0 and no warnings.
The exact strict-parameter and endpoint consumer probe completed with exit status 0,
checked the full declaration consumers at `p = 1/2` and genuine `p = 1`, included the
nonvacuous two-scale endpoint check, and reported only `propext`, `Classical.choice`
and `Quot.sound` in the axiom closures. The retained raw logs have SHA-256
`bedcffed5612fce9b97aaf555545325f3c5a2a7614f98518bf9c9067f8e7e123` (target) and
`4d2b04a3e72ad1c0b62aa1766b0304e1aaad694f172575d2485f47e98c8fa015` (consumer).

## Source partition and metadata checks

The one-row source migration leaves 39 registrations, 28 theorem rows and 11
definition rows. The exact partition is 26 journal, five official arXiv and eight
corrected-v10 rows. The theorem-like coverage is 15/24 journal (13/22 paper-owned),
5/24 official arXiv (5/22 paper-owned), and 4/24 corrected-v10 (4/22 paper-owned).
Journal line 482 is an allowed gap; corrected-v10 line 352 is claimed; official line
344 remains an allowed gap. The four literal definitions contribute no theorem
coverage, and the other 20 corrected-v10 theorem-like statements remain unclaimed.

The source-reporting fixtures restore the exact historical version 4 source identity
and marker bytes, then check the live version 5 source partition, exact marker and
source/defs pins, the three required gaps, omitted maximality or uniqueness outputs,
and wrong historical identity or bytes. On the exact proof commit plus metadata staging
union, all nine non-Lean configured source checks passed, and the source-reporting test
suite passed all 24 tests. The command results and log hashes are recorded below. The
independent committed-byte proof audit and integrated private-main certificate are
documented separately; this receipt does not confer whole-paper credit.

The maximality and uniqueness omission controls are exact-byte fixture checks: each
removes one output, recomputes the temporary marker hash, and verifies that the mutated
block differs from the canonical approved payload. They are not represented as separate
gate-level semantic rejection tests.

| Source check or fixture | Exit / result | Raw-log SHA-256 |
|---|---:|---|
| `check_manifest.py` | 0 | `50607998231b782fce7d5992bbe5496f91ce531308c05815dd3abf4a0ffddf3c` |
| `check_coverage.py` | 0 | `11255d7ba8ad2bb7bd0d84d5238adabddfc45cc68d98329f43b85300e5aec42f` |
| `check_clauses.py` | 0 | `1fbd8ebbbbffc143825cdc9557d71272dabf3b33b1a5f99f0318ed7f6d66fef2` |
| `check_constants.py` | 0 | `22852bb5f624632dbd9e2399cf138f43ef30ee1a88a93678cefaeb4e5c77a430` |
| `check_exponents.py` | 0 | `157672613d1156cdf7b31a013d91462ddc0540dea4b7fb1eaa9f83f5afc19c49` |
| `paper_anchors.py` | 0 | `8f9dc128c2a158c504c74ad5a9e5d6a453ec87497ee1ce667473bcb404af6875` |
| `paper_citations.py` | 0 | `90cb4242d0fecfa27ed6db889bab1226daf0dad6418505aaee88b41733beb5a4` |
| `sync_docs.py --check` | 0 | `4fc3b6ef99624386372cc058b92e37d2866a20929394e9a1b6035d00d5890a53` |
| `assumptions.py --check` | 0 | `d74af14e6ba78e307eaab537d9c429c0ece00b388309b20137ea3bac4797f8a6` |
| `python3 -m unittest tools.test_source_reporting` | 0; 24 tests | `e625402063a41da00ea81b9ed3856af6f28584d89124e3e8ab1f15d8c7f9f749` |

The exact proof commit also passed a separate committed-byte source/consumer audit;
its report SHA-256 is `791958a461fa43428841811f77a4ea9c80c8bfd5117c446bff0c2a8f879d7626`.
