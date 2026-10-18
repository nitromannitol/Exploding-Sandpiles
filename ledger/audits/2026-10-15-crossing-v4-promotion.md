# Corrected-v10 Proposition 2.1: version 4 validation

15 October 2026. The `prop-crossing-time` registration advances from version
3 to version 4 under the exact corrected-source declaration ruling of this
date. Its manifest state is `PROVED` for the exact corrected-source statement.
This receipt records bounded declaration and consumer evidence. Full-repository
checks and final independent review are documented separately.

## Exact declaration and source

The export remains `Exploding.Frozen.crossing_time` in
`Exploding/Frozen/CrossingTime.lean`; the public `Exploding.crossing_time`
restates its complete type. For d ≥ 2, 0 < p ≤ 1 and every δ > 0, it supplies
a positive cube scale with probability at least `ENNReal.ofReal (1 - δ)`
under the actual `toyLaw d p` of the following event: for every direction and
seed in the closed cube, every cube coordinate is eventually always one,
and a common positive all-one time occurs by `k^d`.

The source is `paper/corrected-arxiv/exploding-corrected-arxiv.tex`,
SHA-256 `59b5ac1a5cdf80c5b550dfc1738414892e0aa3f8cdb0bf03d00c74685a3e1be2`,
with `paper/corrected-arxiv/defs.tex`, SHA-256
`9aba2c73246d79e3c6b87cb1f01cf3e2f636e27c8afd97ccb8ba5c032a9ee65b`.
The homogeneous law is at 85–94, the delivered crossing initialization and
terminal-gated positive minimum at 270–283, and the proposition at 286–292.
The global historical journal-source pin, official arXiv extraction and
abstract are unchanged. This is a corrected-source declaration only.

| Surface | SHA-256 |
|---|---|
| Historical version 3 marker | `86d88877abf5e6e1dc37f9bf5e1a1552bb04588de3fa050596b1faf4fb3d5e38` |
| Version 4 marker, 555 UTF-8 bytes | `0abd7c5aad74dc25d871825907205f3af57bbc7755498247c348ad66592bceae` |
| Version 4 whole Frozen file | `e11583eb725c3ebd8a0e2ec15d2fbc033db18da0b7b1719f3b21bb6b2d1d3faa` |
| Version 4 source-level semantic closure | `254217882eed9f4c125df372a844801ce973e90087909ac00c89838e91fe4f5d` |
| Ordinary provider file | `26c1d9e9bdb9d688ac07690fa265963f4d102cfd4fdb876d15b2de7be9811be1` |

The Frozen proof applies `Exploding.crossing_time_terminal_bound` directly.
That provider combines the strict crossing bound and the all-high endpoint,
then transports the event with the installed a.e. terminal characterization.
The source-level closure digest covers 11 explicit definition declarations;
it is an integrity check, not a replacement for the semantic and Lean audits.

## Statement correspondence

| Binder | Classification | Source basis |
|---|---|---|
| d : ℕ | TYPING | Lattice dimension. |
| hd : 2 ≤ d | SOURCE | Standing dimension range. |
| p : ℝ | TYPING | Bernoulli parameter. |
| hp : 0 < p | SOURCE | Positive-density range. |
| hp1 : p ≤ 1 | RULED | Corrected homogeneous law. |
| δ : ℝ | TYPING | Error parameter. |
| hδ : 0 < δ | SOURCE | Proposition's error restriction. |

There are three SOURCE, three TYPING and one RULED binders, with zero
STANDING or EXCESS inputs. No cited-input, upper-height, terminality,
measurability or desired-probability premise is added. The positive k may
depend on d, p and δ. The direction and seed quantifiers occur inside one
event under the same law and at the same scale.

Both source clauses remain visible. The finite deadline is a positive
all-one hit with `1 ≤ n ≤ k^d`. Terminal one is a coordinatewise eventual-one
tail. Under the true law, the indicator-seeded integer odometer is monotone,
nonnegative and bounded by one, so a hit persists and a coordinate that never
hits one stays zero. The law-supported bound is proved inside the ordinary
provider. No global terminal object is introduced.

The historical version 3 GoodCube-only and hidden-exponent readings remain
bound to their old source and marker. Version 4 displays `k^d` explicitly and
is excluded from those historical clause/exponent comparisons. The new
correspondence is recorded here, without changing the old annotations.

## Source partition and validation status

One existing theorem row changes source group; there is no additional
registration. The registry remains 39 rows and 28 theorem rows. Its
historical group has 33 rows (26 theorems and seven cited-input definitions),
and its corrected group has six rows (two theorems and four literal
definitions). Structural coverage is historical 22/24, including 20/22
paper-owned statements, and corrected-v10 2/24, including 2/22 paper-owned
statements. Literal definitions add no theorem coverage. The historical
crossing and counterexample gaps are at lines 416 and 1351; the corrected
gap list contains the other 22 statements. The seven cited inputs and all
unrelated statement registrations are unchanged.

The source-reporting fixtures reconstruct both exact historical version 3
markers, preserving all-historical clause/exponent comparisons of 24/30
and counterexample-only mixed comparisons of 23/29. The two-migration
scenario expects 22/28 and excludes both corrected rows. The live partition,
missing input, wrong citation, changed identity, changed bytes, and stale or
missing gap-allowance controls are checked separately.

The bounded target build of `Exploding.Frozen.CrossingTime` and
`Exploding.MainTheorems` passed. Both source-reporting regression suites
passed all 34 tests, preserving the historical controls and checking the
crossing migration and negative controls described above. An exact transient
consumer checked both complete export types, each export at d=2,p=1/2,δ=1/2
and d=2,p=1,δ=1/2, and the separate all-seed endpoint mass-one event at k=1.
Both exports and that endpoint event closed to exactly
`propext`, `Classical.choice` and `Quot.sound`, with no warnings or errors.
The exact consumer source has SHA-256
`380d86579d94e7f398e4a1cc17f1a95ae3db3a78a5de3b490d937f76c0694020`.
Full-repository checks and final independent review are documented separately
from these bounded results.
