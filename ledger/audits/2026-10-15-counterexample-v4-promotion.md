# Corrected-v10 Theorem 6.1: version 4 promotion

15 October 2026. This status-only promotion changes `thm-counterexample@4`
from `SEALED` to `PROVED`. Its frozen statement, proof, provider, source pins
and four literal definitions are unchanged.

The exact export is `Exploding.Frozen.counterexample`, with only the outward
inputs `d : ℕ` and `2 ≤ d`. One explosive background supplies the failure of
the lower height bound, finite axial arrivals, `limsup ≥ 3/2`, `liminf = 1`
and failure of every measurable symmetric-difference-volume limit. There is
no cited-result binder or caller-supplied witness or proof step.

The pinned source is `paper/corrected-arxiv/exploding-corrected-arxiv.tex`,
SHA-256 `59b5ac1a5cdf80c5b550dfc1738414892e0aa3f8cdb0bf03d00c74685a3e1be2`,
with input `paper/corrected-arxiv/defs.tex`, SHA-256
`9aba2c73246d79e3c6b87cb1f01cf3e2f636e27c8afd97ccb8ba5c032a9ee65b`.
The theorem is at lines 1875–1885 and its same-background volume argument at
2337–2373. Its exact hashes are:

| Surface | SHA-256 |
|---|---|
| Frozen marker | `1af0799acd9eccce67b979a6a59e756398fd513054e9019f1118421bf7ecf178` |
| Semantic closure | `616c1a01e21168c1b7e7840e907d5365135b1877df7e22d79132500a0ccae600` |
| Whole Frozen file | `8af8ce219791bec742fb2106a26e7895f4255a653594c9958545b049a645cf32` |

The four literal definitions remain `FROZEN`: threshold at 100–102, pile at
103, arrival at 118 and support at 109–111, with the nearest-site tie rule at
173–174. Independent audit checked their full bodies and public carriers.
They add zero numbered-theorem coverage.

The accepted declaration tree was independently audited as tree
`ab7e842c1044efcb4a51e132f2ba43857d72d99c`, then committed as
`fdf71fe0302b054b6de0f5c76e8f404f2edb0d70` with the same tree. Its integrated
baseline at `93ade26b580e0067a7ed368664bef65543e5830b` completed a full locked
build of 9,405 jobs. All eleven configured checks passed: manifest, axioms,
warnings, constants, generated documentation, clauses, coverage, exponents,
source anchors, citations and assumptions. The axiom check found 39 clean
nodes, zero `sorryAx` dependencies and zero unresolved exports. The exact
Frozen/public applications, four defining equations and inhabited `d = 2`
witness were checked; the theorem and definition closures used only
`propext`, `Classical.choice` and `Quot.sound`.

The retained evidence is bound by SHA-256:

| Record | SHA-256 |
|---|---|
| Exact-declaration ruling, `R-EXPLODING-COUNTEREXAMPLE-V10-20261015.md` | `1f53b9e3e8b88533156646d6b1c331559fdf5a459df8632b3a51bc21aa355f43` |
| Independent final source/body/consumer audit report | `75135b1cee4320cebf1eb00c5d65f6106e0215186c77d59706c1472ca742e7a6` |
| Independent audit evidence inventory | `a813f5017537a8f7d0080708bcca8317a5fb2c8b8cc58d13a9581195fbca2c8f` |
| Integrated full-build log | `77cee0921abcf23159154d29cc2af83834ed709f6cdcb3b132144e7f77a49e2e` |
| Integrated eleven-check result | `bdca0bb1ff609243ee4b331f9e9da9273f2a514fa952a7ab0579617d8d10ae69` |

The aggregate is 28 `PROVED` rows: 22 paper-owned rows across the historical
and corrected source pins, plus six cited-input discharges. Eleven
definitions remain `FROZEN`: seven historical cited inputs and four literal
local definitions. No row remains `SEALED`. All other manifest rows,
including `lem-finite-exploding@7` with `0 < p ≤ 1`, are preserved.

Structural coverage remains old-source 23/24 and corrected-v10 1/24. The
other 23 corrected-v10 statements and the nine remaining strict Bernoulli
`p < 1` rows retain their gaps. The seven historical cited inputs remain
registered, and Antal–Pisztora remains an assumed cited input. The official
arXiv source and the corrected draft's abstract are unchanged.

The accompanying root imports expose the already reviewed ordinary
`ArxivBondHoleGeometry` and `ArxivBondHoleTail` modules to the next full build.
Those modules receive no numbered-theorem credit here. Corrected Proposition
2.2, the fixed-root hole tail and its exact alpha constant remain outside this
promotion. The build evidence above certifies the preserved declaration tree;
the final integration checks must also cover these two added root imports.
