# ExplodingAudit Comparator Surface

This directory contains a Mathlib-only comparator challenge for the limit shape theorem
(Theorem 1.2 of *A shape theorem for exploding sandpiles*, Ahmed Bou-Rabee, label
`theorem:limit_shape` at `paper/corrected-arxiv/exploding-corrected-arxiv.tex:104-112`).

| Directory | Checked theorem |
| --- | --- |
| `LimitShape/` | `Exploding.StatementAudit.LimitShape.limit_shape` |

`LimitShape/Challenge.lean` imports only `Mathlib`, rebuilds from scratch every definition
needed to read the theorem, states it, and ends with one `sorry`, the proof being checked.  The
definitions rebuilt are the lattice `Site d = Fin d → ℤ` with its unit vectors, nearest-neighbour
graph `lattice` and components `componentIn`; parallel toppling (`lap`, the odometer `podo`,
`Stabilizable`, the explosion threshold `explosionThreshold`, the exploding sandpile
`explodingPile`); the nearest lattice point `nearestSite`; the boxes `cube` and `cent` and the
norm `mnorm`; the bootstrap-percolation odometer `spanOdo` with `InternallySpanned`; the
background law `toyLaw` with `productLaw` and `chipLaw`; Bernoulli site and bond percolation
(`bitLaw`, `sitePercolation`, `openSites`, `IsInfiniteOpenCluster`, `bondPercolation`,
`openBondGraph`, `bondTheta`, `bondCritical`, `bernoulliProduct`, `IsIncreasingSet`,
`HasDependenceGraph`); and the four cited results that the theorem takes as hypotheses.

## What Is Checked

A *background* is a function `η : ℤ^d → ℤ` counting chips.  Add `n` chips at the origin and
topple in parallel: every site holding at least `2d` chips fires, sending one chip to each
neighbour.  The odometer `v_t = podo s₀ t` counts the topplings by time `t`.  The explosion
threshold `M_η` is the least `n ≥ 1` for which `η + n δ₀` does not stabilize, and the exploding
sandpile is `η + M_η δ₀`.  For `d ≥ 2` and `0 < p ≤ 1`, the theorem states that there is a
set `B ⊆ ℝ^d` that is convex, open and nonempty (a convex domain), chosen before the
background, such that for almost every `η` drawn from `toyLaw d p` (`2d - 1` chips with
probability `p` and `2d - 2` with probability `1 - p` at each site, independently),

```
| {y : v_t([t y]) > 0} △ B |  →  0      as t → ∞,
```

where `[·]` is the nearest lattice point `nearestSite`, `|·|` is Lebesgue measure on `ℝ^d`, and
`△` is the symmetric difference.  The endpoint `p = 1` is included; it is the deterministic
background `η ≡ 2d - 1`.

The theorem takes as explicit hypotheses four results that the paper cites; each is a
`Prop`-valued definition in the challenge.

- `LiggettSchonmannStaceyBoundedDegree`: Corollary 1.4 of Liggett, Schonmann and Stacey,
  *Domination by product measures* (domination of a bounded-degree dependent field of bits by a
  product measure of density close to one).
- `MathieuHoleVolume`: Lemma 5.2 of Mathieu, *Quenched invariance principles for random walks
  with random conductances* (the holes of the infinite cluster of highly supercritical site
  percolation have volume below `(log n)^{5/2}`).
- `AntalPisztoraChemicalDistance`: Theorem 1.1 of Antal and Pisztora, *On the chemical distance
  for supercritical Bernoulli percolation* (the chemical distance in supercritical bond
  percolation exceeds `ρ |y|` with probability at most `e^{-c |y|}`).
- `SchonmannBootstrap`: Schonmann's large-deviation bound for bootstrap percolation
  (Proposition 7.4 of the paper).

The library proves three of them, as `Exploding.xlse_lss_bounded_degree`,
`Exploding.xmf_proved` and `Exploding.xsr_schonmann`; only `AntalPisztoraChemicalDistance` is
assumed.  The challenge keeps all four as hypotheses, as the library statement does.

The library statement is `Exploding.Frozen.limit_shape`
(`Exploding/Frozen/LimitShape.lean`), proved by `Exploding.LSProof.ls_assemble`
(`Exploding/Support/LSProofAux.lean`).  The challenge states the same theorem over the copied
vocabulary.

## Definition Provenance

The challenge definitions are statement-level copies of the repository definitions needed to
state the theorem surface, each with the same binders and the same body.  `Exploding` is the
library; `lattice-probability` is the `LatticeProb` dependency at the revision pinned in
`lake-manifest.json`.

| Challenge declaration | Repository source |
| --- | --- |
| `Site` | `lattice-probability`: `LatticeProb/Site.lean:19` |
| `unit` | `lattice-probability`: `LatticeProb/Site.lean:22` |
| `unit_ne_zero` | `lattice-probability`: `LatticeProb/Site.lean:24` |
| `lattice` | `lattice-probability`: `LatticeProb/Site.lean:30` |
| `componentIn` | `lattice-probability`: `LatticeProb/Site.lean:54` |
| `dirac` | `Exploding/Support/Toppling.lean:32` |
| `nbrSumZ` | `Exploding/Support/Toppling.lean:40` |
| `lap` | `Exploding/Support/Toppling.lean:62` |
| `podo` | `Exploding/Support/Toppling.lean:69` |
| `Stabilizable` | `Exploding/Support/Toppling.lean:90` |
| `explosionThreshold` | `Exploding/Support/Toppling.lean:102` |
| `cube` | `Exploding/Support/Vocab.lean:31` |
| `cent` | `Exploding/Support/Vocab.lean:34` |
| `mnorm` | `Exploding/Support/Vocab.lean:91` |
| `explodingPile` | `Exploding/Support/Vocab.lean:182` |
| `nearestSite` | `Exploding/Support/Vocab.lean:187` |
| `spanOdo` | `Exploding/Support/Vocab.lean:195` |
| `InternallySpanned` | `Exploding/Support/Vocab.lean:204` |
| `chipLaw` | `Exploding/Support/Vocab.lean:211` |
| `productLaw` | `Exploding/Support/Vocab.lean:215` |
| `toyLaw` | `Exploding/Support/Vocab.lean:220` |
| `bitLaw` | `Exploding/Support/Percolation.lean:19` |
| `sitePercolation` | `Exploding/Support/Percolation.lean:24` |
| `openSites` | `Exploding/Support/Percolation.lean:28` |
| `IsInfiniteOpenCluster` | `Exploding/Support/Percolation.lean:32` |
| `bondPercolation` | `Exploding/Support/Percolation.lean:53` |
| `openBondGraph` | `Exploding/Support/Percolation.lean:57` |
| `bondTheta` | `Exploding/Support/Percolation.lean:62` |
| `bondCritical` | `Exploding/Support/Percolation.lean:67` |
| `bernoulliProduct` | `Exploding/Support/Percolation.lean:73` |
| `IsIncreasingSet` | `Exploding/Support/Percolation.lean:78` |
| `HasDependenceGraph` | `Exploding/Support/Percolation.lean:84` |
| `LiggettSchonmannStaceyBoundedDegree` | `Exploding/External/LiggettSchonmannStaceyBoundedDegree.lean:31` |
| `MathieuHoleVolume` | `Exploding/External/MathieuHoles.lean:28` |
| `AntalPisztoraChemicalDistance` | `Exploding/External/AntalPisztora.lean:29` |
| `SchonmannBootstrap` | `Exploding/External/Schonmann.lean:23` |

The theorem itself, `limit_shape`, is `Exploding.Frozen.limit_shape` with the namespace
qualifiers removed from its name and from the four hypotheses.

## Reproducing The Checks

The comparator configuration permits only

```json
["propext", "Quot.sound", "Classical.choice"]
```

and enables the nanoda replay.  The challenge elaborates standalone against this repository's
Mathlib toolchain:

```bash
bash ExplodingAudit/check_standalone.sh ExplodingAudit/LimitShape/Challenge.lean
bash ExplodingAudit/check_standalone.sh --vocabulary   # Challenge vs SolutionBasic
```

with expected outcome `rc=0` and exactly one `declaration uses 'sorry'` warning.  The solution
builds with `lake build ExplodingAudit`.  Then, with `leanprover/comparator`, `lean4export` (at
the toolchain's tag), nanoda and `landrun` built at the pins below, from the repository root:

```bash
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator ExplodingAudit/LimitShape/comparator.json
```

expecting `Your solution is okay!`.

**Status.**  The challenge elaborates on Mathlib alone with one intentional `sorry`; the
solution builds and proves the byte-identical statement from `Exploding.Frozen.limit_shape`
through `ExplodingAudit/Support/LimitShapeBridge.lean`; `leanprover/comparator` at commit
`575674928e239f5bc452aab72d1dd7b0f1326494`, with nanoda at
`6ae1f0cd962f081f6c423454c5da729d841236a7` and landrun at
`811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`, printed `Your solution is okay!` with the nanoda
kernel enabled.
