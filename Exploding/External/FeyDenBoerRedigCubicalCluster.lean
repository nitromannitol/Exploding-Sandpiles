import LatticeProb.External.FeyDenBoerRedigCubicalCluster

/-!
# Cited input: cubical toppling clusters (Fey-den Boer and Redig)

Literal alias of the cited-input proposition `LatticeProb.External.FeyDenBoerRedigCubicalCluster`.
Source: A. Fey-den Boer and F. Redig, *Limiting shapes for deterministic centrally seeded growth
models*, [arXiv:math/0702450v2](https://arxiv.org/abs/math/0702450v2), Theorem 4.1, printed p. 7.
Only the cubical toppled-support and lower-radius conclusion is cited; the constructive proof
is on pp. 8-9 and is not reproduced here.

Height convention: Section 2 of the source uses total origin height `n` over background height
`h`. Here `h = 2 * d - 2` and `N` counts the extra chips, so the total origin height is
`n = N + h = N + 2 * d - 2`. This is the total-origin convention. It differs from the extra-chip
`n` convention of `Exploding.External.FeyLevinePeresRadius`.

The proposition is a cited, unproved input. Its definition is the literal cited statement and
asserts no proof of it.
-/


/-- The cited Fey-den Boer and Redig cubical-cluster proposition, with total origin height
`N + 2 * d - 2`. -/
-- FROZEN-STATEMENT-BEGIN
def Exploding.External.FeyDenBoerRedigCubicalCluster : Prop :=
  LatticeProb.External.FeyDenBoerRedigCubicalCluster
-- FROZEN-STATEMENT-END

/-- Definitional characterization of the alias: it unfolds to the Lattice-Probability cited
proposition. -/
theorem Exploding.External.FeyDenBoerRedigCubicalCluster_iff :
    Exploding.External.FeyDenBoerRedigCubicalCluster ↔ LatticeProb.External.FeyDenBoerRedigCubicalCluster :=
  Iff.rfl

