import LatticeProb.External.FeyLevinePeresRadius

/-!
# Cited input: outer radius of toppled sites (Fey, Levine and Peres)

Literal alias of the cited-input proposition `LatticeProb.External.FeyLevinePeresRadius`.
Source: A. Fey, L. Levine and Y. Peres, *Growth rates and explosions in sandpiles*,
[arXiv:0901.3805v2](https://arxiv.org/abs/0901.3805v2), Theorem 1.1, printed p. 4. The parallel
discrete toppling procedure of Section 2, pp. 5-6, is the one used by the definition, and the
toppled set is taken from the positive parallel odometer at some finite time.

Height convention: here `n` is the number of extra chips added to the background height `h` at
the origin, so the total origin height is `h + n`, with `d <= h <= 2 * d - 2`. This is the
extra-chip convention. It differs from the total-origin `n = N + h` convention of
`Exploding.External.FeyDenBoerRedigCubicalCluster`.

The proposition is a cited, unproved input. Its definition is the literal cited statement and
asserts no proof of it.
-/


/-- The eventual outer-radius bound of Fey, Levine and Peres, Theorem 1.1, for every positive
`ε` and background height `d <= h <= 2 * d - 2`. -/
-- FROZEN-STATEMENT-BEGIN
def Exploding.External.FeyLevinePeresRadius : Prop :=
  LatticeProb.External.FeyLevinePeresRadius
-- FROZEN-STATEMENT-END

/-- Definitional characterization of the alias: it unfolds to the Lattice-Probability cited
proposition. -/
theorem Exploding.External.FeyLevinePeresRadius_iff :
    Exploding.External.FeyLevinePeresRadius ↔ LatticeProb.External.FeyLevinePeresRadius :=
  Iff.rfl

