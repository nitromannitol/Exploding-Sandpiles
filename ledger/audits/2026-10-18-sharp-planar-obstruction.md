# Sharp planar obstruction, 18 October 2026

This record binds `Exploding.Frozen.sharp_planar_obstruction` (node
`rem-sharp-planar-obstruction`, version 1) to the unnumbered remark "Sharp planar
obstruction" at lines 785-823 of the corrected arXiv-format draft, SHA-256
`c99ce52a57b7da1f805efe610c474c968c0aa00e0840bd8b0e92ae0d4c53f262`, with its
`defs.tex` input, SHA-256
`9aba2c73246d79e3c6b87cb1f01cf3e2f636e27c8afd97ccb8ba5c032a9ee65b`.
No source byte changes.

## Statement

On homogeneous height 2 in dimension two there are constants `c, C > 0`, chosen
before `n`, such that every `n ≥ 1` has a positive order `M` whose wave from the
origin covers `cent 2 n` (each site at some time), which is at most every
positive covering order, and which satisfies
`c n² log (n + 1) ≤ M ≤ C n² log (n + 1)`. The least order is characterized
inside the statement; no minimum or default-valued function is defined. Both
bounds concern the same `M`, and the constants are uniform over all `n ≥ 1`.

The only hypotheses are the two cited inputs already used by the sharp square
lower bound: `Exploding.External.FeyDenBoerRedigCubicalCluster` and
`Exploding.External.FeyLevinePeresRadius`. No new cited input, External or
paper-owned premise is introduced. The existence and uniqueness of the least
positive covering order is proved separately without cited inputs
(`Exploding.planar_wave_least_order_exists_unique`, nonvacuity consumer at `n = 1`).

## Proof

`Exploding.planar_wave_order_bounds` in `Exploding/Support/PlanarWaveOptimality.lean`.

- Upper bound: the sharp square lower bound at `d = 2`, `η ≡ 2`, with
  `m = ⌈C₀ n² log (n + 1)⌉ + 1`, and leastness of `M`.
- Lower bound at large scales: for an integer `a ≥ A` (the Fey-Levine-Peres radius
  constant) and `k = ⌊n / (a + 1)⌋`, the parallel toppling of `2 + k² δ₀` stabilizes
  at a common time (Fey-den Boer and Redig) and its odometer vanishes off the box of
  radius `a k` (Fey, Levine and Peres). The lower origin estimate, the planar
  logarithmic killed-Green lower bound of Lattice-Probability
  (`LatticeProb.planar_killedGreen_zero_zero_log_lower`) and the row-sum bound give
  `v(0) ≥ (c₀ / 2) k² log (k + 2)` beyond an explicit cutoff. The site `(n, 0)` of
  the cube lies outside that box, so the covering comparison gives `v(0) < m` for
  every covering order `m`.
- Small scales: `M ≥ 1` and a reduced constant.

This route uses the potential-kernel lower bound for the killed Green function
instead of the printed early-return calculation; the printed argument is not
changed.

## Review and checks

The statement, binders, carriers, definition bodies, consumption of every
intermediate fact, and the proof composition were reviewed independently against
the source. The exported theorem and both public helpers
(`Exploding.planar_wave_cover_order_lower_eventually`,
`Exploding.planar_wave_cover_order_upper`) report exactly `propext`,
`Classical.choice` and `Quot.sound`.
