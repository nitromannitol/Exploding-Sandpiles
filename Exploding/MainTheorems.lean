import Exploding.Frozen.SquareLowerBound
import Exploding.Frozen.LastWaveBound
import Exploding.Frozen.DimensionalReduction
import Exploding.Frozen.ApproxSubadditivity
import Exploding.Frozen.Recurrence

/-!
# Main results

The formalization of *A shape theorem for exploding sandpiles* (Ahmed Bou-Rabee) is a work
in progress, and **none of the paper's main results is proved yet**.  Their frozen
statements are registered:

* `Exploding.Frozen.limit_shape`: Theorem 1.2, the toppled region of the exploding
  sandpile with the Bernoulli background `(1.2)`, rescaled by time, converges in measure to
  a convex domain.  Open: its proof is a single `sorry`.
* `Exploding.Frozen.convergence_of_time_constant`: Theorem 1.3, the rescaled arrival times
  converge locally uniformly to a continuous, convex, one-homogeneous function.  Its proof
  is written, from Propositions 3.1 and 4.1 and the cited Theorem 1.1, but both
  propositions are still open, so it is not yet proved.
* `Exploding.Frozen.explosive`: Theorem 1.4, a product background with at least `d` chips
  at every site and a positive density of sites with `2d - 1` chips explodes almost surely.
  Open.
* `Exploding.Frozen.generalized_convergence`: Theorem 5.1, convergence of the exploding
  sandpile under the hypotheses of Section 5.  Its proof is written, from Proposition 5.1
  and the wave-approximation hypothesis, but Proposition 5.1 is still open.
* `Exploding.Frozen.counterexample`: Theorem 6.1, explosive backgrounds without a limit
  shape.  Open.

None of the declarations above is restated here, since this file states only what is
proved.  Each of them takes the results the paper cites for it, from Theorem 1.1 (Fey,
Levine and Peres) to the percolation results behind Proposition 2.2, as explicit
hypotheses stated in `Exploding/External/`; see `ASSUMPTIONS.md`.

The theorems below are the results of the paper that **are** proved.  Each restates its
certified counterpart in `Exploding/Frozen/` unchanged and is proved by `exact` of it, so
the statements displayed in this file are the certified ones.  None of them takes a cited
result as a hypothesis.

The model is that of `Exploding/Support/Toppling.lean` and
`Exploding/Support/Vocab.lean`: a background `η : Site d → ℤ` counts chips at each site,
`Exploding.lastWave` and `Exploding.penultimateWave` are the last and penultimate waves of
Section 3, `Exploding.clusterArrival` the penultimate-cluster arrival time, and
`Exploding.Recurrent` recurrence in the sense of Section 7.  The constrained processes of
Section 7.1 are in `Exploding/Support/Reduction.lean`.

All five reduce to the standard axioms (`propext`, `Classical.choice`, `Quot.sound`); see
`Exploding/Meta/AxiomsAudit.lean`.
-/

open Exploding LatticeProb

/-- **Lemma 3.1** (`lemma:square_lower_bound`): on a nonnegative background, for `n ≥ 1`
and `m ≥ (2d)^{dn}`, every site of `[-n, n]^d` is reached by the `m`-wave started at the
origin: the wave is positive there at some time.  The certified statement is
`Exploding.Frozen.square_lower_bound`, restated unchanged. -/
theorem Exploding.square_lower_bound (d : ℕ) (hd : 2 ≤ d) :
    ∀ η : Site d → ℤ, (∀ x, 0 ≤ η x) → ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, (2 * d) ^ (d * n) ≤ m →
      ∀ x ∈ cent d n, ∃ t : ℕ, 0 < wave η m (0 : Site d) t x := by
  exact Exploding.Frozen.square_lower_bound d hd

/-- **Lemma 3.3** (`lemma:last_wave_bound`): for a background with `2d - 2 ≤ η ≤ 2d - 1`
whose last wave from `z` is well defined, the last wave exceeds the penultimate wave by at
most one at every site and every time `t ≥ 1`.  The certified statement is
`Exploding.Frozen.last_wave_bound`, restated unchanged. -/
theorem Exploding.last_wave_bound (d : ℕ) (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (z : Site d) (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n z)
    (t : ℕ) (ht : 1 ≤ t) (x : Site d) :
    lastWave η z t x ≤ 1 + penultimateWave η z x := by
  exact Exploding.Frozen.last_wave_bound d hd η hlow hhigh z hlast t ht x

/-- **Lemma 3.4** (`lemma:approx_subadditivity`): under the same standing hypotheses, with
the last wave well defined from every site, the penultimate-cluster arrival times are
subadditive.  The certified statement is `Exploding.Frozen.approx_subadditivity`, restated
unchanged. -/
theorem Exploding.approx_subadditivity (d : ℕ) (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (hlast : ∀ y : Site d, ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n y)
    (a b z : Site d) :
    clusterArrival η a z ≤ clusterArrival η a b + clusterArrival η b z := by
  exact Exploding.Frozen.approx_subadditivity d hd η hlow hhigh hlast a b z

/-- **Proposition 7.2** (`prop:dimensional_reduction`), with the paper's `d` written
`d + 1`: at every time, on the face `F_1(Q_n)` of the box, the constrained odometer in
`ℤ^{d+1}` equals the one in `ℤ^d`, and where it vanishes the configuration in `ℤ^{d+1}`
exceeds the one in `ℤ^d` by `2`.  The certified statement is
`Exploding.Frozen.dimensional_reduction`, restated unchanged. -/
theorem Exploding.dimensional_reduction (d n : ℕ) (hd : 1 ≤ d) (η : Site (d + 1) → ℤ)
    (t : ℕ) (y : Site d) (hy : cons 1 y ∈ faceLow (d + 1) n 0) :
    redOdoUp n η t (cons 1 y) = redOdoDown n η t y ∧
      (redOdoUp n η t (cons 1 y) = 0 →
        redConfUp n η t (cons 1 y) = redConfDown n η t y + 2) := by
  exact Exploding.Frozen.dimensional_reduction d n hd η t y hy

/-- **Proposition 7.3** (`prop:recurrence`): the constant background `d` on `ℤ^d` is
recurrent.  The certified statement is `Exploding.Frozen.recurrence`, restated unchanged. -/
theorem Exploding.recurrence (d : ℕ) (hd : 1 ≤ d) : Recurrent (fun _ : Site d => (d : ℤ)) := by
  exact Exploding.Frozen.recurrence d hd
