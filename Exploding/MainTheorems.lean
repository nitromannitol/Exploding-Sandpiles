import Exploding.Frozen.LimitShape
import Exploding.Frozen.TimeConstant
import Exploding.Frozen.Explosive
import Exploding.Frozen.CrossingTime
import Exploding.Frozen.Renormalization
import Exploding.Frozen.LocalConvexity
import Exploding.Frozen.SquareLowerBound
import Exploding.Frozen.FiniteExploding
import Exploding.Frozen.LastWaveBound
import Exploding.Frozen.ApproxSubadditivity
import Exploding.Frozen.PenultimateCluster
import Exploding.Frozen.PenultimateUpperBound
import Exploding.Frozen.PenultimateClose
import Exploding.Frozen.LastWaveConvergence
import Exploding.Frozen.ApproximateSubadditive
import Exploding.Frozen.GeneralizedLastWave
import Exploding.Frozen.GeneralizedConvergence
import Exploding.Frozen.Counterexample
import Exploding.Frozen.ExplosionCriteria
import Exploding.Frozen.DimensionalReduction
import Exploding.Frozen.Recurrence
import Exploding.Frozen.BoxCrossing

/-!
# Main results

This file gives the public paper-facing theorem statements. The 21 existing paper-owned
old-source statements retain their corrected-journal contracts, including the proved
finite-exploding version 7 with `0 < p ≤ 1`. The nine other strict Bernoulli paper rows
retain their `p < 1` premises. Theorem 6.1 below is the
proposed corrected-v10 v4 successor; its full proof and public type await the exact integrated
Lean checks and independent final-byte audit. The proposal does not certify any other v10
statement. Existing baseline axiom and build records do not cover this candidate.

The existing main theorems and the proposed counterexample are:

* `Exploding.limit_shape`: Theorem 1.2, the region toppled by time `t`, rescaled by `t`,
  converges in measure to a convex domain.
* `Exploding.convergence_of_time_constant`: Theorem 1.3, the rescaled arrival times converge
  locally uniformly to a continuous, convex, one-homogeneous function.
* `Exploding.explosive`: Theorem 1.4, a product background with at least `d` chips at every
  site and a positive density of sites with `2d - 1` chips explodes almost surely.
* `Exploding.generalized_convergence`: Theorem 5.1, convergence of the exploding sandpile
  under the hypotheses of Section 5.
* `Exploding.counterexample`: proposed corrected-v10 Theorem 6.1; its complete conclusion
  uses one background for both axial limits and the measurable-volume obstruction.

The other public results summarize old-source Propositions 2.1, 2.2, 3.1, 4.1, 5.1, 7.1,
7.2, 7.3 and 7.5 and Lemmas 2.1 and 3.1 to 3.7.

## Cited results

Seven historical literature results that the paper cites remain registered as assumptions.
Each is a proposition in `Exploding/External/` with the old-source pin; a theorem carries one
when its exact type has that hypothesis. The proposed v4 Theorem 6.1 has no cited-result
binder, and no `axiom` is declared (see `ASSUMPTIONS.md`):

* `FeyLevinePeresExplosive`, Theorem 1.1 of the paper (Proposition 1.4 of Fey, Levine and
  Peres), `hFLP`;
* `SchonmannBootstrap`, Proposition 7.4 of the paper (Schonmann's large-deviation bound for
  bootstrap percolation), `hSch`;
* `LiggettSchonmannStacey`, Theorem 0.0 of Liggett, Schonmann and Stacey, cited in the proof
  of Proposition 5.1, `hLSS`;
* `LiggettSchonmannStaceyBoundedDegree` (Corollary 1.4 of Liggett, Schonmann and Stacey),
  `AntalPisztoraChemicalDistance` (Theorem 1.1 of Antal and Pisztora) and `MathieuHoleVolume`
  (Lemma 5.2 of Mathieu), the three percolation results cited before Proposition 2.2,
  `hLSSB`, `hChem`, `hHole`;
* `FeyMeesterRedigLeastAction`, Theorem 2.8 of Fey, Meester and Redig, retained in the
  historical journal-source Theorem 6.1 record, `hFMR`.

Six of the seven are discharged by proofs in this repository:

* The historical FMR registration is separately proved by `Exploding.xfmr_proved`
  (`Exploding/Support/ExtFMR.lean`); FMR is not a premise of proposed v4 Theorem 6.1;
* `LiggettSchonmannStaceyBoundedDegree` is proved by `Exploding.xlse_lss_bounded_degree`
  and `LiggettSchonmannStacey` by `Exploding.xlse_lss_general`
  (`Exploding/Support/ExtLSSCountable.lean`), so `hLSSB` and `hLSS` may be discharged
  everywhere they occur;
* `MathieuHoleVolume` is proved by `Exploding.xmf_proved`
  (`Exploding/Support/ExtMHHoleVolume.lean`), so `hHole` may be discharged everywhere it occurs;
* `SchonmannBootstrap` is proved by `Exploding.xsr_schonmann`
  (`Exploding/Support/ExtSchFinal.lean`), so `hSch` may be discharged everywhere it occurs;
* `FeyLevinePeresExplosive` follows from `SchonmannBootstrap` by
  `Exploding.LSProof.ls_flp_from_explosive` (`Exploding/Support/LSProofAux.lean`), because
  Theorem 1.4 strengthens Theorem 1.1, so `hFLP` of Theorem 1.3 may be replaced by `hSch`;
  `Exploding.xsr_flp` (`Exploding/Support/ExtSchFLP.lean`) applies it to
  `Exploding.xsr_schonmann`, so `hFLP` may be discharged everywhere it occurs.  Theorem 1.2
  already does so in its proof.

The other one, `AntalPisztoraChemicalDistance`, is assumed.  The results below take the
cited results as follows, `perc` standing for the
three percolation results `hLSSB`, `hHole`, `hChem`:

| result | cited hypotheses taken |
|---|---|
| Theorem 1.2 | `perc`, `hSch` |
| Theorem 1.3 | `perc`, `hFLP` |
| Theorem 1.4, Proposition 7.5 | `hSch` |
| Proposition 2.2, Lemmas 3.2, 3.5, 3.6, 3.7, Propositions 3.1, 4.1 | `perc` |
| Proposition 5.1, Theorem 5.1 | `perc`, `hLSS` |
| Theorem 6.1 v4 candidate | none; its proposed type has no cited-result binder |
| Propositions 2.1, 7.1, 7.2, 7.3, Lemmas 2.1, 3.1, 3.3, 3.4 | none |

Propositions 5.1 and 7.1 and Theorem 5.1 also carry the model hypotheses of Sections 5 and 7
(finite range of dependence, path-filling, box-crossing, recurrence, wave approximation);
these are assumptions on the law of the background, not cited results.

## The model

The model is that of `Exploding/Support/Toppling.lean` and `Exploding/Support/Vocab.lean`: a
background `η : Site d → ℤ` counts chips at each site, `Exploding.arrival` is the arrival
time of the exploding sandpile `η + M_η δ₀`, `Exploding.lastWave` and
`Exploding.penultimateWave` are the last and penultimate waves of Section 3,
`Exploding.lastArrival` and `Exploding.clusterArrival` their arrival times, and
`Exploding.Recurrent` is recurrence in the sense of Section 7.  The constrained processes of
Section 7.1 are in `Exploding/Support/Reduction.lean`, and the hypotheses of Sections 5 and 7
in `Exploding/Support/Hypotheses.lean`.  The readings of the paper's statements that are not
literal are listed in `CORRESPONDENCE.md`.
-/

open Exploding LatticeProb MeasureTheory Filter

/-- **Theorem 1.2** (`theorem:limit_shape`): the region toppled by time `t` in the exploding
sandpile `η + M_η δ₀` with the Bernoulli background `(1.2)`, rescaled by `t`, converges in
measure to a convex domain, here a nonempty open convex set `B`: almost surely the volume of
the symmetric difference of `B` and `{y | 0 < podo (explodingPile η) t [t y]}` tends to `0`.
It takes the three percolation results behind Proposition 2.2 (`hLSSB`, `hHole`, `hChem`)
and Schonmann's bound (`hSch`) as hypotheses; Theorem 1.1 is discharged in the proof by
`Exploding.LSProof.ls_flp_from_explosive`.  The certified statement is
`Exploding.Frozen.limit_shape`, restated unchanged. -/
theorem Exploding.limit_shape (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance)
    (hSch : Exploding.External.SchonmannBootstrap) :
    ∃ B : Set (Fin d → ℝ),
      Convex ℝ B ∧ IsOpen B ∧ B.Nonempty ∧
      ∀ᵐ η ∂(toyLaw d p),
        Tendsto
          (fun t : ℕ =>
            volume (symmDiff
              {y : Fin d → ℝ | 0 < podo (explodingPile η) t (nearestSite ((t : ℝ) • y))} B))
          atTop (nhds 0) := by
  exact Exploding.Frozen.limit_shape d hd p hp hp1 hLSSB hHole hChem hSch

/-- **Theorem 1.3** (`theorem:convergence_of_time_constant`): there is a continuous, convex,
one-homogeneous function `N` such that almost surely the background is explosive, every
arrival time `T_η(x)` is finite, and the rescaled arrival times `T_η([n y]) / n` converge to
`N y` uniformly for `y` in every compact set.  It takes Theorem 1.1 (`hFLP`) and the three
percolation results behind Proposition 2.2 as hypotheses.  The certified statement is
`Exploding.Frozen.convergence_of_time_constant`, restated unchanged. -/
theorem Exploding.convergence_of_time_constant (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p)
    (hp1 : p < 1)
    (hFLP : Exploding.External.FeyLevinePeresExplosive)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ N : (Fin d → ℝ) → ℝ,
      Continuous N ∧
      ConvexOn ℝ Set.univ N ∧
      (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
      ∀ᵐ η ∂(toyLaw d p),
        Explosive η ∧ (∀ x : Site d, arrival η x ≠ ⊤) ∧
          ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
            ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
              |((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ) - N y| ≤ ε := by
  exact Exploding.Frozen.convergence_of_time_constant d hd p hp hp1 hFLP hLSSB hHole hChem

/-- **Theorem 1.4** (`theorem:explosive`): a product background with at least `d` chips at
every site and a positive density of sites with `2d - 1` chips explodes almost surely.  The
certified statement is `Exploding.Frozen.explosive`, restated unchanged. -/
theorem Exploding.explosive (d : ℕ) (hd : 2 ≤ d) (ν : Measure ℤ) (hν : IsProbabilityMeasure ν)
    (hlow : ν {m : ℤ | (d : ℤ) ≤ m} = 1) (hhit : 0 < ν {(2 * (d : ℤ) - 1)})
    (hSch : Exploding.External.SchonmannBootstrap) :
    ∀ᵐ β ∂(Measure.infinitePi fun _ : Site d => ν), Explosive β := by
  exact Exploding.Frozen.explosive d hd ν hν hlow hhit hSch

/-- **Proposition 2.1** (`prop:crossing_time`): for every `δ > 0` there is a side length
`k` so that with probability at least `1 - δ` every line across the box `Q_k` carries a
`(2d-1)`-chip catalyst, hence every crossing time is at most `k^d`.  The certified
statement is `Exploding.Frozen.crossing_time`, restated unchanged. -/
theorem Exploding.crossing_time (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ k : ℕ, 1 ≤ k ∧ ENNReal.ofReal (1 - δ) ≤ toyLaw d p {η | GoodCube η k} := by
  exact Exploding.Frozen.crossing_time d hd p hp hp1 δ hδ

/-- **Proposition 2.2** (`prop:renormalization_properties`): on an event of probability 1
an infinite connected set of good cubes has small holes and linear chemical distance.  The
certified statement is `Exploding.Frozen.renormalization_properties`, restated unchanged. -/
theorem Exploding.renormalization_properties (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᵐ η ∂(toyLaw d p),
        ∃ Cinf : Set (Site d), IsInfiniteConnectedGoodSet η k Cinf ∧
          (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)),
            x ∉ Cinf →
              (componentIn Cinfᶜ x).Finite ∧
                ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2)) ∧
          (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ Cinf, ∀ y ∈ Cinf,
            mnorm x ≤ (n : ℤ) → Real.log n ^ (2 : ℕ) ≤ (mnorm (x - y) : ℝ) →
              ∃ m : ℕ, chemDist Cinf x y = (m : ℕ∞) ∧
                c * (mnorm (x - y) : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ C * (mnorm (x - y) : ℝ)) := by
  exact Exploding.Frozen.renormalization_properties d hd p hp hp1 hLSSB hHole hChem

/-- **Lemma 2.1** (`lemma:local_convexity`): a finite path of topplings fills its
bounding rectangle: the `A`-frozen parallel toppling odometer started from `1` on `A`
equals `1` on `br A` from time `|br A|` on.  The certified statement is
`Exploding.Frozen.local_convexity`, restated unchanged. -/
theorem Exploding.local_convexity (d : ℕ) (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (m : ℕ) (z : ℕ → Site d) (hpath : ∀ i : ℕ, i < m → (lattice d).Adj (z i) (z (i + 1)))
    (A : Set (Site d)) (hA : A = z '' {i : ℕ | i ≤ m})
    (hfin : (br A).Finite) (t : ℕ) (ht : hfin.toFinset.card ≤ t)
    (x : Site d) (hx : x ∈ br A) :
    fodo A η (Set.indicator A 1) t x = 1 := by
  exact Exploding.Frozen.local_convexity d hd η hlow hhigh m z hpath A hA hfin t ht x hx

/-- **Lemma 3.1** (`lemma:square_lower_bound`): on a nonnegative background, for `n ≥ 1`
and `m ≥ (2d)^{dn}`, every site of `[-n, n]^d` is reached by the `m`-wave started at the
origin: the wave is positive there at some time.  The certified statement is
`Exploding.Frozen.square_lower_bound`, restated unchanged. -/
theorem Exploding.square_lower_bound (d : ℕ) (hd : 2 ≤ d) :
    ∀ η : Site d → ℤ, (∀ x, 0 ≤ η x) → ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, (2 * d) ^ (d * n) ≤ m →
      ∀ x ∈ cent d n, ∃ t : ℕ, 0 < wave η m (0 : Site d) t x := by
  exact Exploding.Frozen.square_lower_bound d hd

/-- **Lemma 3.2** (`lemma:finite_exploding`): the last wave is well defined,
`M̂_η(0) < ∞`.  The certified statement is `Exploding.Frozen.finite_exploding`, restated
unchanged. -/
theorem Exploding.finite_exploding (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∀ᵐ η ∂(toyLaw d p), ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d) := by
  exact Exploding.Frozen.finite_exploding d hd p hp hp1 hLSSB hHole hChem

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

/-- **Lemma 3.5** (`lemma:last_penultimate_cluster`): penultimate clusters are
polylogarithmically small.  The certified statement is
`Exploding.Frozen.last_penultimate_cluster`, restated unchanged. -/
theorem Exploding.last_penultimate_cluster (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
        ∀ y ∈ penultimateCluster η x, ∀ i, ((|y i - x i| : ℤ) : ℝ) ≤ Real.log n ^ γ := by
  exact Exploding.Frozen.last_penultimate_cluster d hd p hp hp1 hLSSB hHole hChem

/-- **Lemma 3.6** (`lemma:penultimate_upper_bound`): the last-wave arrival times obey a
linear upper bound up to a power of the logarithm.  The certified statement is
`Exploding.Frozen.penultimate_upper_bound`, restated unchanged. -/
theorem Exploding.penultimate_upper_bound (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧
      ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
        ∃ m : ℕ, lastArrival η (0 : Site d) x = (m : ℕ∞) ∧
          (m : ℝ) ≤ C * (mnorm x : ℝ) + Real.log n ^ γ := by
  exact Exploding.Frozen.penultimate_upper_bound d hd p hp hp1 hLSSB hHole hChem

/-- **Lemma 3.7** (`lemma:last_penultimate_close`): the last-wave and penultimate-cluster
arrival times are polylogarithmically close.  The certified statement is
`Exploding.Frozen.last_penultimate_close`, restated unchanged. -/
theorem Exploding.last_penultimate_close (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
        lastArrival η (0 : Site d) x ≤ clusterArrival η (0 : Site d) x ∧
          ∃ a b : ℕ, lastArrival η (0 : Site d) x = (a : ℕ∞) ∧
            clusterArrival η (0 : Site d) x = (b : ℕ∞) ∧ (b : ℝ) ≤ (a : ℝ) + Real.log n ^ γ := by
  exact Exploding.Frozen.last_penultimate_close d hd p hp hp1 hLSSB hHole hChem

/-- **Proposition 3.1** (`prop:convergence_of_the_last_wave`): the rescaled last-wave arrival
times `T̂_η(0, [n y]) / n` are almost surely finite and converge to a continuous, convex,
one-homogeneous function `N`, uniformly on compact sets.  It takes the three percolation
results behind Proposition 2.2 as hypotheses.  The certified statement is
`Exploding.Frozen.convergence_of_the_last_wave`, restated unchanged. -/
theorem Exploding.convergence_of_the_last_wave (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p)
    (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ N : (Fin d → ℝ) → ℝ,
      Continuous N ∧
      ConvexOn ℝ Set.univ N ∧
      (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
      ∀ᵐ η ∂(toyLaw d p),
        (∀ x : Site d, lastArrival η (0 : Site d) x ≠ ⊤) ∧
          ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
            ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
              |((lastArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
                - N y| ≤ ε := by
  exact Exploding.Frozen.convergence_of_the_last_wave d hd p hp hp1 hLSSB hHole hChem

/-- **Proposition 4.1** (`prop:approximate_subadditive`): the last wave is a bounded
approximation of the exploding sandpile: almost surely there are constants `C₁` and `C₂` with
`T_η(x) ≤ T̂_η(0, x) + C₁` and `T̂_η(0, x) ≤ T_η(x) + C₂` at every site `x`.  It takes the
three percolation results behind Proposition 2.2 as hypotheses.  The certified statement is
`Exploding.Frozen.approximate_subadditive`, restated unchanged. -/
theorem Exploding.approximate_subadditive (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p)
    (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∀ᵐ η ∂(toyLaw d p), ∃ C1 C2 : ℕ, ∀ x : Site d,
      arrival η x ≤ lastArrival η (0 : Site d) x + (C1 : ℕ∞) ∧
        lastArrival η (0 : Site d) x ≤ arrival η x + (C2 : ℕ∞) := by
  exact Exploding.Frozen.approximate_subadditive d hd p hp hp1 hLSSB hHole hChem

/-- **Proposition 5.1** (`prop:convergence_of_the_generalized_last_wave`): for a law `P` on
backgrounds with `η_min ≤ η ≤ 2d - 1`, stationary and ergodic for a finite-index sublattice
`L`, and satisfying finite range of dependence (Hypothesis 5.1), path-filling (Hypothesis 5.3)
and strong box-crossing (Hypothesis 5.4), the rescaled last-wave arrival times converge
almost surely, uniformly on compact sets, to a continuous, convex, one-homogeneous function,
and `P`-almost every background is explosive.  It takes the Liggett-Schonmann-Stacey
domination theorem (`hLSS`) and the three percolation results behind Proposition 2.2 as
hypotheses.  The certified statement is
`Exploding.Frozen.convergence_of_the_generalized_last_wave`, restated unchanged. -/
theorem Exploding.convergence_of_the_generalized_last_wave (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ)
    (hηmin : 0 ≤ ηmin)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0)
    (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (hstat : StationaryOn d L P) (herg : ErgodicOn d L P)
    (h1 : FiniteRangeOfDependence d P) (h3 : PathFillingHyp d P)
    (h4 : StronglyBoxCrossingHyp d P)
    (hLSS : Exploding.External.LiggettSchonmannStacey)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ N : (Fin d → ℝ) → ℝ,
      Continuous N ∧
      ConvexOn ℝ Set.univ N ∧
      (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
      ∀ᵐ η ∂P,
        Explosive η ∧ (∀ x : Site d, lastArrival η (0 : Site d) x ≠ ⊤) ∧
          ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
            ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
              |((lastArrival η (0 : Site d) (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ)
                - N y| ≤ ε := by
  exact Exploding.Frozen.convergence_of_the_generalized_last_wave d hd ηmin hηmin L hL P hP
    hsupp hstat herg h1 h3 h4 hLSS hLSSB hHole hChem

/-- **Theorem 5.1** (`Convergence of the exploding sandpile`): under the hypotheses of
Proposition 5.1 and the wave-approximation hypothesis (Hypothesis 5.5), the rescaled arrival
times `T_η([n y]) / n` of the exploding sandpile converge almost surely, uniformly on compact
sets, to a continuous, convex, one-homogeneous function, and every arrival time is finite.
It takes the Liggett-Schonmann-Stacey domination theorem (`hLSS`) and the three percolation
results behind Proposition 2.2 as hypotheses.  The certified statement is
`Exploding.Frozen.generalized_convergence`, restated unchanged. -/
theorem Exploding.generalized_convergence (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0)
    (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (hstat : StationaryOn d L P) (herg : ErgodicOn d L P)
    (h1 : FiniteRangeOfDependence d P) (h3 : PathFillingHyp d P)
    (h4 : StronglyBoxCrossingHyp d P) (h5 : WaveApproximationHyp d P)
    (hLSS : Exploding.External.LiggettSchonmannStacey)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ N : (Fin d → ℝ) → ℝ,
      Continuous N ∧
      ConvexOn ℝ Set.univ N ∧
      (∀ c : ℝ, 0 ≤ c → ∀ y : Fin d → ℝ, N (c • y) = c * N y) ∧
      ∀ᵐ η ∂P,
        Explosive η ∧ (∀ x : Site d, arrival η x ≠ ⊤) ∧
          ∀ K : Set (Fin d → ℝ), IsCompact K → ∀ ε : ℝ, 0 < ε →
            ∀ᶠ n : ℕ in atTop, ∀ y ∈ K,
              |((arrival η (nearestSite ((n : ℝ) • y))).toNat : ℝ) / (n : ℝ) - N y| ≤ ε := by
  exact Exploding.Frozen.generalized_convergence d hd ηmin hηmin L hL P hP hsupp hstat herg
    h1 h3 h4 h5 hLSS hLSSB hHole hChem

/-- **Theorem 6.1** (corrected arXiv-format source, exploding-corrected-arxiv.tex:1875-1885,
label theorem:counterexample; same-background volume obstruction at 2337-2373). One explosive
background has finite axial arrivals and both stated axial limits; for that same background,
no measurable set is a symmetric-difference-volume limit. Candidate proof and final audit pending. -/
theorem Exploding.counterexample (d : ℕ) (hd : 2 ≤ d) :
    ∃ η : Site d → ℤ, ∃ hη : Explosive η,
      (¬ ∀ x : Site d, 2 * (d : ℤ) - 2 ≤ η x) ∧
      (∀ n : ℕ, counterexampleArrival η hη ((n : ℤ) • e1 d) ≠ ⊤) ∧
      3 / 2 ≤ limsup
        (fun n : ℕ =>
          ((counterexampleArrival η hη ((n : ℤ) • e1 d)).toNat : ℝ) / (n : ℝ))
        atTop ∧
      liminf
        (fun n : ℕ =>
          ((counterexampleArrival η hη ((n : ℤ) • e1 d)).toNat : ℝ) / (n : ℝ))
        atTop = 1 ∧
      ¬ ∃ B : Set (Fin d → ℝ),
        MeasurableSet B ∧
        Tendsto
          (fun t : ℕ => volume (symmDiff (counterexampleSupport η hη t) B))
          atTop (nhds 0) := by
  exact Exploding.Frozen.counterexample d hd

/-- **Proposition 7.1** (`prop:explosion_criteria`): a stationary, ergodic,
finite-range-dependent, box-crossing and recurrent law on backgrounds bounded between
`η_min ≥ 0` and `2d - 1` is explosive.  The certified statement is
`Exploding.Frozen.explosion_criteria`, restated unchanged. -/
theorem Exploding.explosion_criteria (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0) (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (hstat : StationaryOn d L P) (herg : ErgodicOn d L P)
    (h1 : FiniteRangeOfDependence d P) (h2 : BoxCrossingHyp d P)
    (hrec : RecurrentLaw d P) :
    ExplosiveLaw d P := by
  exact Exploding.Frozen.explosion_criteria d hd ηmin hηmin L hL P hP hsupp hstat herg h1 h2 hrec

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

/-- **Proposition 7.5** (`exploding.tex:1986-1988`): a product background with at least `d`
chips at every site and a positive density of `(2d-1)`-sites is box-crossing.  The certified
statement is `Exploding.Frozen.box_crossing`, restated unchanged. -/
theorem Exploding.box_crossing (d : ℕ) (hd : 2 ≤ d) (ν : Measure ℤ) (hν : IsProbabilityMeasure ν)
    (hlow : ν {m : ℤ | (d : ℤ) ≤ m} = 1) (hhit : 0 < ν {(2 * (d : ℤ) - 1)})
    (hSch : Exploding.External.SchonmannBootstrap) :
    BoxCrossingHyp d (Measure.infinitePi fun _ : Site d => ν) := by
  exact Exploding.Frozen.box_crossing d hd ν hν hlow hhit hSch
