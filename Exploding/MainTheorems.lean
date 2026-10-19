import Exploding.Frozen.LimitShape
import Exploding.Frozen.TimeConstant
import Exploding.Frozen.Explosive
import Exploding.Frozen.CrossingTime
import Exploding.Frozen.Renormalization
import Exploding.Frozen.LocalConvexity
import Exploding.Frozen.SquareLowerBound
import Exploding.Frozen.SharpPlanarObstruction
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
import Exploding.External.LSSBoundedDegreeProved
import Exploding.Support.ExtLSSCountable
import Exploding.Support.ExtMHHoleVolume
import Exploding.Support.ExtSchFinal
import Exploding.Support.ExtSchFLP

/-!
# Main results

This file states the numbered results of A. Bou-Rabee, *A shape theorem for exploding
sandpiles*, in the corrected edition `paper/corrected-arxiv/exploding-corrected-arxiv.tex`, and
derives each from its statement in `Exploding/Frozen/`. Results are named by their number and
LaTeX label in that edition; its section "Corrections to the published version" lists every
change from arXiv v2.

The main theorems are:

* `Exploding.limit_shape`: Theorem 1.2, the region toppled by time `t`, rescaled by `t`,
  converges in volume to a nonempty open convex set.
* `Exploding.convergence_of_time_constant`: Theorem 1.3, the rescaled arrival times converge
  locally uniformly to a continuous, convex, one-homogeneous function.
* `Exploding.explosive`: Theorem 1.4, a product background with one common site law `ν` on `ℤ`
  satisfying `ν {m ≥ d} = 1` and `ν {2d - 1} > 0` explodes almost surely.
* `Exploding.generalized_convergence`: Theorem 5.1, convergence of the exploding sandpile
  under the hypotheses of Section 5.
* `Exploding.counterexample`: Theorem 6.1, an explosive background with no limit shape.

The other numbered results (Propositions 2.1, 2.2, 3.1, 4.1, 5.1, 7.1, 7.2, 7.3 and 7.5,
Lemmas 2.1 and 3.1 to 3.7, and the remark after Lemma 3.1) follow, together with the two
results the paper quotes, Theorem 1.1 and Proposition 7.4.

## Cited results

Each cited result is a proposition in `Exploding/External/` (or, for the two radius bounds, in
Lattice-Probability); no `axiom` is declared. Six are proved in this repository, and the
statements below are instantiated with those proofs, so they are not hypotheses here:

* Proposition 1.4 of Fey, Levine and Peres (Theorem 1.1 of the paper), `Exploding.xsr_flp`;
* Schonmann's bound for bootstrap percolation (Proposition 7.4), `Exploding.xsr_schonmann`;
* Theorem 0.0 and Corollary 1.4 of Liggett, Schonmann and Stacey, `Exploding.xlse_lss_general`
  and `Exploding.lssBoundedDegree`;
* Lemma 5.2 of Mathieu, `Exploding.xmf_proved`;
* Theorem 2.8 of Fey, Meester and Redig, `Exploding.xfmr_proved`, which no result below uses.

Three are hypotheses of the results that use them:

* Theorem 1.1 of Antal and Pisztora (chemical distance in supercritical bond percolation),
  `hChem`: Theorems 1.2, 1.3 and 5.1, Propositions 2.2, 3.1, 4.1 and 5.1, and Lemmas 3.2 and
  3.5 to 3.7;
* Theorem 4.1 of Fey, den Boer and Redig, `hFdBR`, and Theorem 1.1 of Fey, Levine and Peres
  (the radius of the toppled cluster), `hFLP`: Lemma 3.1 and the remark after it.

The statements in `Exploding/Frozen/` take every cited result they use as an explicit
hypothesis, including the six proved ones; the restatements here discharge those six.

Propositions 5.1 and 7.1 and Theorem 5.1 also carry the hypotheses of Sections 5 and 7 on the
law of the background (finite range of dependence, path-filling, box-crossing, recurrence,
wave approximation). Hypothesis 1 is used in the form "the values on two finite sets at
distance more than `K` are independent"; the published text states pairwise independence, and
whether these three results hold under the pairwise form is open.

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

/-- **Theorem 1.1** (`prop:fey_levine_peres_explode`, Proposition 1.4 of Fey, Levine and
Peres): for `d ≥ 2` and `0 < p ≤ 1`, the background of law `(1.2)` is explosive almost surely. -/
theorem Exploding.fey_levine_peres_explosive :
    ∀ d : ℕ, 2 ≤ d → ∀ p : ℝ, 0 < p → p ≤ 1 → ∀ᵐ η ∂(toyLaw d p), Explosive η :=
  Exploding.xsr_flp

/-- **Theorem 1.2** (`theorem:limit_shape`): for `d ≥ 2` and `0 < p ≤ 1`, there is a
nonempty open convex set `B` such that almost surely the volume of the symmetric difference of
`B` and the rescaled toppled region `{y | 0 < v_t([t y])}` of `η + M_η δ₀` tends to `0`.
The chemical-distance bound of Antal and Pisztora is a hypothesis. -/
theorem Exploding.limit_shape (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ B : Set (Fin d → ℝ),
      Convex ℝ B ∧ IsOpen B ∧ B.Nonempty ∧
      ∀ᵐ η ∂(toyLaw d p),
        Tendsto
          (fun t : ℕ =>
            volume (symmDiff
              {y : Fin d → ℝ | 0 < podo (explodingPile η) t (nearestSite ((t : ℝ) • y))} B))
          atTop (nhds 0) := by
  exact Exploding.Frozen.limit_shape d hd p hp hp1 Exploding.lssBoundedDegree Exploding.xmf_proved
    hChem Exploding.xsr_schonmann

/-- **Theorem 1.3** (`theorem:convergence_of_time_constant`): there is a continuous, convex,
one-homogeneous function `N` such that almost surely the background is explosive, every
arrival time `T_η(x)` is finite, and `T_η([n y]) / n` converges to `N y` uniformly for `y` in
every compact set. The chemical-distance bound of Antal and Pisztora is a hypothesis. -/
theorem Exploding.convergence_of_time_constant (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p)
    (hp1 : p ≤ 1)
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
  exact Exploding.Frozen.convergence_of_time_constant d hd p hp hp1 Exploding.xsr_flp
    Exploding.lssBoundedDegree Exploding.xmf_proved hChem

/-- **Theorem 1.4** (`theorem:explosive`): for `d ≥ 2` and a probability law `ν` on `ℤ` with
`ν {m ≥ d} = 1` and `ν {2d - 1} > 0`, the background with independent values of law `ν`
explodes almost surely. -/
theorem Exploding.explosive (d : ℕ) (hd : 2 ≤ d) (ν : Measure ℤ) (hν : IsProbabilityMeasure ν)
    (hlow : ν {m : ℤ | (d : ℤ) ≤ m} = 1) (hhit : 0 < ν {(2 * (d : ℤ) - 1)}) :
    ∀ᵐ β ∂(Measure.infinitePi fun _ : Site d => ν), Explosive β := by
  exact Exploding.Frozen.explosive d hd ν hν hlow hhit Exploding.xsr_schonmann

/-- **Proposition 2.1** (`prop:crossing_time`): for every `δ > 0` there is a cube scale `k` such
that, with probability at least `1 - δ`, for every direction and every seed on the closed
cube, the frozen process started from the delivered seed reaches the value one on the whole
cube, and does so by time `k^d`. -/
theorem Exploding.crossing_time (d : ℕ) (hd : 2 ≤ d)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ k : ℕ, 1 ≤ k ∧
      ENNReal.ofReal (1 - δ) ≤ toyLaw d p
        {η : Site d → ℤ |
          ∀ (i : Fin d) (z : Site d), z ∈ closureN (cube d k) →
            (∀ x ∈ cube d k, ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
              crossOdo η k i z t x = 1) ∧
            (∃ n : ℕ, 1 ≤ n ∧ n ≤ k ^ d ∧
              ∀ x ∈ cube d k, crossOdo η k i z n x = 1)
        } := by
  exact Exploding.Frozen.crossing_time d hd p hp hp1 δ hδ

/-- **Proposition 2.2** (`prop:renormalization_properties`): almost surely, for every large cube
scale, the good cubes have a unique infinite component `C∞`, the holes of `C∞` near the
origin have polylogarithmic volume, and chemical distances in `C∞` are comparable to
Manhattan distances. The chemical-distance bound of Antal and Pisztora is a hypothesis. -/
theorem Exploding.renormalization_properties (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
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
                c * (mnorm (x - y) : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ C * (mnorm (x - y) : ℝ)) ∧
          (∃ z ∈ goodSites η k, Cinf = componentIn (goodSites η k) z) ∧
          (∀ z ∈ goodSites η k, (componentIn (goodSites η k) z).Infinite →
            componentIn (goodSites η k) z = Cinf) := by
  exact Exploding.Frozen.renormalization_properties d hd p hp hp1
    Exploding.lssBoundedDegree Exploding.xmf_proved hChem

/-- **Lemma 2.1** (`lemma:local_convexity`): on a background with `2d - 2 ≤ η ≤ 2d - 1`, a finite
path of topplings fills its bounding rectangle: the `A`-frozen parallel toppling odometer
started from `1` on `A` equals `1` on `br A` from time `|br A|` on. -/
theorem Exploding.local_convexity (d : ℕ) (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (m : ℕ) (z : ℕ → Site d) (hpath : ∀ i : ℕ, i < m → (lattice d).Adj (z i) (z (i + 1)))
    (A : Set (Site d)) (hA : A = z '' {i : ℕ | i ≤ m})
    (hfin : (br A).Finite) (t : ℕ) (ht : hfin.toFinset.card ≤ t)
    (x : Site d) (hx : x ∈ br A) :
    fodo A η (Set.indicator A 1) t x = 1 := by
  exact Exploding.Frozen.local_convexity d hd η hlow hhigh m z hpath A hA hfin t ht x hx

/-- **Lemma 3.1** (`lemma:square_lower_bound`): for `d ≥ 2` there is `C > 0` such that for every
background with `2d - 2 ≤ η ≤ 2d - 1`, every `n ≥ 1` and every `m ≥ C n^d` (`m ≥ C n² log (n + 1)`
when `d = 2`), the `m`-wave from the origin is eventually positive on `[-n, n]^d`. Theorem 4.1
of Fey, den Boer and Redig and the radius bound of Fey, Levine and Peres are hypotheses. -/
theorem Exploding.square_lower_bound (d : ℕ) (hd : 2 ≤ d)
    (hFdBR : Exploding.External.FeyDenBoerRedigCubicalCluster)
    (hFLP : Exploding.External.FeyLevinePeresRadius) :
    ∃ C : ℝ, 0 < C ∧
      ∀ η : Site d → ℤ,
        (∀ x, 2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1) →
        ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, 1 ≤ m →
          Nat.ceil (C * (n : ℝ) ^ d *
            (if d = 2 then Real.log ((n : ℝ) + 1) else 1)) ≤ m →
          ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
            ∀ x ∈ cent d n, 0 < wave η m (0 : Site d) t x := by
  exact Exploding.Frozen.square_lower_bound d hd hFdBR hFLP

/-- **The remark after Lemma 3.1** (sharp planar obstruction): on the constant background `2` in
dimension two, the least order `M` whose wave from the origin covers `[-n, n]²` satisfies
`c n² log (n + 1) ≤ M ≤ C n² log (n + 1)`, so the logarithm in Lemma 3.1 cannot be removed.
The same two cited results as in Lemma 3.1 are hypotheses. -/
theorem Exploding.sharp_planar_obstruction
    (hFDR : Exploding.External.FeyDenBoerRedigCubicalCluster)
    (hFLP : Exploding.External.FeyLevinePeresRadius) :
    ∃ c C : Real, 0 < c ∧ 0 < C ∧
      ∀ n : Nat, 1 ≤ n → ∃ M : Nat,
        1 ≤ M ∧
        (∀ x ∈ cent 2 n, ∃ t : Nat,
          0 < wave (fun _ : Site 2 => (2 : Int)) M (0 : Site 2) t x) ∧
        (∀ m : Nat, 1 ≤ m →
          (∀ x ∈ cent 2 n, ∃ t : Nat,
            0 < wave (fun _ : Site 2 => (2 : Int)) m (0 : Site 2) t x) → M ≤ m) ∧
        c * (n : Real)^2 * Real.log ((n : Real) + 1) ≤ (M : Real) ∧
        (M : Real) ≤ C * (n : Real)^2 * Real.log ((n : Real) + 1) := by
  exact Exploding.Frozen.sharp_planar_obstruction hFDR hFLP

/-- **Lemma 3.2** (`lemma:finite_exploding`): almost surely the last wave is well defined,
`M̂_η(0) < ∞`. The chemical-distance bound of Antal and Pisztora is a hypothesis. -/
theorem Exploding.finite_exploding (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∀ᵐ η ∂(toyLaw d p), ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d) := by
  exact Exploding.Frozen.finite_exploding d hd p hp hp1
    Exploding.lssBoundedDegree Exploding.xmf_proved hChem

/-- **Lemma 3.3** (`lemma:last_wave_bound`): at every time, including time zero, the last wave is
at most one more than the penultimate wave, and at most one outside the interior of the
penultimate cluster. -/
theorem Exploding.last_wave_bound (d : ℕ) (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (z : Site d) (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n z) (t : ℕ) (x : Site d) :
    lastWave η z t x ≤ 1 + penultimateWave η z x ∧
      (x ∉ penultimateCluster η z \ innerBoundary (penultimateCluster η z) →
        lastWave η z t x ≤ 1) :=
  Exploding.Frozen.last_wave_bound d hd η hlow hhigh z hlast t x

/-- **Lemma 3.4** (`lemma:approx_subadditivity`): when the last wave is well defined from every
site, the penultimate-cluster arrival times are subadditive. -/
theorem Exploding.approx_subadditivity (d : ℕ) (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (hlast : ∀ y : Site d, ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n y)
    (a b z : Site d) :
    clusterArrival η a z ≤ clusterArrival η a b + clusterArrival η b z := by
  exact Exploding.Frozen.approx_subadditivity d hd η hlow hhigh hlast a b z

/-- **Lemma 3.5** (`lemma:last_penultimate_cluster`): penultimate clusters are
polylogarithmically small. The chemical-distance bound of Antal and Pisztora is a hypothesis. -/
theorem Exploding.last_penultimate_cluster (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
        ∀ y ∈ penultimateCluster η x, ∀ i, ((|y i - x i| : ℤ) : ℝ) ≤ Real.log n ^ γ := by
  exact Exploding.Frozen.last_penultimate_cluster d hd p hp hp1
    Exploding.lssBoundedDegree Exploding.xmf_proved hChem

/-- **Lemma 3.6** (`lemma:penultimate_upper_bound`): the last-wave arrival times obey a linear
upper bound up to a power of the logarithm. The chemical-distance bound of Antal and Pisztora
is a hypothesis. -/
theorem Exploding.penultimate_upper_bound (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ γ C : ℝ, 0 < γ ∧ 0 < C ∧
      ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
        ∃ m : ℕ, lastArrival η (0 : Site d) x = (m : ℕ∞) ∧
          (m : ℝ) ≤ C * (mnorm x : ℝ) + Real.log n ^ γ := by
  exact Exploding.Frozen.penultimate_upper_bound d hd p hp hp1
    Exploding.lssBoundedDegree Exploding.xmf_proved hChem

/-- **Lemma 3.7** (`lemma:last_penultimate_close`): the last-wave and penultimate-cluster
arrival times are polylogarithmically close. The chemical-distance bound of Antal and
Pisztora is a hypothesis. -/
theorem Exploding.last_penultimate_close (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
        lastArrival η (0 : Site d) x ≤ clusterArrival η (0 : Site d) x ∧
          ∃ a b : ℕ, lastArrival η (0 : Site d) x = (a : ℕ∞) ∧
            clusterArrival η (0 : Site d) x = (b : ℕ∞) ∧ (b : ℝ) ≤ (a : ℝ) + Real.log n ^ γ := by
  exact Exploding.Frozen.last_penultimate_close d hd p hp hp1
    Exploding.lssBoundedDegree Exploding.xmf_proved hChem

/-- **Proposition 3.1** (`prop:convergence_of_the_last_wave`): for `0 < p ≤ 1`, the rescaled
last-wave arrival times `T̂_η(0, [n y]) / n` are almost surely finite and converge to a
continuous, convex, one-homogeneous function `N`, uniformly on compact sets. The
chemical-distance bound of Antal and Pisztora is a hypothesis. -/
theorem Exploding.convergence_of_the_last_wave (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p)
    (hp1 : p ≤ 1)
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
  exact Exploding.Frozen.convergence_of_the_last_wave d hd p hp hp1
    Exploding.lssBoundedDegree Exploding.xmf_proved hChem

/-- **Proposition 4.1** (`prop:approximate_subadditive`): almost surely there are constants `C₁`
and `C₂` with `T_η(x) ≤ T̂_η(0, x) + C₁` and `T̂_η(0, x) ≤ T_η(x) + C₂` at every site `x`. The
chemical-distance bound of Antal and Pisztora is a hypothesis. -/
theorem Exploding.approximate_subadditive (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p)
    (hp1 : p ≤ 1)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∀ᵐ η ∂(toyLaw d p), ∃ C1 C2 : ℕ, ∀ x : Site d,
      arrival η x ≤ lastArrival η (0 : Site d) x + (C1 : ℕ∞) ∧
        lastArrival η (0 : Site d) x ≤ arrival η x + (C2 : ℕ∞) := by
  exact Exploding.Frozen.approximate_subadditive d hd p hp hp1
    Exploding.lssBoundedDegree Exploding.xmf_proved hChem

/-- **Proposition 5.1** (`prop:convergence_of_the_generalized_last_wave`): for `d ≥ 2` and a law
`P` on backgrounds with `η_min ≤ η ≤ 2d - 1`, stationary and measurably ergodic for a
sublattice `L` of finite index, and satisfying Hypotheses 1, 3 and 4, the rescaled
last-wave arrival times converge almost surely, uniformly on compact sets, to a continuous,
convex, one-homogeneous function, and `P`-almost every background is explosive. The
chemical-distance bound of Antal and Pisztora is a hypothesis. -/
theorem Exploding.convergence_of_the_generalized_last_wave (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0)
    (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (hstat : StationaryOn d L P) (herg : MeasurableErgodicOn d L P)
    (h1 : FiniteRangeOfDependence d P) (h3 : PathFillingHyp d P)
    (h4 : StronglyBoxCrossingHyp d P)
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
  exact Exploding.Frozen.convergence_of_the_generalized_last_wave d hd ηmin L hL P hP
    hsupp hstat herg h1 h3 h4
    Exploding.xlse_lss_general Exploding.lssBoundedDegree Exploding.xmf_proved hChem

/-- **Theorem 5.1** (convergence of the exploding sandpile): under the hypotheses of
Proposition 5.1 and Hypothesis 5, almost surely the background is explosive, every arrival
time is finite, and `T_η([n y]) / n` converges uniformly on compact sets to a continuous,
convex, one-homogeneous function. The chemical-distance bound of Antal and Pisztora is a
hypothesis. -/
theorem Exploding.generalized_convergence (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0)
    (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (hstat : StationaryOn d L P) (herg : MeasurableErgodicOn d L P)
    (h1 : FiniteRangeOfDependence d P) (h3 : PathFillingHyp d P)
    (h4 : StronglyBoxCrossingHyp d P) (h5 : WaveApproximationHyp d P)
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
  exact Exploding.Frozen.generalized_convergence d hd ηmin L hL P hP hsupp hstat herg
    h1 h3 h4 h5 Exploding.xlse_lss_general Exploding.lssBoundedDegree Exploding.xmf_proved hChem

/-- **Theorem 6.1** (`theorem:counterexample`): for every `d ≥ 2` there is an explosive background,
not bounded below by `2d - 2`, whose arrival times along `e₁` are finite and satisfy
`limsup T(n e₁)/n ≥ 3/2` and `liminf T(n e₁)/n = 1`, and for which no measurable set is a
limit in volume of the rescaled toppled regions. -/
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

/-- **Proposition 7.1** (`prop:explosion_criteria`): for `d ≥ 2`, a law on backgrounds bounded
between `η_min` and `2d - 1` that is stationary and measurably ergodic for a sublattice of
finite index, satisfies Hypotheses 1 and 2, and is recurrent, is explosive. The paper
states it for every `d`; the case `d = 1` is not covered here. -/
theorem Exploding.explosion_criteria (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0) (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (hstat : StationaryOn d L P) (herg : MeasurableErgodicOn d L P)
    (h1 : FiniteRangeOfDependence d P) (h2 : BoxCrossingHyp d P)
    (hrec : RecurrentLaw d P) :
    ExplosiveLaw d P := by
  exact Exploding.Frozen.explosion_criteria d hd ηmin L hL P hP hsupp hstat herg h1 h2 hrec

/-- **Proposition 7.2** (`prop:dimensional_reduction`), with the paper's `d` written `d + 1`: for
every tangential boundary choice `beta : Site d → Bool`, at every time, on the face `F_1(Q_n)`
the constrained odometer in `ℤ^{d+1}` equals the one in `ℤ^d`, and where it vanishes the
configuration in `ℤ^{d+1}` exceeds the one in `ℤ^d` by `2`. -/
theorem Exploding.dimensional_reduction (d n : ℕ) (hd : 1 ≤ d) (beta : Site d → Bool)
    (η : Site (d + 1) → ℤ) (t : ℕ) (y : Site d) (hy : cons 1 y ∈ faceLow (d + 1) n 0) :
    bUpOdo beta n η t (cons 1 y) = bLowOdo beta n η t y ∧
      (bUpOdo beta n η t (cons 1 y) = 0 →
        bUpConf beta n η t (cons 1 y) = bLowConf beta n η t y + 2) := by
  exact Exploding.Frozen.dimensional_reduction d n hd beta η t y hy

/-- **Proposition 7.3** (`prop:recurrence`): the constant background `d` on `ℤ^d` is recurrent. -/
theorem Exploding.recurrence (d : ℕ) (hd : 1 ≤ d) : Recurrent (fun _ : Site d => (d : ℤ)) := by
  exact Exploding.Frozen.recurrence d hd

/-- **Proposition 7.4** (`prop:schonnmann_bootstrap`, Schonmann's bound): for `d ≥ 1` and
`0 < p ≤ 1`, if each site has `2d` chips with probability `p` and `d` otherwise, independently,
there are `c, C > 0` such that `Q_n` is internally spanned with probability at least
`1 - c exp(-C n)`. -/
theorem Exploding.schonmann_bootstrap :
    ∀ d : ℕ, 1 ≤ d → ∀ p : ℝ, 0 < p → p ≤ 1 →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ,
        ENNReal.ofReal (1 - c * Real.exp (-(C * (n : ℝ)))) ≤
          productLaw d (2 * (d : ℤ)) (d : ℤ) p {η | InternallySpanned η n} :=
  Exploding.xsr_schonmann

/-- **Proposition 7.5**: for `d ≥ 2`, a background with independent values of a common law `ν`
with `ν {m ≥ d} = 1` and `ν {2d - 1} > 0` is box-crossing; in dimension one, every law on
backgrounds with `η ≥ 1` is box-crossing. -/
theorem Exploding.box_crossing :
    (∀ (d : ℕ) (_hd : 2 ≤ d) (ν : Measure ℤ) (_hν : IsProbabilityMeasure ν)
      (_hlow : ν {m : ℤ | (d : ℤ) ≤ m} = 1) (_hhit : 0 < ν {(2 * (d : ℤ) - 1)}),
      BoxCrossingHyp d (Measure.infinitePi fun _ : Site d => ν)) ∧
    (∀ (P : Measure (Site 1 → ℤ)) (_hP : IsProbabilityMeasure P)
      (_hsupp : P {η : Site 1 → ℤ | ∀ x, (1 : ℤ) ≤ η x} = 1),
      BoxCrossingHyp 1 P) :=
  ⟨fun d hd ν hν hlow hhit =>
    Exploding.Frozen.box_crossing.1 d hd ν hν hlow hhit Exploding.xsr_schonmann,
   Exploding.Frozen.box_crossing.2⟩
