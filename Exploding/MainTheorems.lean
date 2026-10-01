import Exploding.Frozen.SquareLowerBound
import Exploding.Frozen.LastWaveBound
import Exploding.Frozen.DimensionalReduction
import Exploding.Frozen.ApproxSubadditivity
import Exploding.Frozen.Recurrence
import Exploding.Frozen.CrossingTime
import Exploding.Frozen.LocalConvexity
import Exploding.Frozen.Renormalization
import Exploding.Frozen.FiniteExploding
import Exploding.Frozen.PenultimateCluster
import Exploding.Frozen.PenultimateUpperBound
import Exploding.Frozen.PenultimateClose
import Exploding.Frozen.Explosive
import Exploding.Frozen.ExplosionCriteria
import Exploding.Frozen.BoxCrossing

/-!
# Main results

The formalization of *A shape theorem for exploding sandpiles* (Ahmed Bou-Rabee) is a work
in progress.  The paper's main results are registered as frozen statements, whose states in
`ledger/manifest.yaml` are:

* `Exploding.Frozen.limit_shape`: Theorem 1.2, the toppled region of the exploding
  sandpile with the Bernoulli background `(1.2)`, rescaled by time, converges in measure to
  a convex domain.  Conditional: its proof is complete, resting on Theorem 1.3.
* `Exploding.Frozen.convergence_of_time_constant`: Theorem 1.3, the rescaled arrival times
  converge locally uniformly to a continuous, convex, one-homogeneous function.
  Conditional: its proof is written, from Propositions 3.1 and 4.1, both still open.
* `Exploding.Frozen.explosive`: Theorem 1.4, a product background with at least `d` chips
  at every site and a positive density of sites with `2d - 1` chips explodes almost surely.
  Proved.
* `Exploding.Frozen.generalized_convergence`: Theorem 5.1, convergence of the exploding
  sandpile under the hypotheses of Section 5.  Conditional: its proof is written, from
  Proposition 5.1 and the wave-approximation hypothesis, and Proposition 5.1 is still open.
* `Exploding.Frozen.counterexample`: Theorem 6.1, explosive backgrounds without a limit
  shape.  Open.

Only Theorem 1.4 is restated below; the four open statements are not, since this file
states only what is proved.  Each of them takes the results the paper cites for it, from
Theorem 1.1 (Fey, Levine and Peres) to the percolation results behind Proposition 2.2, as
explicit hypotheses stated in `Exploding/External/`; see `ASSUMPTIONS.md`.

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

All fifteen reduce to the standard axioms (`propext`, `Classical.choice`, `Quot.sound`);
see `Exploding/Meta/AxiomsAudit.lean`.
-/

open Exploding LatticeProb MeasureTheory

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

/-- **Proposition 2.1** (`prop:crossing_time`): for every `δ > 0` there is a side length
`k` so that with probability at least `1 - δ` every line across the box `Q_k` carries a
`(2d-1)`-chip catalyst, hence every crossing time is at most `k^d`.  The certified
statement is `Exploding.Frozen.crossing_time`, restated unchanged. -/
theorem Exploding.crossing_time (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ k : ℕ, 1 ≤ k ∧ ENNReal.ofReal (1 - δ) ≤ toyLaw d p {η | GoodCube η k} := by
  exact Exploding.Frozen.crossing_time d hd p hp hp1 δ hδ

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

/-- **Lemma 3.2** (`lemma:finite_exploding`): the last wave is well defined,
`M̂_η(0) < ∞`.  The certified statement is `Exploding.Frozen.finite_exploding`, restated
unchanged. -/
theorem Exploding.finite_exploding (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∀ᵐ η ∂(toyLaw d p), ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d) := by
  exact Exploding.Frozen.finite_exploding d hd p hp hp1 hLSSB hHole hChem

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

/-- **Theorem 1.4** (`theorem:explosive`): a product background with at least `d` chips at
every site and a positive density of sites with `2d - 1` chips explodes almost surely.  The
certified statement is `Exploding.Frozen.explosive`, restated unchanged. -/
theorem Exploding.explosive (d : ℕ) (hd : 2 ≤ d) (ν : Measure ℤ) (hν : IsProbabilityMeasure ν)
    (hlow : ν {m : ℤ | (d : ℤ) ≤ m} = 1) (hhit : 0 < ν {(2 * (d : ℤ) - 1)})
    (hSch : Exploding.External.SchonmannBootstrap) :
    ∀ᵐ β ∂(Measure.infinitePi fun _ : Site d => ν), Explosive β := by
  exact Exploding.Frozen.explosive d hd ν hν hlow hhit hSch

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

/-- **Proposition 7.5** (`exploding.tex:1986-1988`): a product background with at least `d`
chips at every site and a positive density of `(2d-1)`-sites is box-crossing.  The certified
statement is `Exploding.Frozen.box_crossing`, restated unchanged. -/
theorem Exploding.box_crossing (d : ℕ) (hd : 2 ≤ d) (ν : Measure ℤ) (hν : IsProbabilityMeasure ν)
    (hlow : ν {m : ℤ | (d : ℤ) ≤ m} = 1) (hhit : 0 < ν {(2 * (d : ℤ) - 1)})
    (hSch : Exploding.External.SchonmannBootstrap) :
    BoxCrossingHyp d (Measure.infinitePi fun _ : Site d => ν) := by
  exact Exploding.Frozen.box_crossing d hd ν hν hlow hhit hSch
