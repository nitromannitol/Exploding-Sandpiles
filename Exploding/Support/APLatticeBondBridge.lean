/-
Bond percolation of this repository and the bond model of Lattice-Probability in which the
Percolation-Rigidity formalization states its results.

The bonds `(x, i)` of this repository index the edges `{x, x + e_i}`, which are exactly the bonds
of `Exploding.LatticeBond.Bond d`.  Reindexing a configuration along this bijection carries
`bondPercolation d q` to `latticeBondLaw d q` and the graph of open bonds to `openGraph`, so the
percolation probabilities agree, and every density above `bondCritical d` lies above
`criticalProbability d`.  Connection probabilities inside a set transfer through `openIn`.
-/
import Exploding.Support.LatticeBond.Critical
import Exploding.Rigidity.External.WellConnected
import Exploding.Support.APVendoredBridge
import Exploding.Support.ExtAPProof14

open LatticeProb MeasureTheory ProbabilityTheory Relation
open scoped ENNReal

namespace Exploding

variable {d : ℕ}

/-! ### The bijection between the two kinds of bonds -/

theorem l1_unit (x : Site d) (i : Fin d) : (∑ j, |x j - (x + unit i) j|) = 1 := by
  classical
  have h : ∀ j, |x j - (x + unit i) j| = if j = i then 1 else 0 := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp [unit]
    · simp [unit, hj]
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The bond of the Lattice-Probability model carried by the index `(x, i)`. -/
def toLatticeBond (a : Site d × Fin d) : LatticeBond.Bond d :=
  ⟨bondEdge a, a.1, a.1 + unit a.2, rfl, l1_unit a.1 a.2⟩

theorem toLatticeBond_bijective : Function.Bijective (toLatticeBond (d := d)) := by
  constructor
  · intro a b h
    exact bondEdge_injective (congrArg Subtype.val h)
  · rintro ⟨e, x, y, rfl, hxy⟩
    have hadj : (lattice d).Adj x y := LatticeBond.lattice_adj_iff_l1Dist.mpr hxy
    obtain ⟨i, hi | hi⟩ := hadj
    · refine ⟨(x, i), Subtype.ext ?_⟩
      show s(x, x + unit i) = s(x, y)
      rw [hi]
    · refine ⟨(y, i), Subtype.ext ?_⟩
      show s(y, y + unit i) = s(x, y)
      rw [hi, Sym2.eq_swap]

/-- The bijection between the bond indices of this repository and the Lattice-Probability bonds. -/
noncomputable def latticeBondEquiv (d : ℕ) : Site d × Fin d ≃ LatticeBond.Bond d :=
  Equiv.ofBijective toLatticeBond toLatticeBond_bijective

/-- A configuration of this repository as a Lattice-Probability configuration. -/
noncomputable def toLatticeConfig (ω : Site d × Fin d → Bool) : LatticeBond.Configuration d :=
  fun e => ω ((latticeBondEquiv d).symm e)

theorem toLatticeConfig_apply (ω : Site d × Fin d → Bool) (a : Site d × Fin d) :
    toLatticeConfig ω (toLatticeBond a) = ω a := by
  rw [toLatticeConfig, show toLatticeBond a = latticeBondEquiv d a from rfl,
    Equiv.symm_apply_apply]

theorem measurable_toLatticeConfig : Measurable (toLatticeConfig (d := d)) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-! ### Laws and graphs -/

theorem bitLaw_eq_bernoulliMeasure {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    bitLaw q = bernoulliMeasure true false (⟨q, hq0, hq1⟩ : unitInterval) := by
  have h1 : ((unitInterval.toNNReal ⟨q, hq0, hq1⟩ : NNReal) : ℝ≥0∞) = ENNReal.ofReal q := by
    rw [ENNReal.ofReal, Real.toNNReal_of_nonneg hq0]
    rfl
  have h2 : ((unitInterval.toNNReal (unitInterval.symm ⟨q, hq0, hq1⟩) : NNReal) : ℝ≥0∞) =
      ENNReal.ofReal (1 - q) := by
    rw [ENNReal.ofReal, Real.toNNReal_of_nonneg (by linarith)]
    rfl
  rw [bernoulliMeasure_def, bitLaw]
  ext s _
  simp only [Measure.add_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, h1, h2]

/-- **The law of the reindexed configuration is the Lattice-Probability bond law.** -/
theorem map_toLatticeConfig_bondPercolation {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (bondPercolation d q).map toLatticeConfig =
      LatticeBond.latticeBondLaw d ⟨q, hq0, hq1⟩ := by
  have : IsProbabilityMeasure (bitLaw q) := rn_bitLaw_isProb hq0 hq1
  have h := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : Site d × Fin d => bitLaw q)
    (latticeBondEquiv d).symm.injective
  rw [bondPercolation, show (toLatticeConfig : (Site d × Fin d → Bool) → _) =
    fun ω e => ω ((latticeBondEquiv d).symm e) from rfl, h, LatticeBond.latticeBondLaw,
    bitLaw_eq_bernoulliMeasure hq0 hq1]

theorem toLatticeConfig_bondOfAdjacent {ω : Site d × Fin d → Bool} {x : Site d} {i : Fin d}
    (h : (LatticeBond.nearestNeighborGraph d).Adj x (x + unit i)) :
    toLatticeConfig ω (LatticeBond.bondOfAdjacent h) = ω (x, i) := by
  rw [show LatticeBond.bondOfAdjacent h = toLatticeBond (x, i) from Subtype.ext rfl,
    toLatticeConfig_apply]

/-- The open graph of the reindexed configuration is the graph of open bonds. -/
theorem openGraph_toLatticeConfig (ω : Site d × Fin d → Bool) :
    LatticeBond.openGraph (toLatticeConfig ω) = openBondGraph ω := by
  ext x y
  rw [LatticeBond.openGraph_adj_iff, openBondGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨h, ho⟩
    refine ⟨h.ne, ?_⟩
    obtain ⟨i, hi | hi⟩ := id h
    · subst hi
      exact Or.inl ⟨i, rfl, by rwa [toLatticeConfig_bondOfAdjacent] at ho⟩
    · subst hi
      refine Or.inr ⟨i, rfl, ?_⟩
      rw [show LatticeBond.bondOfAdjacent h = LatticeBond.bondOfAdjacent h.symm.symm from rfl,
        LatticeBond.bondOfAdjacent_symm h.symm, toLatticeConfig_bondOfAdjacent h.symm] at ho
      exact ho
  · rintro ⟨hne, ⟨i, rfl, hi⟩ | ⟨i, rfl, hi⟩⟩
    · have h' : (LatticeBond.nearestNeighborGraph d).Adj x (x + unit i) := by
        exact ⟨i, Or.inl rfl⟩
      exact ⟨h', by rw [toLatticeConfig_bondOfAdjacent h']; exact hi⟩
    · have h' : (LatticeBond.nearestNeighborGraph d).Adj y (y + unit i) := by
        exact ⟨i, Or.inl rfl⟩
      refine ⟨h'.symm, ?_⟩
      rw [LatticeBond.bondOfAdjacent_symm h', toLatticeConfig_bondOfAdjacent h']
      exact hi

/-! ### Percolation probability and critical probability -/

theorem preimage_toLatticeConfig_infiniteComponentEvent :
    toLatticeConfig ⁻¹' LatticeBond.infiniteComponentEvent (0 : Site d) =
      {ω : Site d × Fin d → Bool | {x : Site d | (openBondGraph ω).Reachable 0 x}.Infinite} := by
  ext ω
  simp only [Set.mem_preimage, LatticeBond.infiniteComponentEvent, Set.mem_ofPred_eq]
  rw [openGraph_toLatticeConfig]
  have : ((openBondGraph ω).connectedComponentMk 0).supp =
      {x : Site d | (openBondGraph ω).Reachable 0 x} := by
    ext x
    simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq,
      Set.mem_ofPred_eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  rw [this]

/-- The percolation probabilities of the two models agree. -/
theorem theta_eq_bondTheta {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    LatticeBond.theta d ⟨q, hq0, hq1⟩ = (bondTheta d q).toReal := by
  rw [LatticeBond.theta, measureReal_def, ← map_toLatticeConfig_bondPercolation hq0 hq1,
    Measure.map_apply measurable_toLatticeConfig
      (LatticeBond.measurableSet_infiniteComponentEvent 0),
    preimage_toLatticeConfig_infiniteComponentEvent, bondTheta]

/-- Every density above `bondCritical d` lies above the Lattice-Probability critical
probability. -/
theorem criticalProbability_lt_of_bondCritical_lt [NeZero d] {q : ℝ} (hq : bondCritical d < q)
    (hq1 : q ≤ 1) : LatticeBond.criticalProbability d < q := by
  set q' := (bondCritical d + q) / 2 with hq'
  have h1 : bondCritical d < q' := by rw [hq']; linarith
  have h2 : q' < q := by rw [hq']; linarith
  have hq'0 : 0 ≤ q' := (xap14_bondCritical_nonneg d).trans h1.le
  have hq'1 : q' ≤ 1 := h2.le.trans hq1
  have hθ := xap14_theta_pos_of_gt_bondCritical h1 hq'1
  have hpos : 0 < LatticeBond.theta d ⟨q', hq'0, hq'1⟩ := by
    rw [theta_eq_bondTheta hq'0 hq'1]
    have : bondTheta d q' ≠ ⊤ := by
      have : IsProbabilityMeasure (bondPercolation d q') := rn_infinitePi_isProb hq'0 hq'1
      exact measure_ne_top _ _
    exact ENNReal.toReal_pos hθ this
  exact (LatticeBond.criticalProbability_le _ hpos).trans_lt h2

/-! ### Connections inside a set -/

/-- Existence of an open walk of exactly `n` edges inside `S`. -/
def openInWalk (ω : LatticeBond.Configuration d) (S : Set (Site d)) :
    ℕ → Site d → Site d → Prop
  | 0, x, y => x = y
  | n + 1, x, y => ∃ z, (Rigidity.External.openIn ω S).Adj x z ∧ openInWalk ω S n z y

theorem reachable_openIn_iff (ω : LatticeBond.Configuration d) (S : Set (Site d))
    (x y : Site d) : (Rigidity.External.openIn ω S).Reachable x y ↔ ∃ n, openInWalk ω S n x y := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => exact ⟨0, rfl⟩
    | @cons u v w h p ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, v, h, hn⟩
  · rintro ⟨n, hn⟩
    induction n generalizing x with
    | zero =>
      change x = y at hn
      subst y
      exact SimpleGraph.Reachable.refl _
    | succ n ih =>
      obtain ⟨z, h, hz⟩ := hn
      exact h.reachable.trans (ih z hz)

theorem measurableSet_openIn_reachable (S : Set (Site d)) (x y : Site d) :
    MeasurableSet {ω : LatticeBond.Configuration d | (Rigidity.External.openIn ω S).Reachable x y} := by
  have hwalk : ∀ n x, MeasurableSet {ω : LatticeBond.Configuration d | openInWalk ω S n x y} := by
    intro n
    induction n with
    | zero => exact fun x => MeasurableSet.const _
    | succ n ih =>
      intro x
      have : {ω : LatticeBond.Configuration d | openInWalk ω S (n + 1) x y} =
          ⋃ z, ({ω | (LatticeBond.openGraph ω).Adj x z} ∩ {_ω | x ∈ S ∧ z ∈ S}) ∩
            {ω | openInWalk ω S n z y} := by
        ext ω
        simp only [openInWalk, Rigidity.External.openIn, Set.mem_ofPred_eq, Set.mem_iUnion,
          Set.mem_inter_iff]
      rw [this]
      exact MeasurableSet.iUnion fun z =>
        ((LatticeBond.measurableSet_openGraph_adj x z).inter (MeasurableSet.const _)).inter (ih z)
  have : {ω : LatticeBond.Configuration d | (Rigidity.External.openIn ω S).Reachable x y} =
      ⋃ n, {ω | openInWalk ω S n x y} := by
    ext ω
    simp only [reachable_openIn_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [this]
  exact MeasurableSet.iUnion fun n => hwalk n x

theorem openIn_toLatticeConfig_reachable {ω : Site d × Fin d → Bool} {S : Set (Site d)}
    {x y : Site d} (hx : x ∈ S)
    (h : (Rigidity.External.openIn (toLatticeConfig ω) S).Reachable x y) : xap_Reach ω S x y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  refine ⟨hx, ReflTransGen.mono (fun a b hab => ?_) _ _ h⟩
  obtain ⟨hab, ha, hb⟩ := hab
  rw [openGraph_toLatticeConfig] at hab
  exact ⟨ha, hb, hab⟩

/-- A connection probability inside a set in the Lattice-Probability model bounds the
corresponding confined connection probability of this repository. -/
theorem latticeBondLaw_openIn_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {S : Set (Site d)}
    {x y : Site d} (hx : x ∈ S) :
    (LatticeBond.latticeBondLaw d ⟨q, hq0, hq1⟩).real
        {ω | (Rigidity.External.openIn ω S).Reachable x y} ≤
      (bondPercolation d q).real {ω | xap_Reach ω S x y} := by
  have : IsProbabilityMeasure (bondPercolation d q) := rn_infinitePi_isProb hq0 hq1
  rw [← map_toLatticeConfig_bondPercolation hq0 hq1]
  refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
  rw [Measure.map_apply measurable_toLatticeConfig (measurableSet_openIn_reachable S x y)]
  exact measure_mono fun ω hω => openIn_toLatticeConfig_reachable hx hω

end Exploding
