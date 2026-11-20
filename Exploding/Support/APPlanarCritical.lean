/-
Planar bond percolation from the vendored percolation library.

Through `map_openEdges_bondPercolation`, Kesten's theorem in the form `θ(p) = 0` for `p ≤ 1/2`
(Harris) gives `1/2 ≤ bondCritical 2`, and the Bollobás–Riordan estimate (Ch. 3, Lemma 9: for
`p > 1/2` the `3n × n` rectangle is crossed the long way with probability tending to one) gives
lower bounds for crossing events of translated rectangles, stated with the confined open paths
`xap_Reach` of this repository.
-/
import Exploding.Support.APVendoredBridge
import Exploding.Support.ExtAPDefs

open LatticeProb MeasureTheory ProbabilityTheory Relation
open scoped ENNReal

namespace Exploding

variable {d : ℕ}

/-! ### Confined paths and the vendored connection events -/

theorem xap_reach_of_induce_reachable {ω : Site d × Fin d → Bool} {S : Set (Site d)}
    {a e : Site d} (ha : a ∈ S) (he : e ∈ S)
    (h : ((openBondGraph ω).induce S).Reachable ⟨a, ha⟩ ⟨e, he⟩) : xap_Reach ω S a e := by
  refine ⟨ha, ?_⟩
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  have := ReflTransGen.lift (fun z : S => (z : Site d))
    (r := ((openBondGraph ω).induce S).Adj) (p := xap_RS ω S)
    (fun x y hxy => ⟨x.2, y.2, by simpa [SimpleGraph.induce_adj] using hxy⟩) _ _ h
  simpa using this

/-- An open crossing of the vendored model is an open crossing of the bond configuration. -/
theorem openEdges_mem_openCrossing {ω : Site d × Fin d → Bool} {S A B : Set (Site d)}
    (h : openEdges ω ∈ Percolation.Literature.openCrossing S A B) :
    ∃ a ∈ A, ∃ e ∈ B, xap_Reach ω S a e := by
  obtain ⟨a, ha, e, he, has, hes, hreach⟩ := h
  rw [openGraph_openEdges] at hreach
  exact ⟨a, ha, e, he, xap_reach_of_induce_reachable has hes hreach⟩

/-- Events of the vendored model have the same probability as their preimages. -/
theorem bondPercolation_preimage_openEdges {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {V : Set (Set (Sym2 (Site d)))} (hV : MeasurableSet V) :
    bondPercolation d q (openEdges ⁻¹' V) =
      Percolation.Literature.bondPercolation (Percolation.Literature.LatticeModels.zdGraph d)
        ⟨q, hq0, hq1⟩ V := by
  rw [← map_openEdges_bondPercolation hq0 hq1, Measure.map_apply measurable_openEdges hV]

/-! ### The critical probability of the square lattice -/

theorem preimage_openEdges_percolatesAt :
    openEdges ⁻¹' Percolation.Literature.percolatesAt (0 : Site d) =
      {ω : Site d × Fin d → Bool | {x : Site d | (openBondGraph ω).Reachable 0 x}.Infinite} := by
  ext ω
  simp only [Set.mem_preimage, Percolation.Literature.percolatesAt,
    Percolation.Literature.openCluster, openGraph_openEdges, Set.mem_ofPred_eq]

/-- Below one half there is no bond percolation on `ℤ²` (Harris; the vendored
`Kesten1980_theta_eq_zero`). -/
theorem bondTheta_two_eq_zero {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) : bondTheta 2 q = 0 := by
  have hq1 : q ≤ 1 := by linarith
  have hK := Percolation.Literature.Kesten1980_theta_eq_zero ⟨q, hq0, hq1⟩ hq
  rw [bondTheta, ← preimage_openEdges_percolatesAt,
    bondPercolation_preimage_openEdges hq0 hq1
      (Percolation.Literature.measurableSet_percolatesAt_holds _)]
  rw [Percolation.Literature.theta, measureReal_eq_zero_iff] at hK
  exact hK

/-- The critical probability of bond percolation on `ℤ²` is at least one half. -/
theorem half_le_bondCritical_two : (1 / 2 : ℝ) ≤ bondCritical 2 := by
  refine le_csSup ⟨1, fun q hq => hq.2.1⟩ ⟨by norm_num, by norm_num, bondTheta_two_eq_zero
    (by norm_num) le_rfl⟩

/-! ### Crossings of rectangles -/

/-- The probability that a translate of the rectangle `[0, M] × [0, K]` has an open left-right
crossing is at least the vendored crossing probability. -/
theorem crossingProb_le_lr {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (v : Site 2) (M K : ℕ) :
    ENNReal.ofReal (Percolation.Literature.crossingProb ⟨q, hq0, hq1⟩ M K) ≤
      bondPercolation 2 q {ω | ∃ a ∈ (· + v) '' (Percolation.Literature.leftSide M K : Set (Site 2)),
        ∃ e ∈ (· + v) '' (Percolation.Literature.rightSide M K : Set (Site 2)),
        xap_Reach ω ((· + v) '' (Percolation.Literature.rectangle M K : Set (Site 2))) a e} := by
  set W := Percolation.Literature.openCrossing
    ((· + v) '' (Percolation.Literature.rectangle M K : Set (Site 2)))
    ((· + v) '' (Percolation.Literature.leftSide M K : Set (Site 2)))
    ((· + v) '' (Percolation.Literature.rightSide M K : Set (Site 2))) with hW
  have hWm : MeasurableSet W := Percolation.Literature.measurableSet_openCrossing_image _ _ _ _
  have hcross : Percolation.Literature.crossingProb ⟨q, hq0, hq1⟩ M K =
      (Percolation.Literature.bondPercolation (Percolation.Literature.LatticeModels.zdGraph 2)
        ⟨q, hq0, hq1⟩).real W := by
    rw [hW, Percolation.Literature.real_openCrossing_shift]
    rfl
  rw [hcross, ofReal_measureReal (measure_ne_top _ _), ← bondPercolation_preimage_openEdges hq0 hq1 hWm]
  exact measure_mono fun ω hω => openEdges_mem_openCrossing hω

/-- The probability that a translate of the rectangle `[0, K] × [0, M]` has an open bottom-top
crossing is at least the vendored crossing probability of `[0, M] × [0, K]`. -/
theorem crossingProb_le_tb {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (v : Site 2) (M K : ℕ) :
    ENNReal.ofReal (Percolation.Literature.crossingProb ⟨q, hq0, hq1⟩ M K) ≤
      bondPercolation 2 q {ω | ∃ a ∈ (· + v) '' (Percolation.Literature.bottomSide K M : Set (Site 2)),
        ∃ e ∈ (· + v) '' (Percolation.Literature.topSide K M : Set (Site 2)),
        xap_Reach ω ((· + v) '' (Percolation.Literature.rectangle K M : Set (Site 2))) a e} := by
  set W := Percolation.Literature.openCrossing
    ((· + v) '' (Percolation.Literature.rectangle K M : Set (Site 2)))
    ((· + v) '' (Percolation.Literature.bottomSide K M : Set (Site 2)))
    ((· + v) '' (Percolation.Literature.topSide K M : Set (Site 2))) with hW
  have hWm : MeasurableSet W := Percolation.Literature.measurableSet_openCrossing_image _ _ _ _
  have hcross : Percolation.Literature.crossingProb ⟨q, hq0, hq1⟩ M K =
      (Percolation.Literature.bondPercolation (Percolation.Literature.LatticeModels.zdGraph 2)
        ⟨q, hq0, hq1⟩).real W := by
    rw [hW, Percolation.Literature.real_openCrossing_shift, ← Percolation.Literature.real_tbCrossing]
    rfl
  rw [hcross, ofReal_measureReal (measure_ne_top _ _), ← bondPercolation_preimage_openEdges hq0 hq1 hWm]
  exact measure_mono fun ω hω => openEdges_mem_openCrossing hω

/-- The probability that a translate of the rectangle `[0, M] × [0, K]` has no open left-right
crossing is at most one minus the vendored crossing probability. -/
theorem bondPercolation_not_lr_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (v : Site 2) (M K : ℕ) :
    bondPercolation 2 q {ω | ¬ ∃ a ∈ (· + v) '' (Percolation.Literature.leftSide M K : Set (Site 2)),
        ∃ e ∈ (· + v) '' (Percolation.Literature.rightSide M K : Set (Site 2)),
        xap_Reach ω ((· + v) '' (Percolation.Literature.rectangle M K : Set (Site 2))) a e} ≤
      1 - ENNReal.ofReal (Percolation.Literature.crossingProb ⟨q, hq0, hq1⟩ M K) := by
  set W := Percolation.Literature.openCrossing
    ((· + v) '' (Percolation.Literature.rectangle M K : Set (Site 2)))
    ((· + v) '' (Percolation.Literature.leftSide M K : Set (Site 2)))
    ((· + v) '' (Percolation.Literature.rightSide M K : Set (Site 2))) with hW
  have hWm : MeasurableSet W := Percolation.Literature.measurableSet_openCrossing_image _ _ _ _
  have hcross : Percolation.Literature.crossingProb ⟨q, hq0, hq1⟩ M K =
      (Percolation.Literature.bondPercolation (Percolation.Literature.LatticeModels.zdGraph 2)
        ⟨q, hq0, hq1⟩).real W := by
    rw [hW, Percolation.Literature.real_openCrossing_shift]
    rfl
  calc
    _ ≤ bondPercolation 2 q (openEdges ⁻¹' Wᶜ) := by
      refine measure_mono fun ω hω hWω => ?_
      exact absurd (openEdges_mem_openCrossing hWω) hω
    _ = 1 - ENNReal.ofReal (Percolation.Literature.crossingProb ⟨q, hq0, hq1⟩ M K) := by
      rw [bondPercolation_preimage_openEdges hq0 hq1 hWm.compl, prob_compl_eq_one_sub hWm, hcross,
        ofReal_measureReal (measure_ne_top _ _)]

/-- The probability that a translate of the rectangle `[0, K] × [0, M]` has no open bottom-top
crossing is at most one minus the vendored crossing probability of `[0, M] × [0, K]`. -/
theorem bondPercolation_not_tb_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (v : Site 2) (M K : ℕ) :
    bondPercolation 2 q {ω | ¬ ∃ a ∈ (· + v) '' (Percolation.Literature.bottomSide K M : Set (Site 2)),
        ∃ e ∈ (· + v) '' (Percolation.Literature.topSide K M : Set (Site 2)),
        xap_Reach ω ((· + v) '' (Percolation.Literature.rectangle K M : Set (Site 2))) a e} ≤
      1 - ENNReal.ofReal (Percolation.Literature.crossingProb ⟨q, hq0, hq1⟩ M K) := by
  set W := Percolation.Literature.openCrossing
    ((· + v) '' (Percolation.Literature.rectangle K M : Set (Site 2)))
    ((· + v) '' (Percolation.Literature.bottomSide K M : Set (Site 2)))
    ((· + v) '' (Percolation.Literature.topSide K M : Set (Site 2))) with hW
  have hWm : MeasurableSet W := Percolation.Literature.measurableSet_openCrossing_image _ _ _ _
  have hcross : Percolation.Literature.crossingProb ⟨q, hq0, hq1⟩ M K =
      (Percolation.Literature.bondPercolation (Percolation.Literature.LatticeModels.zdGraph 2)
        ⟨q, hq0, hq1⟩).real W := by
    rw [hW, Percolation.Literature.real_openCrossing_shift, ← Percolation.Literature.real_tbCrossing]
    rfl
  calc
    _ ≤ bondPercolation 2 q (openEdges ⁻¹' Wᶜ) := by
      refine measure_mono fun ω hω hWω => ?_
      exact absurd (openEdges_mem_openCrossing hWω) hω
    _ = 1 - ENNReal.ofReal (Percolation.Literature.crossingProb ⟨q, hq0, hq1⟩ M K) := by
      rw [bondPercolation_preimage_openEdges hq0 hq1 hWm.compl, prob_compl_eq_one_sub hWm, hcross,
        ofReal_measureReal (measure_ne_top _ _)]

end Exploding
