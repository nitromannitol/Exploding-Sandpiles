/-
The Antal–Pisztora chemical-distance bound for bond percolation on `ℤ²` at every density above
`bondCritical 2`.

The four rectangles of the frame of a block are translates of the `3N × N` rectangle and of its
transpose, so a frame is bad with probability at most four times the probability that the
`3N × N` rectangle has no open long-way crossing (`frameGood_bad_prob_le`).  Above
`bondCritical 2 ≥ 1/2` this tends to zero by the Bollobás–Riordan estimate, and the
renormalization step `chemicalDistance_of_blockScheme` applied to the frame scheme gives the
bound (`antalPisztora_dim_two`).
-/
import Exploding.Support.APPlanarScheme

open LatticeProb LQGMetric MeasureTheory Filter Topology
open scoped ENNReal

namespace Exploding

/-- A crossing of a set of sites inside a rectangle of the frame, between its two short sides,
is a long-way crossing of that rectangle. -/
theorem exists_frameCross_of_rect {m : ℕ} {ω : Site 2 × Fin 2 → Bool} {b : Site 2}
    {dir : PercDir} {R A B : Set (Site 2)} (hR : R ⊆ frameRect m b dir)
    (hA : ∀ a ∈ A, annLong dir (framePlane m b a) = -(3 * m + 1))
    (hB : ∀ e ∈ B, annLong dir (framePlane m b e) = 3 * m + 1)
    (h : ∃ a ∈ A, ∃ e ∈ B, xap_Reach ω R a e) : ∃ a e, FrameCross m ω b dir a e := by
  obtain ⟨a, ha, e, he, hae⟩ := h
  exact ⟨a, e, hA a ha, hB e he, xap_reach_mono hR hae⟩

/-- **A frame is bad with small probability.**  The frame of a block at scale `2m + 1` is bad
with probability at most four times the probability that the `3N × N` rectangle, `N = 2m + 1`,
has no open left-right crossing. -/
theorem frameGood_bad_prob_le (m : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (b : Site 2) :
    bondPercolation 2 q {ω | ¬ frameGood m ω b} ≤
      4 * (1 - ENNReal.ofReal (Percolation.Literature.crossingProb ⟨q, hq0, hq1⟩
        (3 * (2 * m + 1) - 1) (2 * m + 1 - 1))) := by
  classical
  set M : ℕ := 3 * (2 * m + 1) - 1 with hM
  set K : ℕ := 2 * m + 1 - 1 with hK
  set c0 : ℤ := (2 * m + 1) * b 0 + m with hc0
  set c1 : ℤ := (2 * m + 1) * b 1 + m with hc1
  set vT : Site 2 := ![c0 - (3 * m + 1), c1 + (m + 1)]
  set vB : Site 2 := ![c0 - (3 * m + 1), c1 - (3 * m + 1)]
  set vR : Site 2 := ![c0 + (m + 1), c1 - (3 * m + 1)]
  set p := Percolation.Literature.crossingProb ⟨q, hq0, hq1⟩ M K
  have hrect : ∀ (v : Site 2) (M' K' : ℕ) (z : Site 2),
      z ∈ (· + v) '' (Percolation.Literature.rectangle M' K' : Set (Site 2)) →
      0 ≤ z 0 - v 0 ∧ z 0 - v 0 ≤ M' ∧ 0 ≤ z 1 - v 1 ∧ z 1 - v 1 ≤ K' := by
    rintro v M' K' _ ⟨w, hw, rfl⟩
    rw [Finset.mem_coe, Percolation.Literature.mem_rectangle_iff] at hw
    simp only [Pi.add_apply, add_sub_cancel_right]
    exact hw
  have hside : ∀ (v : Site 2) (M' K' : ℕ) (P : Site 2 → Prop) [DecidablePred P] (z : Site 2),
      z ∈ (· + v) '' (((Percolation.Literature.rectangle M' K').filter P : Finset (Site 2)) :
        Set (Site 2)) → P (z - v) := by
    rintro v M' K' P _ _ ⟨w, hw, rfl⟩
    rw [Finset.mem_coe, Finset.mem_filter] at hw
    simpa only [add_sub_cancel_right] using hw.2
  have hT : {ω | ¬ ∃ a e, FrameCross m ω b .T a e} ⊆
      {ω | ¬ ∃ a ∈ (· + vT) '' (Percolation.Literature.leftSide M K : Set (Site 2)),
        ∃ e ∈ (· + vT) '' (Percolation.Literature.rightSide M K : Set (Site 2)),
        xap_Reach ω ((· + vT) '' (Percolation.Literature.rectangle M K : Set (Site 2))) a e} := by
    intro ω hω h
    refine hω (exists_frameCross_of_rect ?_ ?_ ?_ h)
    · intro z hz
      have := hrect vT M K z hz
      simp only [vT, Matrix.cons_val_zero, Matrix.cons_val_one] at this
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [framePlane, annDir] <;> omega
    · intro a ha
      have := hside vT M K _ a ha
      simp only [vT, Pi.sub_apply, Matrix.cons_val_zero] at this
      simp only [framePlane, annLong]
      omega
    · intro e he
      have := hside vT M K _ e he
      simp only [vT, Pi.sub_apply, Matrix.cons_val_zero] at this
      simp only [framePlane, annLong]
      omega
  have hB : {ω | ¬ ∃ a e, FrameCross m ω b .B a e} ⊆
      {ω | ¬ ∃ a ∈ (· + vB) '' (Percolation.Literature.leftSide M K : Set (Site 2)),
        ∃ e ∈ (· + vB) '' (Percolation.Literature.rightSide M K : Set (Site 2)),
        xap_Reach ω ((· + vB) '' (Percolation.Literature.rectangle M K : Set (Site 2))) a e} := by
    intro ω hω h
    refine hω (exists_frameCross_of_rect ?_ ?_ ?_ h)
    · intro z hz
      have := hrect vB M K z hz
      simp only [vB, Matrix.cons_val_zero, Matrix.cons_val_one] at this
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [framePlane, annDir] <;> omega
    · intro a ha
      have := hside vB M K _ a ha
      simp only [vB, Pi.sub_apply, Matrix.cons_val_zero] at this
      simp only [framePlane, annLong]
      omega
    · intro e he
      have := hside vB M K _ e he
      simp only [vB, Pi.sub_apply, Matrix.cons_val_zero] at this
      simp only [framePlane, annLong]
      omega
  have hL : {ω | ¬ ∃ a e, FrameCross m ω b .L a e} ⊆
      {ω | ¬ ∃ a ∈ (· + vB) '' (Percolation.Literature.bottomSide K M : Set (Site 2)),
        ∃ e ∈ (· + vB) '' (Percolation.Literature.topSide K M : Set (Site 2)),
        xap_Reach ω ((· + vB) '' (Percolation.Literature.rectangle K M : Set (Site 2))) a e} := by
    intro ω hω h
    refine hω (exists_frameCross_of_rect ?_ ?_ ?_ h)
    · intro z hz
      have := hrect vB K M z hz
      simp only [vB, Matrix.cons_val_zero, Matrix.cons_val_one] at this
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [framePlane, annDir] <;> omega
    · intro a ha
      have := hside vB K M _ a ha
      simp only [vB, Pi.sub_apply, Matrix.cons_val_one, Matrix.cons_val_zero] at this
      simp only [framePlane, annLong]
      omega
    · intro e he
      have := hside vB K M _ e he
      simp only [vB, Pi.sub_apply, Matrix.cons_val_one, Matrix.cons_val_zero] at this
      simp only [framePlane, annLong]
      omega
  have hR : {ω | ¬ ∃ a e, FrameCross m ω b .R a e} ⊆
      {ω | ¬ ∃ a ∈ (· + vR) '' (Percolation.Literature.bottomSide K M : Set (Site 2)),
        ∃ e ∈ (· + vR) '' (Percolation.Literature.topSide K M : Set (Site 2)),
        xap_Reach ω ((· + vR) '' (Percolation.Literature.rectangle K M : Set (Site 2))) a e} := by
    intro ω hω h
    refine hω (exists_frameCross_of_rect ?_ ?_ ?_ h)
    · intro z hz
      have := hrect vR K M z hz
      simp only [vR, Matrix.cons_val_zero, Matrix.cons_val_one] at this
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [framePlane, annDir] <;> omega
    · intro a ha
      have := hside vR K M _ a ha
      simp only [vR, Pi.sub_apply, Matrix.cons_val_one, Matrix.cons_val_zero] at this
      simp only [framePlane, annLong]
      omega
    · intro e he
      have := hside vR K M _ e he
      simp only [vR, Pi.sub_apply, Matrix.cons_val_one, Matrix.cons_val_zero] at this
      simp only [framePlane, annLong]
      omega
  have hsub : {ω | ¬ frameGood m ω b} ⊆
      ((({ω | ¬ ∃ a e, FrameCross m ω b .T a e} ∪ {ω | ¬ ∃ a e, FrameCross m ω b .B a e}) ∪
        {ω | ¬ ∃ a e, FrameCross m ω b .L a e}) ∪ {ω | ¬ ∃ a e, FrameCross m ω b .R a e}) := by
    intro ω hω
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨⟨hTω, hBω⟩, hLω⟩, hRω⟩ := hcon
    exact hω fun dir => by cases dir <;> assumption
  calc
    bondPercolation 2 q {ω | ¬ frameGood m ω b}
        ≤ bondPercolation 2 q {ω | ¬ ∃ a e, FrameCross m ω b .T a e} +
          bondPercolation 2 q {ω | ¬ ∃ a e, FrameCross m ω b .B a e} +
          bondPercolation 2 q {ω | ¬ ∃ a e, FrameCross m ω b .L a e} +
          bondPercolation 2 q {ω | ¬ ∃ a e, FrameCross m ω b .R a e} := by
      refine (measure_mono hsub).trans ?_
      refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
      refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
      exact measure_union_le _ _
    _ ≤ (1 - ENNReal.ofReal p) + (1 - ENNReal.ofReal p) + (1 - ENNReal.ofReal p) +
          (1 - ENNReal.ofReal p) := by
      gcongr
      · exact (measure_mono hT).trans (bondPercolation_not_lr_le hq0 hq1 vT M K)
      · exact (measure_mono hB).trans (bondPercolation_not_lr_le hq0 hq1 vB M K)
      · exact (measure_mono hL).trans (bondPercolation_not_tb_le hq0 hq1 vB M K)
      · exact (measure_mono hR).trans (bondPercolation_not_tb_le hq0 hq1 vR M K)
    _ = 4 * (1 - ENNReal.ofReal p) := by ring

/-- **The Antal–Pisztora bound in two dimensions.**  For bond percolation on `ℤ²` at a density
`q > bondCritical 2`, there are `ρ ≥ 1`, `c > 0` and `R` such that, for `|y|₁ ≥ R`, the
chemical distance from `0` to `y` is finite and larger than `ρ |y|₁` with probability at most
`exp (-c |y|₁)`. -/
theorem antalPisztora_dim_two {q : ℝ} (hq : bondCritical 2 < q) (hq1 : q ≤ 1) :
    ∃ ρ c : ℝ, 1 ≤ ρ ∧ 0 < c ∧ ∃ R : ℕ, ∀ y : Site 2, (R : ℤ) ≤ mnorm y →
      bondPercolation 2 q
          {ω | ∃ m : ℕ, (openBondGraph ω).edist 0 y = (m : ℕ∞) ∧ ρ * (mnorm y : ℝ) < (m : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(c * (mnorm y : ℝ)))) := by
  obtain ⟨ε₀, hε₀, hred⟩ := chemicalDistance_of_blockScheme 2 le_rfl 1
  have hhalf : (1 / 2 : ℝ) < q := half_le_bondCritical_two.trans_lt hq
  have hq0 : 0 ≤ q := by linarith
  have hlim := Percolation.Literature.BollobasRiordan2006_ch3_lemma9_holds ⟨q, hq0, hq1⟩ hhalf
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ 4 * ENNReal.ofReal δ ≤ ε₀ := by
    by_cases htop : ε₀ = ⊤
    · exact ⟨1, one_pos, htop ▸ le_top⟩
    · refine ⟨ε₀.toReal / 4, by
        have := ENNReal.toReal_pos hε₀.ne' htop
        positivity, ?_⟩
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_toReal htop,
        ENNReal.ofReal_ofNat, ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hlim.eventually (lt_mem_nhds (by linarith : 1 - δ < 1)))
  have hbig := hn₀ (2 * n₀ + 1) (by omega)
  refine hred hq0 hq1 (frame_isBlockScheme n₀) fun b => (frameGood_bad_prob_le n₀ hq0 hq1 b).trans ?_
  refine le_trans ?_ hδε
  gcongr
  set p := Percolation.Literature.crossingProb ⟨q, hq0, hq1⟩ (3 * (2 * n₀ + 1) - 1)
    (2 * n₀ + 1 - 1)
  have hp0 : 0 ≤ p := (Percolation.Literature.crossingProb_mem_Icc _ _ _).1
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hp0]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end Exploding
