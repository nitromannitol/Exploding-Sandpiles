/-
Proposition 5.1 of the paper (generalized last wave), the Section-3 assembly, part E:
subadditivity of the limit `N₀` on integer directions.  The microscopic subadditivity
`T̃(0, n(a+b)) ≤ T̃(0, na) + T̃(na, n(a+b))` and the covariance
`T̃(na, n(a+b))(η) = T̃(0, nb)(T_{na} η)` give the inequality on an event of positive
probability, since the shifted copy converges in probability.
-/
import Exploding.Support.GLWSec3D

open Exploding LatticeProb MeasureTheory Filter
open scoped Classical

namespace Exploding

variable {d : ℕ}

theorem glws_g_eq_of_mem {ηmin : ℤ} {L : AddSubgroup (Site d)} {η : Site d → ℤ}
    (hη : η ∈ glws_G d ηmin L) (y : Site d)
    (n : ℕ) : glws_g ηmin L y n η = glws_f η ((n : ℤ) • y) := by
  unfold glws_g
  rw [if_pos hη]

/-- The pointwise cocycle inequality along a pair of directions. -/
theorem glws_f_add_shift (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin) {L : AddSubgroup (Site d)}
    {η : Site d → ℤ} (hη : η ∈ glws_G d ηmin L) {a : Site d} (ha : a ∈ L) (b : Site d) (n : ℕ) :
    glws_f η ((n : ℤ) • (a + b)) ≤
      glws_f η ((n : ℤ) • a) + glws_f (fun z => η ((n : ℤ) • a + z)) ((n : ℤ) • b) := by
  have h := glws_f_subadd hd ηmin hηmin hη L.zero_mem (L.zsmul_mem ha n) ((n : ℤ) • (a + b))
  have hshift := lwc_cluster_shift d η ((n : ℤ) • a) (0 : Site d) ((n : ℤ) • b)
  have e1 : (n : ℤ) • a + (0 : Site d) = (n : ℤ) • a := add_zero _
  have e2 : (n : ℤ) • a + (n : ℤ) • b = (n : ℤ) • (a + b) := by rw [smul_add]
  rw [e1, e2] at hshift
  unfold glws_f
  rw [hshift]
  exact h

/-- **Subadditivity of `N₀`**, when the first direction lies in the sublattice. -/
theorem glws_N0_subadd_L (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (L : AddSubgroup (Site d)) (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hstat : StationaryOn d L P) (hG : ∀ᵐ η ∂P, η ∈ glws_G d ηmin L) (N0 : Site d → ℝ)
    (hN0 : ∀ v : Site d, ∀ᵐ η ∂P,
      Tendsto (fun n : ℕ => glws_f η ((n : ℤ) • v) / (n : ℝ)) atTop (nhds (N0 v)))
    (a b : Site d) (ha : a ∈ L) : N0 (a + b) ≤ N0 a + N0 b := by
  haveI := hP
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set e : ℝ := ε / 3 with he
  have he0 : 0 < e := by rw [he]; positivity
  -- the events
  set H : ℕ → Set (Site d → ℤ) := fun m => glws_G d ηmin L ∩ ⋂ n : ℕ, ⋂ (_ : m ≤ n),
    ({η | glws_g ηmin L a n η / (n : ℝ) ≤ N0 a + e} ∩
      {η | N0 (a + b) - e ≤ glws_g ηmin L (a + b) n η / (n : ℝ)}) with hH
  set F : ℕ → Set (Site d → ℤ) := fun m => ⋂ n : ℕ, ⋂ (_ : m ≤ n),
    {η | glws_g ηmin L b n η / (n : ℝ) ≤ N0 b + e} with hF
  have hHm : ∀ m, MeasurableSet (H m) := by
    intro m
    refine (glws_G_measurable d ηmin L).inter (MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ => ?_)
    exact (measurableSet_le ((glws_g_measurable ηmin L a n).div_const _) measurable_const).inter
      (measurableSet_le measurable_const ((glws_g_measurable ηmin L (a + b) n).div_const _))
  have hFm : ∀ m, MeasurableSet (F m) := by
    intro m
    refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ => ?_
    exact measurableSet_le ((glws_g_measurable ηmin L b n).div_const _) measurable_const
  have hHmono : Monotone H := by
    intro m m' hmm' η hη
    refine ⟨hη.1, Set.mem_iInter.mpr fun n => Set.mem_iInter.mpr fun hn => ?_⟩
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hη.2 n) (le_trans hmm' hn)
  have hFmono : Monotone F := by
    intro m m' hmm' η hη
    refine Set.mem_iInter.mpr fun n => Set.mem_iInter.mpr fun hn => ?_
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hη n) (le_trans hmm' hn)
  -- the unions have full measure
  have hHun : P (⋃ m, H m) = 1 := by
    have hae : ∀ᵐ η ∂P, η ∈ ⋃ m, H m := by
      filter_upwards [hG, hN0 a, hN0 (a + b)] with η h1 h2 h3
      have h2' := h2.eventually (gt_mem_nhds (by linarith : N0 a < N0 a + e))
      have h3' := h3.eventually (lt_mem_nhds (by linarith : N0 (a + b) - e < N0 (a + b)))
      obtain ⟨m, hm⟩ := eventually_atTop.mp (h2'.and h3')
      refine Set.mem_iUnion.mpr ⟨m, h1, Set.mem_iInter.mpr fun n => Set.mem_iInter.mpr fun hn => ?_⟩
      obtain ⟨u, v⟩ := hm n hn
      refine ⟨?_, ?_⟩
      · show glws_g ηmin L a n η / (n : ℝ) ≤ N0 a + e
        rw [glws_g_eq_of_mem h1]
        exact u.le
      · show N0 (a + b) - e ≤ glws_g ηmin L (a + b) n η / (n : ℝ)
        rw [glws_g_eq_of_mem h1]
        exact v.le
    have hmeas : MeasurableSet (⋃ m, H m) := MeasurableSet.iUnion hHm
    exact (prob_compl_eq_zero_iff hmeas).mp (ae_iff.mp hae)
  have hFun : P (⋃ m, F m) = 1 := by
    have hae : ∀ᵐ η ∂P, η ∈ ⋃ m, F m := by
      filter_upwards [hG, hN0 b] with η h1 h2
      have h2' := h2.eventually (gt_mem_nhds (by linarith : N0 b < N0 b + e))
      obtain ⟨m, hm⟩ := eventually_atTop.mp h2'
      refine Set.mem_iUnion.mpr ⟨m, Set.mem_iInter.mpr fun n => Set.mem_iInter.mpr fun hn => ?_⟩
      show glws_g ηmin L b n η / (n : ℝ) ≤ N0 b + e
      rw [glws_g_eq_of_mem h1]
      exact (hm n hn).le
    have hmeas : MeasurableSet (⋃ m, F m) := MeasurableSet.iUnion hFm
    exact (prob_compl_eq_zero_iff hmeas).mp (ae_iff.mp hae)
  have hHt := tendsto_measure_iUnion_atTop (μ := P) hHmono
  have hFt := tendsto_measure_iUnion_atTop (μ := P) hFmono
  rw [hHun] at hHt
  rw [hFun] at hFt
  have hhalf : (1 / 2 : ENNReal) < 1 := by
    rw [ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
  have hHev : ∀ᶠ m in atTop, (1 / 2 : ENNReal) < (P ∘ H) m := hHt.eventually (lt_mem_nhds hhalf)
  have hFev : ∀ᶠ m in atTop, (1 / 2 : ENNReal) < (P ∘ F) m := hFt.eventually (lt_mem_nhds hhalf)
  obtain ⟨m, hm1, hm2⟩ := (hHev.and hFev).exists
  -- a positive-probability set of good backgrounds at the scale `n = m + 1`
  set n : ℕ := m + 1 with hn
  have hnm : m ≤ n := Nat.le_succ m
  have hmp := glw_shift_ergodic_meas_pres d L P hstat ((n : ℤ) • a) (L.zsmul_mem ha n)
  set S : Set (Site d → ℤ) := (fun η : Site d → ℤ => fun z => η ((n : ℤ) • a + z)) ⁻¹' F m
    with hS
  have hSm : MeasurableSet S := hmp.measurable (hFm m)
  have hSP : P S = P (F m) := hmp.measure_preimage (hFm m).nullMeasurableSet
  have hsum : 1 < P (H m) + P S := by
    rw [hSP]
    calc (1 : ENNReal) = 1 / 2 + 1 / 2 := (ENNReal.add_halves 1).symm
      _ < P (H m) + P (F m) := ENNReal.add_lt_add hm1 hm2
  have hunion : P (H m ∪ S) + P (H m ∩ S) = P (H m) + P S := measure_union_add_inter _ hSm
  have hne : P (H m ∩ S) ≠ 0 := by
    intro h0
    rw [h0, add_zero] at hunion
    have : P (H m ∪ S) ≤ 1 := prob_le_one
    rw [hunion] at this
    exact absurd hsum (not_lt.mpr this)
  obtain ⟨η, hηH, hηS⟩ := nonempty_of_measure_ne_zero hne
  have hηG : η ∈ glws_G d ηmin L := hηH.1
  have hTG : (fun z => η ((n : ℤ) • a + z)) ∈ glws_G d ηmin L :=
    glws_G_shift hηG (L.zsmul_mem ha n)
  have hηH2 := hηH.2
  simp only [Set.mem_iInter] at hηH2
  obtain ⟨hA, hAB⟩ := hηH2 n hnm
  have hB : glws_g ηmin L b n (fun z => η ((n : ℤ) • a + z)) / (n : ℝ) ≤ N0 b + e := by
    have := hηS
    simp only [hS, Set.mem_preimage, hF, Set.mem_iInter] at this
    exact this n hnm
  simp only [Set.mem_setOf_eq] at hA hAB
  rw [glws_g_eq_of_mem hηG] at hA hAB
  rw [glws_g_eq_of_mem hTG] at hB
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.succ_pos m
  have hmain := glws_f_add_shift hd ηmin hηmin hηG ha b n
  have h1 : N0 (a + b) - e ≤ (glws_f η ((n : ℤ) • a) + glws_f (fun z => η ((n : ℤ) • a + z))
      ((n : ℤ) • b)) / (n : ℝ) :=
    le_trans hAB (div_le_div_of_nonneg_right hmain hnpos.le)
  rw [add_div] at h1
  linarith

/-- **Subadditivity of `N₀`** on all integer directions. -/
theorem glws_N0_subadd (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0) (P : Measure (Site d → ℤ))
    (hP : IsProbabilityMeasure P) (hstat : StationaryOn d L P)
    (hG : ∀ᵐ η ∂P, η ∈ glws_G d ηmin L) (N0 : Site d → ℝ)
    (hN0 : ∀ v : Site d, ∀ᵐ η ∂P,
      Tendsto (fun n : ℕ => glws_f η ((n : ℤ) • v) / (n : ℝ)) atTop (nhds (N0 v)))
    {η₀ : Site d → ℤ}
    (hlat : ∀ v : Site d,
      Tendsto (fun n : ℕ => glws_f η₀ ((n : ℤ) • v) / (n : ℝ)) atTop (nhds (N0 v)))
    (a b : Site d) : N0 (a + b) ≤ N0 a + N0 b := by
  obtain ⟨qa, hqa0, _, hqaL⟩ := AddSubgroup.exists_nsmul_mem_of_index_ne_zero hL a
  obtain ⟨qb, hqb0, _, hqbL⟩ := AddSubgroup.exists_nsmul_mem_of_index_ne_zero hL b
  set q : ℕ := qa * qb with hq
  have hqpos : 0 < q := Nat.mul_pos hqa0 hqb0
  have haL : (q : ℤ) • a ∈ L := by
    have : (q : ℤ) • a = qb • (qa • a) := by
      rw [natCast_zsmul]
      show (qa * qb) • a = qb • (qa • a)
      rw [mul_comm, mul_smul]
    rw [this]; exact L.nsmul_mem hqaL qb
  have hsub := glws_N0_subadd_L hd ηmin hηmin L P hP hstat hG N0 hN0 ((q : ℤ) • a) ((q : ℤ) • b) haL
  have e1 : (q : ℤ) • a + (q : ℤ) • b = (q : ℤ) • (a + b) := by rw [smul_add]
  rw [e1, glws_N0_nsmul hlat (a + b) q, glws_N0_nsmul hlat a q, glws_N0_nsmul hlat b q] at hsub
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hqpos
  nlinarith

end Exploding
