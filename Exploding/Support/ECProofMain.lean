/-
Proposition 7.1 assembled: under finite range of dependence and box-crossing, almost every
bounded nonnegative background is explosive.  The proof is a Peierls argument on the plane
of tiles: if a pile of `n` chips at the origin always stabilizes, the tiles that topple
completely are enclosed by a `*`-connected chain of tiles that are not box-crossing.
-/
import Exploding.Support.ECProofProb

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- If every constant pile stabilizes, a long `*`-path of non-crossing tiles exists. -/
theorem ec_robust_bad (hd : 2 ≤ d) (η : Site d → ℤ)
    (hη : ∀ x, 0 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1) (k : Fin d → ℕ) (hk : ∀ i, 0 < k i)
    (hrob : Robust η) :
    ∃ j : ℕ, ∃ l : List (ℤ × ℤ), l.Nodup ∧ List.IsChain ec_adj8 l ∧
      l.head? = some ((j : ℤ) + 1, 0) ∧ j + 3 ≤ l.length ∧
      ∀ z ∈ l, ¬ BoxCrossed η k (ec_emb d z) := by
  obtain ⟨F, hF, h0, hcl⟩ := ec_full_tiles hd η hη k hk hrob
  obtain ⟨j, l, hnd, hch, hhd, hlen, hz⟩ := ec_top F hF h0
  exact ⟨j, l, hnd, hch, hhd, hlen, fun z hzl => hcl z (hz z hzl).1 (hz z hzl).2⟩

/-- The double geometric series of the Peierls sum. -/
theorem ec_series_bound (ρ : ENNReal) (hρ : 8 * ρ ≤ 2⁻¹) :
    ∑' j : ℕ, ∑' i : ℕ, (8 : ENNReal) ^ (j + 2 + i) * ρ ^ (j + 2 + i + 1) ≤ 256 * ρ ^ 3 := by
  have hterm : ∀ j i : ℕ, (8 : ENNReal) ^ (j + 2 + i) * ρ ^ (j + 2 + i + 1) =
      64 * ρ ^ 3 * ((8 * ρ) ^ j * (8 * ρ) ^ i) := by
    intro j i; ring
  have hgeo : (1 - 8 * ρ)⁻¹ ≤ 2 := by
    have h1 : 2⁻¹ ≤ 1 - 8 * ρ := by
      calc (2 : ENNReal)⁻¹ = 1 - 2⁻¹ := ENNReal.one_sub_inv_two.symm
        _ ≤ 1 - 8 * ρ := tsub_le_tsub_left hρ 1
    calc (1 - 8 * ρ)⁻¹ ≤ (2⁻¹)⁻¹ := ENNReal.inv_le_inv.2 h1
      _ = 2 := inv_inv _
  calc ∑' j : ℕ, ∑' i : ℕ, (8 : ENNReal) ^ (j + 2 + i) * ρ ^ (j + 2 + i + 1)
      = ∑' j : ℕ, ∑' i : ℕ, (64 * ρ ^ 3 * (8 * ρ) ^ j) * (8 * ρ) ^ i := by
        refine tsum_congr (fun j => tsum_congr (fun i => ?_))
        rw [hterm]; ring
    _ = ∑' j : ℕ, (64 * ρ ^ 3 * (8 * ρ) ^ j) * (1 - 8 * ρ)⁻¹ := by
        refine tsum_congr (fun j => ?_)
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ = (64 * ρ ^ 3 * (1 - 8 * ρ)⁻¹) * (1 - 8 * ρ)⁻¹ := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ ≤ (64 * ρ ^ 3 * 2) * 2 := by gcongr
    _ = 256 * ρ ^ 3 := by ring

open Classical in
/-- The event that some nodup `*`-path of `j + 3 + i` tiles from `(j + 1, 0)` consists of
non-crossing tiles. -/
def ec_badSet (k : Fin d → ℕ) (j i : ℕ) : Set (Site d → ℤ) :=
  ⋃ l ∈ (ec_paths (j + 2 + i) ((j : ℤ) + 1, 0)).filter List.Nodup,
    {η | ∀ z ∈ l, ¬ BoxCrossed η k (ec_emb d z)}

theorem ec_badSet_prob (hd : 2 ≤ d) (P : Measure (Site d → ℤ)) [IsProbabilityMeasure P]
    (K : ℕ)
    (h1 : ∀ I J : Finset (Site d), (∀ a ∈ I, ∀ b ∈ J, (K : ℤ) < mnorm (a - b)) →
      ProbabilityTheory.IndepFun (fun η : Site d → ℤ => fun i : I => η i)
        (fun η : Site d → ℤ => fun j : J => η j) P)
    (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hbad : ∀ j, P {η | ¬ BoxCrossed η k j} ≤ ENNReal.ofReal (r ^ ((2 * K + 1) ^ 2)))
    (j i : ℕ) :
    P (ec_badSet k j i) ≤ (8 : ENNReal) ^ (j + 2 + i) * ENNReal.ofReal r ^ (j + 2 + i + 1) := by
  classical
  set F := (ec_paths (j + 2 + i) ((j : ℤ) + 1, 0)).filter List.Nodup with hF
  unfold ec_badSet
  calc P (⋃ l ∈ F, {η : Site d → ℤ | ∀ z ∈ l, ¬ BoxCrossed η k (ec_emb d z)})
      ≤ ∑ l ∈ F, P {η : Site d → ℤ | ∀ z ∈ l, ¬ BoxCrossed η k (ec_emb d z)} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ l ∈ F, ENNReal.ofReal r ^ (j + 2 + i + 1) := by
        refine Finset.sum_le_sum (fun l hl => ?_)
        obtain ⟨hlp, hnd⟩ := Finset.mem_filter.1 hl
        have := ec_path_prob hd P K h1 k hk r hr0 hr1 hbad l hnd
        rwa [ec_paths_length _ _ l hlp] at this
    _ = (F.card : ENNReal) * ENNReal.ofReal r ^ (j + 2 + i + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (8 : ENNReal) ^ (j + 2 + i) * ENNReal.ofReal r ^ (j + 2 + i + 1) := by
        gcongr
        have h1 : F.card ≤ 8 ^ (j + 2 + i) :=
          (Finset.card_filter_le _ _).trans (ec_paths_card _ _)
        calc (F.card : ENNReal) ≤ ((8 ^ (j + 2 + i) : ℕ) : ENNReal) := by exact_mod_cast h1
          _ = 8 ^ (j + 2 + i) := by push_cast; rfl

/-- **Almost every bounded nonnegative background is explosive**, under finite range of
dependence and box-crossing. -/
theorem ec_explosive_ae (hd : 2 ≤ d) (P : Measure (Site d → ℤ)) (hP : IsProbabilityMeasure P)
    (hsupp : ∀ᵐ η ∂P, ∀ x, 0 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1)
    (h1 : FiniteRangeOfDependence d P) (h2 : BoxCrossingHyp d P) : ∀ᵐ η ∂P, Explosive η := by
  classical
  obtain ⟨K, hK⟩ := h1
  have key : ∀ ε : ℝ, 0 < ε → P {η | ¬ Explosive η} ≤ ENNReal.ofReal ε := by
    intro ε hε
    set r : ℝ := min (1 / 16) ε with hr
    have hr0 : 0 < r := lt_min (by norm_num) hε
    have hr1 : r ≤ 1 / 16 := min_le_left _ _
    have hrε : r ≤ ε := min_le_right _ _
    set M : ℕ := (2 * K + 1) ^ 2 with hM
    have hδpos : 0 < r ^ M := pow_pos hr0 M
    obtain ⟨k, hk, hkP⟩ := h2 (r ^ M) hδpos
    have hδ1 : r ^ M ≤ 1 := pow_le_one₀ hr0.le (by linarith)
    have hbad : ∀ j, P {η | ¬ BoxCrossed η k j} ≤ ENNReal.ofReal (r ^ M) :=
      fun j => ec_bad_prob_le P k j (r ^ M) hδ1 (hkP j)
    have hcover : {η : Site d → ℤ | ¬ Explosive η} ⊆
        {η | ¬ ∀ x, 0 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1} ∪ ⋃ j : ℕ, ⋃ i : ℕ, ec_badSet k j i := by
      intro η hη
      by_cases hb : ∀ x, 0 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1
      · right
        have hrob : Robust η := not_not.1 hη
        obtain ⟨j, l, hnd, hch, hhd, hlen, hz⟩ := ec_robust_bad hd η hb k hk hrob
        obtain ⟨i, hi⟩ : ∃ i, l.length = j + 2 + i + 1 := ⟨l.length - (j + 3), by omega⟩
        refine Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨i, ?_⟩⟩
        unfold ec_badSet
        simp only [Set.mem_iUnion, Set.mem_setOf_eq]
        exact ⟨l, Finset.mem_filter.2 ⟨ec_mem_paths _ _ l hi hhd hch, hnd⟩, hz⟩
      · left; exact hb
    have hρ8 : 8 * ENNReal.ofReal r ≤ 2⁻¹ := by
      have e1 : (8 : ENNReal) * ENNReal.ofReal r = ENNReal.ofReal (8 * r) := by
        rw [ENNReal.ofReal_mul (by norm_num)]; simp
      have e2 : (2 : ENNReal)⁻¹ = ENNReal.ofReal (1 / 2) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
      rw [e1, e2]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    calc P {η | ¬ Explosive η}
        ≤ P ({η | ¬ ∀ x, 0 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1} ∪ ⋃ j : ℕ, ⋃ i : ℕ, ec_badSet k j i) :=
          measure_mono hcover
      _ ≤ P {η | ¬ ∀ x, 0 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1} + P (⋃ j : ℕ, ⋃ i : ℕ, ec_badSet k j i) :=
          measure_union_le _ _
      _ = P (⋃ j : ℕ, ⋃ i : ℕ, ec_badSet k j i) := by rw [ae_iff.1 hsupp, zero_add]
      _ ≤ ∑' j : ℕ, ∑' i : ℕ, P (ec_badSet k j i) :=
          (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun j => measure_iUnion_le _)
      _ ≤ ∑' j : ℕ, ∑' i : ℕ, (8 : ENNReal) ^ (j + 2 + i) * ENNReal.ofReal r ^ (j + 2 + i + 1) :=
          ENNReal.tsum_le_tsum fun j => ENNReal.tsum_le_tsum fun i =>
            ec_badSet_prob hd P K hK k hk r hr0.le (by linarith) hbad j i
      _ ≤ 256 * ENNReal.ofReal r ^ 3 := ec_series_bound _ hρ8
      _ ≤ ENNReal.ofReal ε := by
          have e3 : (256 : ENNReal) * ENNReal.ofReal r ^ 3 = ENNReal.ofReal (256 * r ^ 3) := by
            rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow hr0.le]; simp
          rw [e3]
          refine ENNReal.ofReal_le_ofReal ?_
          nlinarith [sq_nonneg r, hr0]
  rw [ae_iff]
  by_contra hne
  have hlt : 0 < (P {η | ¬ Explosive η}).toReal :=
    ENNReal.toReal_pos hne (measure_ne_top P _)
  have := key ((P {η | ¬ Explosive η}).toReal / 2) (by positivity)
  have h3 : ENNReal.ofReal ((P {η | ¬ Explosive η}).toReal / 2) < P {η | ¬ Explosive η} := by
    conv_rhs => rw [← ENNReal.ofReal_toReal (measure_ne_top P {η | ¬ Explosive η})]
    exact (ENNReal.ofReal_lt_ofReal_iff hlt).2 (by linarith)
  exact absurd this (not_le.2 h3)

end Exploding
