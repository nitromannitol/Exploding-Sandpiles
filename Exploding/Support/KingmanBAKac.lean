/-
The measure-theoretic package of the first-return (induced) map: for a measurable set `A` of
positive measure and a measure-preserving `T` on a probability space, the induced map
`T_A x = T^[r x] x` preserves the restriction `μ|_A` and the first return time `r` is
integrable on `A` with `∫_A r dμ ≤ 1` (Kac's lemma).  The ergodicity of the induced map is not
needed and is not proved here.

The proof is the standard one: for a measurable `B ⊆ A`, the sets
`U_N(B) = {x | x, T x, …, T^{N-1} x ∉ A, T^N x ∈ B}` satisfy
`μ (U_N) = μ (A ∩ {r = N+1} ∩ T^{-(N+1)} B) + μ (U_{N+1})`, and the `U_N` are pairwise disjoint.
-/
import Exploding.Support.MKingman4
import Mathlib.Dynamics.Ergodic.Conservative

open Exploding LatticeProb MeasureTheory Filter ProbabilityTheory
open scoped ENNReal

namespace Exploding

variable {Ω : Type}

section ReturnTime

/-- Characterisation of the first return time `r x = n` for `n ≥ 1`. -/
theorem king_returnTime_eq_iff (T : Ω → Ω) (A : Set Ω) (x : Ω) {n : ℕ} (hn : 1 ≤ n) :
    mk2_returnTime T A x = n ↔
      T^[n] x ∈ A ∧ ∀ j : ℕ, 1 ≤ j → j < n → T^[j] x ∉ A := by
  constructor
  · intro h
    have hne : ∃ m : ℕ, 1 ≤ m ∧ T^[m] x ∈ A := by
      by_contra hcon
      have hempty : {m : ℕ | 1 ≤ m ∧ T^[m] x ∈ A} = ∅ := by
        ext m
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hm => hcon ⟨m, hm⟩
      unfold mk2_returnTime at h
      rw [hempty, Nat.sInf_empty] at h
      omega
    have hmem : T^[n] x ∈ A := by
      have := mk2_inducedMap_mem T A x hne
      unfold mk2_inducedMap at this
      rwa [h] at this
    refine ⟨hmem, fun j hj1 hjn hjA => ?_⟩
    unfold mk2_returnTime at h
    have := Nat.sInf_le (s := {m : ℕ | 1 ≤ m ∧ T^[m] x ∈ A}) ⟨hj1, hjA⟩
    omega
  · rintro ⟨hA, hmin⟩
    have hne : ∃ m : ℕ, 1 ≤ m ∧ T^[m] x ∈ A := ⟨n, hn, hA⟩
    have hle : mk2_returnTime T A x ≤ n := Nat.sInf_le ⟨hn, hA⟩
    by_contra hne'
    have hlt : mk2_returnTime T A x < n := lt_of_le_of_ne hle hne'
    have hmem := mk2_returnTime_pos T A x hne
    have hmem2 := mk2_inducedMap_mem T A x hne
    exact hmin _ hmem hlt hmem2

/-- The first return time is `0` exactly when the orbit never returns to `A`. -/
theorem king_returnTime_eq_zero_iff (T : Ω → Ω) (A : Set Ω) (x : Ω) :
    mk2_returnTime T A x = 0 ↔ ∀ j : ℕ, 1 ≤ j → T^[j] x ∉ A := by
  constructor
  · intro h j hj hjA
    have hne : ∃ m : ℕ, 1 ≤ m ∧ T^[m] x ∈ A := ⟨j, hj, hjA⟩
    have := mk2_returnTime_pos T A x hne
    omega
  · intro h
    have hempty : {m : ℕ | 1 ≤ m ∧ T^[m] x ∈ A} = ∅ := by
      ext m
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hm => h m hm.1 hm.2
    unfold mk2_returnTime
    rw [hempty, Nat.sInf_empty]

variable [MeasurableSpace Ω]

/-- The first return time is measurable. -/
theorem king_returnTime_measurable {T : Ω → Ω} (hT : Measurable T) {A : Set Ω}
    (hA : MeasurableSet A) : Measurable (mk2_returnTime T A) := by
  refine measurable_to_countable' fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : mk2_returnTime T A ⁻¹' {0} = ⋂ j ∈ {j : ℕ | 1 ≤ j}, (T^[j]) ⁻¹' Aᶜ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, king_returnTime_eq_zero_iff,
        Set.mem_iInter, Set.mem_setOf_eq, Set.mem_compl_iff]
    rw [this]
    exact MeasurableSet.biInter (Set.to_countable _) fun j _ =>
      (hT.iterate j) hA.compl
  · have : mk2_returnTime T A ⁻¹' {n} =
        (T^[n]) ⁻¹' A ∩ ⋂ j ∈ {j : ℕ | 1 ≤ j ∧ j < n}, (T^[j]) ⁻¹' Aᶜ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, king_returnTime_eq_iff T A x hn,
        Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_compl_iff]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun j hj => h2 j hj.1 hj.2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun j hj1 hj2 => h2 j ⟨hj1, hj2⟩⟩
    rw [this]
    exact ((hT.iterate n) hA).inter
      (MeasurableSet.biInter (Set.to_countable _) fun j _ => (hT.iterate j) hA.compl)

/-- The induced map is measurable. -/
theorem king_inducedMap_measurable {T : Ω → Ω} (hT : Measurable T) {A : Set Ω}
    (hA : MeasurableSet A) : Measurable (mk2_inducedMap T A) := by
  have h1 : Measurable (fun p : ℕ × Ω => T^[p.1] p.2) :=
    measurable_from_prod_countable_right fun n => hT.iterate n
  have h2 : Measurable (fun x : Ω => (mk2_returnTime T A x, x)) :=
    (king_returnTime_measurable hT hA).prodMk measurable_id
  exact h1.comp h2

end ReturnTime

section Kac

variable [MeasurableSpace Ω]

/-- `U_N(B)`: the orbit avoids `A` at the times `0, …, N-1` and lands in `B` at time `N`. -/
def king_U (T : Ω → Ω) (A B : Set Ω) (N : ℕ) : Set Ω :=
  {x | (∀ j : ℕ, j < N → T^[j] x ∉ A) ∧ T^[N] x ∈ B}

/-- `D_N(B)`: the points of `A` whose first return to `A` takes `N + 1` steps and lands in `B`. -/
def king_D (T : Ω → Ω) (A B : Set Ω) (N : ℕ) : Set Ω :=
  A ∩ {x | mk2_returnTime T A x = N + 1} ∩ (T^[N + 1]) ⁻¹' B

theorem king_U_measurable {T : Ω → Ω} (hT : Measurable T) {A B : Set Ω} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (N : ℕ) : MeasurableSet (king_U T A B N) := by
  have : king_U T A B N = (⋂ j ∈ {j : ℕ | j < N}, (T^[j]) ⁻¹' Aᶜ) ∩ (T^[N]) ⁻¹' B := by
    ext x
    simp only [king_U, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_preimage,
      Set.mem_compl_iff]
  rw [this]
  exact (MeasurableSet.biInter (Set.to_countable _) fun j _ => (hT.iterate j) hA.compl).inter
    ((hT.iterate N) hB)

theorem king_D_measurable {T : Ω → Ω} (hT : Measurable T) {A B : Set Ω} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (N : ℕ) : MeasurableSet (king_D T A B N) := by
  have hr := king_returnTime_measurable hT hA
  exact (hA.inter (hr (measurableSet_singleton (N + 1)))).inter ((hT.iterate (N + 1)) hB)

omit [MeasurableSpace Ω] in
theorem king_preimage_U_inter (T : Ω → Ω) {A B : Set Ω} (hBA : B ⊆ A) (N : ℕ) :
    T ⁻¹' king_U T A B N ∩ A = king_D T A B N := by
  ext x
  have e : ∀ j : ℕ, T^[j] (T x) = T^[j + 1] x := fun j => (Function.iterate_succ_apply T j x).symm
  simp only [king_U, king_D, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, e]
  constructor
  · rintro ⟨⟨h1, h2⟩, hx⟩
    refine ⟨⟨hx, ?_⟩, h2⟩
    rw [king_returnTime_eq_iff T A x (Nat.succ_pos N)]
    refine ⟨hBA h2, fun j hj1 hjN => ?_⟩
    have := h1 (j - 1) (by omega)
    rwa [show j - 1 + 1 = j by omega] at this
  · rintro ⟨⟨hx, hr⟩, h2⟩
    rw [king_returnTime_eq_iff T A x (Nat.succ_pos N)] at hr
    refine ⟨⟨fun j hj => hr.2 (j + 1) (by omega) (by omega), h2⟩, hx⟩

omit [MeasurableSpace Ω] in
theorem king_preimage_U_diff (T : Ω → Ω) (A B : Set Ω) (N : ℕ) :
    T ⁻¹' king_U T A B N \ A = king_U T A B (N + 1) := by
  ext x
  have e : ∀ j : ℕ, T^[j] (T x) = T^[j + 1] x := fun j => (Function.iterate_succ_apply T j x).symm
  simp only [king_U, Set.mem_sdiff, Set.mem_preimage, Set.mem_setOf_eq, e]
  constructor
  · rintro ⟨⟨h1, h2⟩, hx⟩
    refine ⟨fun j hj => ?_, h2⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simpa using hx
    · have := h1 (j - 1) (by omega)
      rwa [show j - 1 + 1 = j by omega] at this
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun j hj => h1 (j + 1) (by omega), h2⟩, ?_⟩
    simpa using h1 0 (by omega)

/-- The one-step recursion for the measures of the sets `U_N`. -/
theorem king_U_step {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hBA : B ⊆ A) (N : ℕ) :
    μ (king_U T A B N) = μ (king_D T A B N) + μ (king_U T A B (N + 1)) := by
  have hU := king_U_measurable hT.measurable hA hB N
  have h1 : μ (T ⁻¹' king_U T A B N) = μ (king_U T A B N) :=
    hT.measure_preimage hU.nullMeasurableSet
  rw [← h1, ← measure_inter_add_sdiff (T ⁻¹' king_U T A B N) hA,
    king_preimage_U_inter T hBA, king_preimage_U_diff]

/-- Telescoping: `μ (U_{N0}) = ∑_{i<M} μ (D_{N0+i}) + μ (U_{N0+M})`. -/
theorem king_U_telescope {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hBA : B ⊆ A) (N0 M : ℕ) :
    μ (king_U T A B N0) =
      ∑ i ∈ Finset.range M, μ (king_D T A B (N0 + i)) + μ (king_U T A B (N0 + M)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [ih, Finset.sum_range_succ, king_U_step hT hA hB hBA (N0 + M), ← add_assoc]
    rfl

omit [MeasurableSpace Ω] in
/-- The sets `U_N(B)` are pairwise disjoint when `B ⊆ A`. -/
theorem king_U_disjoint (T : Ω → Ω) {A B : Set Ω} (hBA : B ⊆ A) :
    Pairwise (Function.onFun Disjoint (king_U T A B)) := by
  intro N M hNM
  rw [Function.onFun, Set.disjoint_left]
  intro x hxN hxM
  rcases lt_or_gt_of_ne hNM with h | h
  · exact hxM.1 N h (hBA hxN.2)
  · exact hxN.1 M h (hBA hxM.2)

/-- The total mass of the sets `U_N(B)` is at most `1`. -/
theorem king_tsum_U_le {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} (hT : Measurable T)
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (hBA : B ⊆ A) :
    ∑' N, μ (king_U T A B N) ≤ 1 := by
  rw [← measure_iUnion (king_U_disjoint T hBA) (fun N => king_U_measurable hT hA hB N)]
  exact prob_le_one

/-- **Mass formula.**  For measurable `B ⊆ A`, `μ B = ∑_N μ (D_N(B))`. -/
theorem king_measure_eq_tsum {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hBA : B ⊆ A) : μ B = ∑' N, μ (king_D T A B N) := by
  have hU0 : king_U T A B 0 = B := by ext x; simp [king_U]
  have htele := fun M => king_U_telescope hT hA hB hBA 0 M
  have hle : ∑' N, μ (king_D T A B N) ≤ μ B := by
    apply ENNReal.tsum_le_of_sum_range_le
    intro M
    have := htele M
    simp only [zero_add, hU0] at this
    rw [this]
    exact le_self_add
  have htail : Tendsto (fun N => μ (king_U T A B N)) atTop (nhds 0) := by
    have hsum : ∑' N, μ (king_U T A B N) ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (king_tsum_U_le hT.measurable hA hB hBA)
    exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsum
  have hge : μ B ≤ ∑' N, μ (king_D T A B N) := by
    have hlim : Tendsto (fun M => ∑' N, μ (king_D T A B N) + μ (king_U T A B M)) atTop
        (nhds (∑' N, μ (king_D T A B N) + 0)) := tendsto_const_nhds.add htail
    rw [add_zero] at hlim
    refine ge_of_tendsto hlim (Eventually.of_forall fun M => ?_)
    have := htele M
    simp only [zero_add, hU0] at this
    rw [this]
    exact add_le_add_left (ENNReal.sum_le_tsum _) _
  exact le_antisymm hge hle

/-- The induced map `T_A` preserves the restriction `μ|_A`. -/
theorem king_inducedMap_measurePreserving {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    MeasurePreserving (mk2_inducedMap T A) (μ.restrict A) (μ.restrict A) := by
  have hTA := king_inducedMap_measurable hT.measurable hA
  refine ⟨hTA, ?_⟩
  refine Measure.ext fun B hB => ?_
  rw [Measure.map_apply hTA hB, Measure.restrict_apply (hTA hB), Measure.restrict_apply hB]
  have hBA : MeasurableSet (B ∩ A) := hB.inter hA
  have hsub : B ∩ A ⊆ A := Set.inter_subset_right
  have hret : ∀ᵐ x ∂μ, x ∈ A → ∃ n : ℕ, 1 ≤ n ∧ T^[n] x ∈ A :=
    mk2_ae_return μ T hT.conservative A hA.nullMeasurableSet
  -- the preimage of `B` and of `B ∩ A` agree on `A`, up to a null set
  have h1 : μ (mk2_inducedMap T A ⁻¹' B ∩ A) = μ (⋃ N : ℕ, king_D T A (B ∩ A) N) := by
    refine measure_congr ?_
    rw [Filter.eventuallyEq_set]
    filter_upwards [hret] with x hx
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion, king_D, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hxB, hxA⟩
      have hne := hx hxA
      have hpos := mk2_returnTime_pos T A x hne
      have hmem := mk2_inducedMap_mem T A x hne
      refine ⟨mk2_returnTime T A x - 1, ⟨⟨hxA, by omega⟩, ?_⟩⟩
      have : mk2_returnTime T A x - 1 + 1 = mk2_returnTime T A x := by omega
      rw [this]
      exact ⟨hxB, hmem⟩
    · rintro ⟨N, ⟨⟨hxA, hr⟩, hB'⟩⟩
      refine ⟨?_, hxA⟩
      have : mk2_inducedMap T A x = T^[N + 1] x := by
        unfold mk2_inducedMap; rw [hr]
      rw [this]
      exact hB'.1
  rw [h1, measure_iUnion, ← king_measure_eq_tsum hT hA hBA hsub]
  · intro N M hNM
    rw [Function.onFun, Set.disjoint_left]
    intro x hxN hxM
    have h1 : mk2_returnTime T A x = N + 1 := hxN.1.2
    have h2 : mk2_returnTime T A x = M + 1 := hxM.1.2
    omega
  · exact fun N => king_D_measurable hT.measurable hA hBA N

omit [MeasurableSpace Ω] in
/-- With `B = A`, `D_N(A)` is the set of points of `A` with first return time `N + 1`. -/
theorem king_D_self (T : Ω → Ω) (A : Set Ω) (N : ℕ) :
    king_D T A A N = A ∩ {x | mk2_returnTime T A x = N + 1} := by
  ext x
  simp only [king_D, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, _⟩; exact h
  · rintro ⟨hxA, hr⟩
    refine ⟨⟨hxA, hr⟩, ?_⟩
    exact ((king_returnTime_eq_iff T A x (Nat.succ_pos N)).1 hr).1

/-- The exact telescoping identity behind Kac's lemma:
`∑_{N<M} μ(U_N) = ∑_{i<M} (i+1) μ(A ∩ {r = i+1}) + M μ(U_M)`. -/
theorem king_sum_U_eq {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {A : Set Ω}
    (hA : MeasurableSet A) (M : ℕ) :
    ∑ N ∈ Finset.range M, μ (king_U T A A N) =
      ∑ i ∈ Finset.range M, ((i : ℝ≥0∞) + 1) * μ (A ∩ {x | mk2_returnTime T A x = i + 1})
        + (M : ℝ≥0∞) * μ (king_U T A A M) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ,
      king_U_step hT hA hA subset_rfl M, king_D_self]
    push_cast
    ring

/-- **Kac's lemma (one direction).**  `∫_A r dμ ≤ 1`. -/
theorem king_lintegral_returnTime_le {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    ∫⁻ x, (mk2_returnTime T A x : ℝ≥0∞) ∂(μ.restrict A) ≤ 1 := by
  have hr := king_returnTime_measurable hT.measurable hA
  set R : ℕ → Set Ω := fun n => A ∩ {x | mk2_returnTime T A x = n} with hR
  have hRm : ∀ n, MeasurableSet (R n) := fun n => hA.inter (hr (measurableSet_singleton n))
  have hRd : Pairwise (Function.onFun Disjoint R) := by
    intro n m hnm
    rw [Function.onFun, Set.disjoint_left]
    intro x hxn hxm
    exact hnm (hxn.2.symm.trans hxm.2)
  have hUnion : (⋃ n, R n) = A := by
    ext x
    simp only [hR, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨_, h, rfl⟩⟩
  have h1 : ∫⁻ x, (mk2_returnTime T A x : ℝ≥0∞) ∂(μ.restrict A)
      = ∑' n : ℕ, (n : ℝ≥0∞) * μ (R n) := by
    rw [show μ.restrict A = μ.restrict (⋃ n, R n) by rw [hUnion], lintegral_iUnion hRm hRd]
    refine tsum_congr fun n => ?_
    rw [setLIntegral_congr_fun (hRm n) (g := fun _ => (n : ℝ≥0∞)) (fun x hx => by
      simp only [hR, Set.mem_inter_iff, Set.mem_setOf_eq] at hx
      rw [hx.2]), setLIntegral_const]
  rw [h1]
  apply ENNReal.tsum_le_of_sum_range_le
  intro M
  rcases M with _ | M
  · simp
  · rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one]
    calc ∑ i ∈ Finset.range M, ((i : ℝ≥0∞) + 1) * μ (R (i + 1))
        ≤ ∑ N ∈ Finset.range M, μ (king_U T A A N) := by
          rw [king_sum_U_eq hT hA M]
          exact le_self_add
      _ ≤ ∑' N, μ (king_U T A A N) := ENNReal.sum_le_tsum _
      _ ≤ 1 := king_tsum_U_le hT.measurable hA hA subset_rfl

/-- The induced map preserves the normalised restriction `μ_A`. -/
theorem king_inducedMap_measurePreserving_normalized {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    MeasurePreserving (mk2_inducedMap T A) (mk3_normalizedRestrict μ A)
      (mk3_normalizedRestrict μ A) := by
  have h := king_inducedMap_measurePreserving hT hA
  refine ⟨h.measurable, ?_⟩
  unfold mk3_normalizedRestrict
  rw [Measure.map_smul, h.map_eq]

/-- The first return time is integrable for the normalised restriction `μ_A` (Kac). -/
theorem king_returnTime_integrable {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) (hA0 : μ A ≠ 0) :
    Integrable (fun x => (mk2_returnTime T A x : ℝ)) (mk3_normalizedRestrict μ A) := by
  have hr := king_returnTime_measurable hT.measurable hA
  have hrm : Measurable (fun x => (mk2_returnTime T A x : ℝ)) := measurable_from_top.comp hr
  have hint : Integrable (fun x => (mk2_returnTime T A x : ℝ)) (μ.restrict A) := by
    refine ⟨hrm.aestronglyMeasurable, ?_⟩
    have := king_lintegral_returnTime_le hT hA
    refine lt_of_le_of_lt ?_ (lt_of_le_of_lt this ENNReal.one_lt_top)
    refine le_of_eq ?_
    refine lintegral_congr fun x => ?_
    simp
  have hc : (μ A)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hA0
  exact hint.smul_measure hc

end Kac

end Exploding
