/-
The Peierls estimate for bad blocks.

A predicate `good ω b` on blocks is local when it depends only on the bonds inside the window of
radius `r` of `b`.  Blocks at sup-norm distance more than `2r` then read disjoint bonds, so a
`(2r+1)`-spaced family of blocks has independent bad events.  Packing, the exponential count of
star-connected sets and the marked-animal argument give a geometric tail for the halo of bad
blocks around a short reference set, as soon as every block is bad with probability at most a
threshold depending only on `d` and `r`.  This is the argument of
`Exploding.Support.ArxivBondClusterHaloTail` for block events.
-/
import Exploding.Support.APCoarseGeometry
import Exploding.Support.APPredicateHalo
import Exploding.Support.ArxivBondReferencePath
import Exploding.Support.ExtAPProof4
import Exploding.Support.ExtMHCount
import Exploding.Support.RNProofGraph

open LatticeProb MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Exploding

variable {d : ℕ}

/-! ### Spaced packings -/

/-- The colour of a site modulo `K`. -/
def spacedColor (K : ℕ) (hK : 0 < K) (z : Site d) : Fin d → Fin K :=
  fun i => ⟨(z i % K).toNat, by
    have h1 : 0 ≤ z i % K := Int.emod_nonneg _ (by exact_mod_cast hK.ne')
    have h2 : z i % K < K := Int.emod_lt_of_pos _ (by exact_mod_cast hK)
    omega⟩

theorem spacedColor_far {K : ℕ} (hK : 0 < K) {z w : Site d}
    (hc : spacedColor K hK z = spacedColor K hK w) (hne : z ≠ w) : ∃ i, (K : ℤ) ≤ |z i - w i| := by
  by_contra hcon
  push Not at hcon
  apply hne
  funext i
  have hK' : (0 : ℤ) < K := by exact_mod_cast hK
  have hi : z i % K = w i % K := by
    have := congrFun hc i
    simp only [spacedColor, Fin.mk.injEq] at this
    have h1 : 0 ≤ z i % K := Int.emod_nonneg _ hK'.ne'
    have h3 : 0 ≤ w i % K := Int.emod_nonneg _ hK'.ne'
    omega
  have hdvd : (K : ℤ) ∣ z i - w i := by
    rw [Int.dvd_iff_emod_eq_zero]
    exact (Int.emod_eq_emod_iff_emod_sub_eq_zero).mp hi
  have h0 := Int.eq_zero_of_abs_lt_dvd hdvd (hcon i)
  omega

/-- Every finite set of sites contains a subset of pairwise `K`-spaced sites carrying at least a
`K^{-d}` fraction of it. -/
theorem exists_spaced_packing {K : ℕ} (hK : 0 < K) (Γ : Finset (Site d)) :
    ∃ Γ' ⊆ Γ, (∀ z ∈ Γ', ∀ w ∈ Γ', z ≠ w → ∃ i, (K : ℤ) ≤ |z i - w i|) ∧
      Γ.card ≤ K ^ d * Γ'.card := by
  classical
  let fib : (Fin d → Fin K) → Finset (Site d) := fun c => Γ.filter fun z => spacedColor K hK z = c
  have hdisj : ∀ c ∈ (Finset.univ : Finset (Fin d → Fin K)),
      ∀ c' ∈ Finset.univ, c ≠ c' → Disjoint (fib c) (fib c') := by
    intro c _ c' _ hcc
    rw [Finset.disjoint_left]
    intro z hzc hzc'
    exact hcc ((Finset.mem_filter.1 hzc).2.symm.trans (Finset.mem_filter.1 hzc').2)
  have hUnion : Γ = Finset.univ.biUnion fib := by
    ext z
    constructor
    · intro hz
      exact Finset.mem_biUnion.2 ⟨spacedColor K hK z, Finset.mem_univ _,
        Finset.mem_filter.2 ⟨hz, rfl⟩⟩
    · intro hz
      rcases Finset.mem_biUnion.1 hz with ⟨c, _, hzc⟩
      exact (Finset.mem_filter.1 hzc).1
  have hsum : Γ.card = ∑ c : Fin d → Fin K, (fib c).card := by
    rw [hUnion, Finset.card_biUnion hdisj]
  have hne : (Finset.univ : Finset (Fin d → Fin K)).Nonempty :=
    ⟨fun _ => ⟨0, hK⟩, Finset.mem_univ _⟩
  obtain ⟨c₀, _, hc₀⟩ := Finset.exists_max_image Finset.univ (fun c => (fib c).card) hne
  refine ⟨fib c₀, Finset.filter_subset _ _, ?_, ?_⟩
  · intro z hz w hw hne
    exact spacedColor_far hK ((Finset.mem_filter.1 hz).2.trans (Finset.mem_filter.1 hw).2.symm) hne
  · calc Γ.card = ∑ c : Fin d → Fin K, (fib c).card := hsum
      _ ≤ ∑ _c : Fin d → Fin K, (fib c₀).card :=
          Finset.sum_le_sum fun c _ => hc₀ c (Finset.mem_univ c)
      _ = K ^ d * (fib c₀).card := by
          rw [Finset.sum_const, smul_eq_mul]
          congr 1
          simp

/-! ### Local events -/

/-- An event determined by finitely many coordinates is measurable for the σ-algebra of these
coordinates. -/
theorem measurableSet_comap_domRestrict_of_local {V : Type*} {A : Set V} (hA : A.Finite)
    {E : Set (V → Bool)} (hdet : ∀ ζ ζ' : V → Bool, (∀ b ∈ A, ζ b = ζ' b) → (ζ ∈ E ↔ ζ' ∈ E)) :
    MeasurableSet[MeasurableSpace.comap (fun ζ : V → Bool => A.domRestrict ζ) inferInstance] E := by
  classical
  have himage : E = (fun ζ : V → Bool => A.domRestrict ζ) ⁻¹'
      ((fun ζ : V → Bool => A.domRestrict ζ) '' E) := by
    ext ζ
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro hζ
      exact ⟨ζ, hζ, rfl⟩
    · rintro ⟨ζ', hζ', heq⟩
      exact (hdet ζ' ζ (fun b hb => congrFun heq ⟨b, hb⟩)).mp hζ'
  have : Fintype ↥A := hA.fintype
  rw [himage]
  exact (Set.to_countable _).measurableSet.preimage (measurable_iff_comap_le.mpr le_rfl)

/-- A predicate on blocks is local at radius `r`: whether `b` is good depends only on the bonds
inside the window of radius `r` of `b`. -/
def IsLocalBlockPredicate (N r : ℕ) (good : (Site d × Fin d → Bool) → Site d → Prop) : Prop :=
  ∀ b (ω ω' : Site d × Fin d → Bool), (∀ e ∈ windowBonds N r b, ω e = ω' e) →
    (good ω b ↔ good ω' b)

/-- For a local predicate, all blocks of a finite set are bad with probability at most the
threshold raised to the power of the size of the set divided by `(2r+1)^d`. -/
theorem bad_blocks_prob_le {N r : ℕ} (hN : 0 < N) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {good : (Site d × Fin d → Bool) → Site d → Prop} (hloc : IsLocalBlockPredicate N r good)
    {ε : ℝ≥0∞} (hbad : ∀ b, bondPercolation d q {ω | ¬ good ω b} ≤ ε) (B : Finset (Site d)) :
    bondPercolation d q {ω | ∀ b ∈ B, ¬ good ω b} ≤ ε ^ (B.card / (2 * r + 1) ^ d) := by
  classical
  have : IsProbabilityMeasure (bitLaw q) := rn_bitLaw_isProb hq0 hq1
  have : IsProbabilityMeasure (bondPercolation d q) := rn_infinitePi_isProb hq0 hq1
  by_cases hε : 1 ≤ ε
  · exact prob_le_one.trans (one_le_pow₀ hε)
  push Not at hε
  obtain ⟨Γ, hΓB, hsep, hcard⟩ := exists_spaced_packing (K := 2 * r + 1) (by omega) B
  let I := {b // b ∈ Γ}
  let A : I → Set (Site d × Fin d) := fun b => windowBonds N r b.1
  let E : I → Set (Site d × Fin d → Bool) := fun b => {ω | ¬ good ω b.1}
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro b b' hbb
    apply windowBonds_disjoint
    obtain ⟨i, hi⟩ := hsep b.1 b.2 b'.1 b'.2 (fun h => hbb (Subtype.ext h))
    exact ⟨i, by push_cast at hi; exact hi⟩
  have hE : ∀ b : I, MeasurableSet[MeasurableSpace.comap
      (fun ζ : Site d × Fin d → Bool => (A b).domRestrict ζ) inferInstance] (E b) := by
    intro b
    refine measurableSet_comap_domRestrict_of_local (windowBonds_finite hN r b.1) ?_
    intro ζ ζ' h
    exact not_congr (hloc b.1 ζ ζ' h)
  have hind : iIndepSet E (bondPercolation d q) := by
    change iIndepSet E (Measure.infinitePi fun _ : Site d × Fin d => bitLaw q)
    exact xap4_iIndepSet_of_pairwise_disjoint_bool (bitLaw q) A hdisj E hE
  have hsub : {ω : Site d × Fin d → Bool | ∀ b ∈ B, ¬ good ω b} ⊆
      ⋂ b ∈ (Finset.univ : Finset I), E b := by
    intro ω hω
    simp only [Set.mem_iInter]
    intro b _
    exact hω b.1 (hΓB b.2)
  have hdiv : B.card / (2 * r + 1) ^ d ≤ Γ.card := by
    rw [Nat.div_le_iff_le_mul_add_pred (by positivity)]
    nlinarith [Nat.zero_le ((2 * r + 1) ^ d - 1)]
  calc
    bondPercolation d q {ω | ∀ b ∈ B, ¬ good ω b}
        ≤ bondPercolation d q (⋂ b ∈ (Finset.univ : Finset I), E b) := measure_mono hsub
    _ = ∏ b ∈ (Finset.univ : Finset I), bondPercolation d q (E b) :=
        hind.meas_biInter Finset.univ
    _ ≤ ∏ _b ∈ (Finset.univ : Finset I), ε := Finset.prod_le_prod' fun b _ => hbad b.1
    _ = ε ^ Γ.card := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
    _ ≤ ε ^ (B.card / (2 * r + 1) ^ d) := pow_le_pow_right_of_le_one' hε.le hdiv

/-! ### Marked animals of bad blocks -/

/-- The probability of a rooted star-animal of `m` blocks containing `k` marked bad blocks. -/
theorem marked_bad_block_animal_prob_le (d : ℕ) :
    ∃ K : ℕ, ∀ {N r : ℕ}, 0 < N → ∀ {q : ℝ}, 0 ≤ q → q ≤ 1 →
      ∀ {good : (Site d × Fin d → Bool) → Site d → Prop}, IsLocalBlockPredicate N r good →
      ∀ {ε : ℝ≥0∞}, (∀ b, bondPercolation d q {ω | ¬ good ω b} ≤ ε) →
      ∀ (p : Site d) (m k : ℕ),
      bondPercolation d q
        {ω | ∃ F B : Finset (Site d), p ∈ F ∧ F.card = m ∧
          xmh_SConn (F : Set (Site d)) ∧ B ⊆ F ∧ B.card = k ∧ ∀ x ∈ B, ¬ good ω x} ≤
        ((K : ℝ≥0∞) ^ m * (2 : ℝ≥0∞) ^ m) * ε ^ (k / (2 * r + 1) ^ d) := by
  classical
  obtain ⟨K, hcount⟩ := xmh_starCount d
  refine ⟨K, ?_⟩
  intro N r hN q hq0 hq1 good hloc ε hbad p m k
  obtain ⟨T, hTcard, hTmem⟩ := hcount p m
  let T' : Finset (Finset (Site d)) := T.filter (fun F => F.card = m)
  let b : ℝ≥0∞ := ε ^ (k / (2 * r + 1) ^ d)
  let marked : Finset (Site d) → Finset (Finset (Site d)) :=
    fun F => F.powerset.filter (fun B => B.card = k)
  have hsub :
      {ω | ∃ F B : Finset (Site d), p ∈ F ∧ F.card = m ∧
        xmh_SConn (F : Set (Site d)) ∧ B ⊆ F ∧ B.card = k ∧ ∀ x ∈ B, ¬ good ω x} ⊆
        ⋃ F ∈ T', ⋃ B ∈ marked F, {ω | ∀ x ∈ B, ¬ good ω x} := by
    rintro ω ⟨F, B, hp, hcard, hconn, hBF, hBcard, hdef⟩
    refine Set.mem_iUnion.mpr ⟨F, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨hTmem F hp hcard hconn, hcard⟩
    · refine Set.mem_iUnion.mpr ⟨B, Set.mem_iUnion.mpr ⟨?_, hdef⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hBF, hBcard⟩
  have hmarked (F : Finset (Site d)) (hFm : F.card = m) :
      ((marked F).card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ m := by
    have hcard : (marked F).card ≤ 2 ^ m := by
      calc
        (marked F).card ≤ F.powerset.card := Finset.card_filter_le _ _
        _ = 2 ^ m := by rw [Finset.card_powerset, hFm]
    exact_mod_cast hcard
  have hsum :
      bondPercolation d q (⋃ F ∈ T', ⋃ B ∈ marked F, {ω | ∀ x ∈ B, ¬ good ω x}) ≤
        (T'.card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ m * b) := by
    calc
      _ ≤ ∑ F ∈ T', bondPercolation d q (⋃ B ∈ marked F, {ω | ∀ x ∈ B, ¬ good ω x}) :=
          measure_biUnion_finset_le T' _
      _ ≤ ∑ _F ∈ T', ((2 : ℝ≥0∞) ^ m * b) := by
        apply Finset.sum_le_sum
        intro F hF
        have hFm : F.card = m := (Finset.mem_filter.mp hF).2
        calc
          _ ≤ ∑ B ∈ marked F, bondPercolation d q {ω | ∀ x ∈ B, ¬ good ω x} :=
              measure_biUnion_finset_le (marked F) _
          _ ≤ ∑ _B ∈ marked F, b := by
            apply Finset.sum_le_sum
            intro B hB
            have hBk : B.card = k := (Finset.mem_filter.mp hB).2
            simpa only [b, hBk] using bad_blocks_prob_le hN hq0 hq1 hloc hbad B
          _ = ((marked F).card : ℝ≥0∞) * b := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (2 : ℝ≥0∞) ^ m * b := mul_le_mul_of_nonneg_right (hmarked F hFm) zero_le
      _ = (T'.card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ m * b) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hT' : (T'.card : ℝ≥0∞) ≤ (K : ℝ≥0∞) ^ m := by
    have hcard : T'.card ≤ K ^ m := (Finset.card_filter_le _ _).trans hTcard
    exact_mod_cast hcard
  calc
    _ ≤ bondPercolation d q (⋃ F ∈ T', ⋃ B ∈ marked F, {ω | ∀ x ∈ B, ¬ good ω x}) :=
      measure_mono hsub
    _ ≤ (T'.card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ m * b) := hsum
    _ ≤ ((K : ℝ≥0∞) ^ m * (2 : ℝ≥0∞) ^ m) * b := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right hT' zero_le

/-- A star-connected set containing `p` with at least `m` sites, all bad outside `P`, contains a
rooted star-animal of `m` sites with `k` marked bad sites, provided `|P| + k ≤ m`. -/
theorem exists_marked_animal_of_connected_pred {G : Site d → Prop}
    {S : Set (Site d)} {p : Site d} (hconn : xmh_SConn S) (hp : p ∈ S)
    (P : Finset (Site d)) {m k : ℕ} (hm : 1 ≤ m)
    (hsize : P.card + k ≤ m) (hS : (m : ℕ∞) ≤ S.encard)
    (hbad : ∀ x ∈ S, x ∉ P → ¬ G x) :
    ∃ F B : Finset (Site d), p ∈ F ∧ F.card = m ∧
      xmh_SConn (F : Set (Site d)) ∧ B ⊆ F ∧ B.card = k ∧ ∀ x ∈ B, ¬ G x := by
  classical
  obtain ⟨F, hpF, hFS, hFm, hFconn⟩ := xmh_grow hconn hp m hm hS
  have hcard : k ≤ (F \ P).card := by
    have h := Finset.card_le_card_sdiff_add_card (s := F) (t := P)
    omega
  obtain ⟨B, hB, hBk⟩ := Finset.exists_subset_card_eq hcard
  refine ⟨F, B, hpF, hFm, hFconn, hB.trans Finset.sdiff_subset, hBk, ?_⟩
  intro x hx
  have hx' := Finset.mem_sdiff.mp (hB hx)
  exact hbad x (hFS hx'.1) hx'.2

/-! ### The halo tail -/

/-- **Geometric tail of the halo of bad blocks.**  There is a threshold `ε₀ > 0`, depending only
on `d` and `r`, such that for every local predicate on blocks whose blocks are bad with
probability at most `ε₀`, the halo of bad blocks around a shortest reference set between two
blocks `x` and `y` has more than `(1 + (2r+1)^d) t` blocks with probability at most `2^{-t}`,
where `t = |x - y|₁ + 1`. -/
theorem predHalo_tail (d : ℕ) (hd : 1 ≤ d) (r : ℕ) :
    ∃ ε₀ : ℝ≥0∞, 0 < ε₀ ∧ ∀ {N : ℕ}, 0 < N → ∀ {q : ℝ}, 0 ≤ q → q ≤ 1 →
      ∀ {good : (Site d × Fin d → Bool) → Site d → Prop}, IsLocalBlockPredicate N r good →
      (∀ b, bondPercolation d q {ω | ¬ good ω b} ≤ ε₀) →
      ∀ x y : Site d, ∃ P : Finset (Site d), x ∈ P ∧ y ∈ P ∧ xmh_SConn (P : Set (Site d)) ∧
        bondPercolation d q
          {ω | (((1 + (2 * r + 1) ^ d) * ((mnorm (x - y)).toNat + 1) : ℕ) : ℕ∞) ≤
            (predHalo (good ω) P).encard} ≤
          (1 / 2 : ℝ≥0∞) ^ ((mnorm (x - y)).toNat + 1) := by
  classical
  obtain ⟨K, hK⟩ := marked_bad_block_animal_prob_le d
  set M : ℕ := (2 * r + 1) ^ d with hM
  have hMpos : 0 < M := by positivity
  set C : ℝ≥0∞ := ((K : ℝ≥0∞) * 2) ^ (1 + M) with hC
  have hCtop : C ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top K)
    ENNReal.ofNat_ne_top)
  refine ⟨(2 * (C + 1))⁻¹, ENNReal.inv_pos.mpr (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
    (ENNReal.add_ne_top.mpr ⟨hCtop, ENNReal.one_ne_top⟩)), ?_⟩
  intro N hN q hq0 hq1 good hloc hbad x y
  obtain ⟨P, hx, hy, hconn, _, hcard⟩ := exists_short_star_connected_set hd x y
  refine ⟨P, hx, hy, hconn, ?_⟩
  set t : ℕ := (mnorm (x - y)).toNat + 1 with ht
  have ht1 : 1 ≤ t := by omega
  have hsmall : C * (2 * (C + 1))⁻¹ ≤ 1 / 2 := by
    rw [ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), one_div]
    calc C * (2⁻¹ * (C + 1)⁻¹) = 2⁻¹ * (C * (C + 1)⁻¹) := by ring
      _ ≤ 2⁻¹ * 1 := by
        gcongr
        rw [← div_eq_mul_inv]
        exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact le_self_add)
      _ = 2⁻¹ := mul_one _
  have hsub : {ω : Site d × Fin d → Bool | (((1 + M) * t : ℕ) : ℕ∞) ≤
      (predHalo (good ω) P).encard} ⊆
      {ω | ∃ F B : Finset (Site d), x ∈ F ∧ F.card = (1 + M) * t ∧
        xmh_SConn (F : Set (Site d)) ∧ B ⊆ F ∧ B.card = M * t ∧ ∀ z ∈ B, ¬ good ω z} := by
    intro ω hω
    exact exists_marked_animal_of_connected_pred (predHalo_star_connected hconn)
      (subset_predHalo _ P hx) P (by nlinarith) (by nlinarith) hω
      (fun z hz hzP => not_of_mem_predHalo hz hzP)
  refine (measure_mono hsub).trans ((hK hN hq0 hq1 hloc hbad x ((1 + M) * t) (M * t)).trans ?_)
  have hdiv : M * t / M = t := by rw [Nat.mul_div_cancel_left t hMpos]
  rw [hdiv, ← mul_pow, pow_mul, ← mul_pow]
  refine pow_le_pow_left₀ zero_le ?_ t
  calc ((K : ℝ≥0∞) * 2) ^ (1 + M) * (2 * (C + 1))⁻¹ = C * (2 * (C + 1))⁻¹ := by rw [hC]
    _ ≤ 1 / 2 := hsmall

end Exploding
