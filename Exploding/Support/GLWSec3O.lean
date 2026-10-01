/-
Proposition 5.1 of the paper (generalized last wave): lighting a rectangle along a walk of tiles.

If a tile `c 0` of a walk of strongly box-crossing tiles is lit at time `τ`, all the tiles of the
walk are lit at time `τ + L ∏ k`.  Two sites `a, b` in tiles of the last stretch of the walk are
joined by a path of distinct sites inside that stretch, of at most `V` sites; if the path is long
enough for Hypothesis 5.3, the bounding rectangle of `a` and `b` is lit `V^d` steps later.
-/
import Exploding.Support.GLWSec3N

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

/-- The rectangle spanned by two sites lies in the bounding rectangle of any set containing
both. -/
theorem glws_box_subset_br (A : Set (Site d)) {a b : Site d} (ha : a ∈ A) (hb : b ∈ A)
    (w : Site d) (hw : ∀ m, min (a m) (b m) ≤ w m ∧ w m ≤ max (a m) (b m)) : w ∈ br A := by
  intro m
  obtain ⟨h1, h2⟩ := hw m
  refine ⟨?_, ?_⟩
  · rcases min_choice (a m) (b m) with h | h
    · rw [h] at h1; exact ⟨a, ha, h1⟩
    · rw [h] at h1; exact ⟨b, hb, h1⟩
  · rcases max_choice (a m) (b m) with h | h
    · rw [h] at h2; exact ⟨a, ha, h2⟩
    · rw [h] at h2; exact ⟨b, hb, h2⟩

/-- A tile has at most `(∑ k)^d` sites. -/
theorem glws_tile_ncard_le (k : Fin d → ℕ) (j : Site d) :
    (rboxShift k j).Finite ∧ (rboxShift k j).ncard ≤ (∑ i, k i) ^ d := by
  rw [glws_tile_eq_box]
  refine pclose_box_ncard_le _ _ _ fun i => ?_
  have : k i ≤ ∑ i, k i := Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)
  have h2 : ((k i : ℕ) : ℤ) ≤ ((∑ i, k i : ℕ) : ℤ) := by exact_mod_cast this
  push_cast at h2 ⊢
  linarith

/-- The union of the tiles over a stretch of a walk has at most `(L - L1 + 1) (∑ k)^d` sites. -/
theorem glws_stretch_ncard_le (k : Fin d → ℕ) (c : ℕ → Site d) (L1 L : ℕ) (hL : L1 ≤ L) :
    ({y | ∃ s, L1 ≤ s ∧ s ≤ L ∧ y ∈ rboxShift k (c s)} : Set (Site d)).Finite ∧
      ({y | ∃ s, L1 ≤ s ∧ s ≤ L ∧ y ∈ rboxShift k (c s)} : Set (Site d)).ncard ≤
        (L - L1 + 1) * (∑ i, k i) ^ d := by
  classical
  set F : Finset (Site d) := (Finset.Icc L1 L).biUnion
    (fun s => (glws_tile_ncard_le k (c s)).1.toFinset) with hF
  have hEq : ({y | ∃ s, L1 ≤ s ∧ s ≤ L ∧ y ∈ rboxShift k (c s)} : Set (Site d)) = ↑F := by
    ext y
    simp only [Set.mem_setOf_eq, hF, Finset.coe_biUnion, Finset.coe_Icc, Set.mem_iUnion,
      Set.mem_Icc, Finset.mem_coe, Set.Finite.mem_toFinset, exists_prop]
    constructor
    · rintro ⟨s, h1, h2, h3⟩
      exact ⟨s, ⟨h1, h2⟩, h3⟩
    · rintro ⟨s, ⟨h1, h2⟩, h3⟩
      exact ⟨s, h1, h2, h3⟩
  rw [hEq]
  refine ⟨Finset.finite_toSet _, ?_⟩
  rw [Set.ncard_coe_finset]
  calc F.card ≤ ∑ s ∈ Finset.Icc L1 L, ((glws_tile_ncard_le k (c s)).1.toFinset).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ Finset.Icc L1 L, (∑ i, k i) ^ d := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [← Set.ncard_eq_toFinset_card _ (glws_tile_ncard_le k (c s)).1]
        exact (glws_tile_ncard_le k (c s)).2
    _ = (L - L1 + 1) * (∑ i, k i) ^ d := by
        rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul]
        have : L + 1 - L1 = L - L1 + 1 := by omega
        rw [this]

/-- **Lighting a rectangle along a walk of tiles.** -/
theorem glws_light_box (hd : 2 ≤ d) (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (k : Fin d → ℕ) (hk : ∀ i, 0 < k i)
    (Cinf : Set (Site d)) (hgood : ∀ j ∈ Cinf, StronglyBoxCrossed η k j)
    (γp : ℝ) (hpf : glws_PF d γp η) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ (N : ℕ), 1 ≤ N → ∀ (zc : Site d) (L1 L : ℕ), L1 ≤ L →
      ∀ (c : ℕ → Site d), (∀ s, s ≤ L → c s ∈ Cinf) →
      (∀ s, s < L → (lattice d).Adj (c s) (c (s + 1))) → ∀ τ : ℕ,
      glws_Fired η N k zc τ (c 0) → ∀ (a b : Site d), a ∈ rboxShift k (c L1) →
      b ∈ rboxShift k (c L) →
      (∀ s, L1 ≤ s → s ≤ L → ∀ y ∈ rboxShift k (c s), y ∈ cent d n) →
      (∃ l₀ : Fin d, Real.log n ^ γp ≤ ((|a l₀ - b l₀| : ℤ) : ℝ) + 1) →
      ∀ w : Site d, (∀ m, min (a m) (b m) ≤ w m ∧ w m ≤ max (a m) (b m)) →
        0 < wave η N zc (τ + L * ∏ l, k l + ((L - L1 + 1) * (∑ i, k i) ^ d) ^ d) w := by
  classical
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  obtain ⟨n0, hfill⟩ := glws_pf_fill d γp η hd0 hlow hhigh hpf
  refine ⟨n0, fun n hn N hN zc L1 L hL1 c hcC hadj τ h0 a b ha hb hcent ⟨l₀, hlen⟩ w hw => ?_⟩
  -- all tiles of the walk are lit at time `τ + L ∏ k`
  have hfired := glws_walk_fires hd η hlow hhigh N hN k hk zc L c
    (fun s hs => hgood _ (hcC s hs)) hadj τ h0
  have hlit : ∀ s, s ≤ L → ∀ y ∈ rboxShift k (c s), 0 < wave η N zc (τ + L * ∏ l, k l) y := by
    intro s hs y hy
    have h1 := hfired s hs y hy
    refine pclose_pos_mono hd0 η hlow N zc ?_ h1
    have : s * ∏ l, k l ≤ L * ∏ l, k l := Nat.mul_le_mul_right _ hs
    omega
  -- the stretch of the walk
  set S : Set (Site d) := {y | ∃ s, L1 ≤ s ∧ s ≤ L ∧ y ∈ rboxShift k (c s)} with hS
  obtain ⟨hSfin, hScard⟩ := glws_stretch_ncard_le k c L1 L hL1
  have hSsub : ∀ s, L1 ≤ s → s ≤ L → rboxShift k (c s) ⊆ S :=
    fun s h1 h2 y hy => ⟨s, h1, h2, hy⟩
  have haS : a ∈ S := ⟨L1, le_rfl, hL1, ha⟩
  have hbS : b ∈ S := ⟨L, hL1, le_rfl, hb⟩
  have hbL : b ∈ rboxShift k (c (L1 + (L - L1))) := by rw [Nat.add_sub_cancel' hL1]; exact hb
  have hreach := glws_walk_reach k hk S c L1 L (fun s _ hs => hadj s hs) hSsub (L - L1)
    (by omega) a b ha hbL
  obtain ⟨m, z, hz0, hzm, hzS, hzinj, hzadj, hmcard⟩ := glws_path_of_reach S hSfin haS hbS hreach
  -- the path has at least `log n ^ γp` sites
  have hm_ge : |a l₀ - b l₀| ≤ (m : ℤ) := by
    have h1 := glws_path_coord z hzadj l₀ m le_rfl
    rw [hz0, hzm] at h1
    rw [abs_sub_comm]
    exact h1
  have hlenR : Real.log (n : ℝ) ^ γp ≤ ((m + 1 : ℕ) : ℝ) := by
    have : ((|a l₀ - b l₀| : ℤ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_ge
    push_cast
    linarith
  have hcentz : ∀ i, i < m + 1 → z i ∈ cent d n := by
    intro i hi
    obtain ⟨s, h1, h2, h3⟩ := hzS i (by omega)
    exact hcent s h1 h2 _ h3
  have hfillw := hfill N hN zc n hn (m + 1) z hlenR
    hcentz (fun i j hi hj hij => hzinj i j (by omega) (by omega) hij)
    (fun i hi => hzadj i (by omega)) (τ + L * ∏ l, k l)
    (fun i hi => ?_) w (glws_box_subset_br (z '' {i : ℕ | i < m + 1}) ⟨0, Nat.succ_pos m, hz0⟩ ⟨m, Nat.lt_succ_self m, hzm⟩ w hw)
  · -- monotone in time
    have hpow : (m + 1) ^ d ≤ ((L - L1 + 1) * (∑ i, k i) ^ d) ^ d :=
      Nat.pow_le_pow_left (le_trans hmcard hScard) d
    refine pclose_pos_mono hd0 η hlow N zc ?_ hfillw
    omega
  · obtain ⟨s, h1, h2, h3⟩ := hzS i (by omega)
    exact hlit s h2 _ h3

end Exploding
