/-
Proposition 5.1 of the paper (generalized last wave): the lighting of the tiles around a target from
a lit tile of `C_∞` (the generalized spreading step of Lemmas 3.6 and 3.7).

If the tile `j ∈ C_∞` is lit by an `N`-wave at time `τ`, then for `n` large every site in the tiles
within macroscopic distance `Z = ⌈(log n)^{γ_p + 5}⌉` of a macroscopic site `ν` is lit by time
`τ + A (|j| + |ν|) + B Z^d`, where `A, B` depend on the tile sizes and the chemical-distance constant
only.  The proof finds, by the hole estimate on two rows of macroscopic sites, points `M_-` and
`M_+` of `C_∞` on either side of the target; one is far from `j`; the chemical distance bound gives
walks of `C_∞` to it and from it to the other; the second walk contains a path of distinct sites
whose bounding rectangle covers the target, which is lit by path-filling.
-/
import Exploding.Support.GLWSec3R

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

/-- The corners of two tiles on either side of a box cover the box coordinatewise. -/
theorem glws_cover (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (ν : Site d) (Z : ℕ) (Mlo Mhi : Site d)
    (hlo : ∀ m, Mlo m ≤ ν m - (Z : ℤ) - 1) (hhi : ∀ m, ν m + (Z : ℤ) + 1 ≤ Mhi m) (m : Fin d) :
    min (glws_corner k Mlo m) (glws_corner k Mhi m) ≤ (k m : ℤ) * (ν m - Z) + 1 ∧
      (k m : ℤ) * (ν m + Z + 1) ≤ max (glws_corner k Mlo m) (glws_corner k Mhi m) := by
  have hk1 : (1 : ℤ) ≤ (k m : ℤ) := by exact_mod_cast hk m
  simp only [glws_corner]
  constructor
  · refine le_trans (min_le_left _ _) ?_
    have := mul_le_mul_of_nonneg_left (hlo m) (by linarith : (0 : ℤ) ≤ (k m : ℤ))
    nlinarith
  · refine le_trans ?_ (le_max_right _ _)
    have := mul_le_mul_of_nonneg_left (hhi m) (by linarith : (0 : ℤ) ≤ (k m : ℤ))
    nlinarith

/-- The sites of the second walk stay in the box of radius `2 n` (arithmetic). -/
theorem glws_walk_size (n Cn d Λ m2 s : ℕ) (x Mf : ℤ) (hx : x ≤ (s : ℤ) + Mf)
    (hMf : Mf ≤ (n : ℤ) + (d : ℤ) * Λ) (hs : s ≤ m2) (hm2 : m2 ≤ Cn * (d * (2 * Λ)))
    (hsize : (1 + 2 * Cn) * d * Λ ≤ n) : x ≤ ((2 * n : ℕ) : ℤ) := by
  have h1 : (s : ℤ) ≤ ((Cn * (d * (2 * Λ)) : ℕ) : ℤ) := by exact_mod_cast le_trans hs hm2
  have h2 : (((1 + 2 * Cn) * d * Λ : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast hsize
  push_cast at h1 h2 ⊢
  have h3 : (Cn : ℤ) * ((d : ℤ) * (2 * (Λ : ℤ))) + (d : ℤ) * (Λ : ℤ) =
      (1 + 2 * (Cn : ℤ)) * (d : ℤ) * (Λ : ℤ) := by ring
  linarith

theorem glws_scale_le (kmax n : ℕ) (x : ℤ) (hx : x ≤ ((2 * n : ℕ) : ℤ)) :
    (kmax : ℤ) * (x + 1) ≤ ((kmax * (2 * n + 1) : ℕ) : ℤ) := by
  push_cast at hx ⊢
  have : (0 : ℤ) ≤ (kmax : ℤ) := Int.natCast_nonneg _
  nlinarith

/-- **The key step of the spreading.**  Given two points `M_f, M_o` of the cluster on either side
of the target, within the offset `Λ = Z + 1 + r`, the first far from the lit tile, the tiles around
the target are lit. -/
theorem glws_light_near_key (hd : 2 ≤ d) (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (k : Fin d → ℕ) (hk : ∀ i, 0 < k i)
    (Cinf : Set (Site d)) (hgood : ∀ j ∈ Cinf, StronglyBoxCrossed η k j)
    (Cch : ℝ) (hCch : 0 ≤ Cch) (n0c : ℕ)
    (hchem : ∀ n : ℕ, n0c ≤ n → ∀ x ∈ Cinf, ∀ y ∈ Cinf, mnorm x ≤ (n : ℤ) →
      Real.log n ^ (2 : ℕ) ≤ (mnorm (x - y) : ℝ) →
      ∃ m : ℕ, chemDist Cinf x y = (m : ℕ∞) ∧ (m : ℝ) ≤ Cch * (mnorm (x - y) : ℝ))
    (γp : ℝ) (hγp : 0 < γp) (hpf : glws_PF d γp η) (l₁ : Fin d) :
    ∃ A B n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ (N : ℕ), 1 ≤ N → ∀ (zc : Site d) (τ : ℕ) (j : Site d),
      j ∈ Cinf → mnorm j ≤ (n : ℤ) → glws_Fired η N k zc τ j → ∀ ν : Site d,
      mnorm ν ≤ (n : ℤ) → ∀ y : Site d,
      (∀ m, (k m : ℤ) * (ν m - (glws_Zn γp n : ℤ)) + 1 ≤ y m ∧
        y m ≤ (k m : ℤ) * (ν m + (glws_Zn γp n : ℤ) + 1)) →
      ∀ Mf Mo : Site d, Mf ∈ Cinf → Mo ∈ Cinf →
      ((glws_Zn γp n : ℤ) + 1 ≤ mnorm (j - Mf)) →
      ((2 * glws_Zn γp n + 2 : ℤ) ≤ |Mf l₁ - Mo l₁|) →
      (∀ m, |Mf m - ν m| ≤ ((glws_Zn γp n + 1 + glws_rn n : ℕ) : ℤ)) →
      (∀ m, |Mo m - ν m| ≤ ((glws_Zn γp n + 1 + glws_rn n : ℕ) : ℤ)) →
      (∀ m, min (glws_corner k Mf m) (glws_corner k Mo m) ≤
          (k m : ℤ) * (ν m - (glws_Zn γp n : ℤ)) + 1 ∧
        (k m : ℤ) * (ν m + (glws_Zn γp n : ℤ) + 1) ≤
          max (glws_corner k Mf m) (glws_corner k Mo m)) →
      0 < wave η N zc (τ + A * ((mnorm j).toNat + (mnorm ν).toNat) + B * (glws_Zn γp n) ^ d) y := by
  classical
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  have hdpos : 0 < d := by omega
  set kmax : ℕ := ∑ i, k i with hkmax
  set K : ℕ := ∏ l, k l with hK
  set Cn : ℕ := ⌈Cch⌉₊ with hCn
  have hCnR : Cch ≤ (Cn : ℝ) := Nat.le_ceil Cch
  have hkmax1 : 1 ≤ kmax := le_trans (hk l₁)
    (Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l₁))
  obtain ⟨n1, hasym⟩ := glws_asymp_ln γp hγp kmax Cn d
  obtain ⟨n0lc, hcore⟩ := glws_light_near_core hd η hlow hhigh k hk Cinf hgood γp hpf
  refine ⟨Cn * K, 9 * Cn * K * d + ((6 * Cn * d + 1) * kmax ^ d) ^ d,
    max (max n1 n0c) n0lc, ?_⟩
  intro n hn N hN zc τ j hj hjn hfired ν hνn y hy Mf Mo hMf hMo hfj hfo hMfν hMoν hcov
  have hn1 : n1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn0c : n0c ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn0lc : n0lc ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨h2n, hZ1, hrZ, hfar, hsize, hPF⟩ := hasym n hn1
  set Z : ℕ := glws_Zn γp n with hZ
  set r : ℕ := glws_rn n with hr
  set Λ : ℕ := Z + 1 + r with hΛ
  have hΛ3 : Λ ≤ 3 * Z := by omega
  have hdΛ : d * Λ ≤ n := by
    refine le_trans ?_ hsize
    calc d * Λ = 1 * d * Λ := by ring
      _ ≤ (1 + 2 * Cn) * d * Λ := by
        apply Nat.mul_le_mul_right
        apply Nat.mul_le_mul_right
        omega
  have hjnn : 0 ≤ mnorm j := by unfold mnorm; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hνnn : 0 ≤ mnorm ν := by unfold mnorm; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hn2 : (n : ℤ) ≤ ((2 * n : ℕ) : ℤ) := by push_cast; omega
  -- sizes
  have hMfn : mnorm Mf ≤ mnorm ν + (d : ℤ) * Λ := by
    have h1 : Mf = ν + (Mf - ν) := by abel
    calc mnorm Mf = mnorm (ν + (Mf - ν)) := by rw [← h1]
      _ ≤ mnorm ν + mnorm (Mf - ν) := glw2_mnorm_add_le _ _
      _ ≤ mnorm ν + (d : ℤ) * Λ := add_le_add le_rfl (glws_mnorm_le_coord _ _ hMfν)
  have hMfMo : mnorm (Mf - Mo) ≤ (d : ℤ) * (2 * Λ) := by
    refine glws_mnorm_le_coord _ _ (fun m => ?_)
    have h1 : Mf m - Mo m = (Mf m - ν m) + (ν m - Mo m) := by ring
    have h2 : |ν m - Mo m| ≤ (Λ : ℤ) := by rw [abs_sub_comm]; exact hMoν m
    simp only [Pi.sub_apply]
    calc |Mf m - Mo m| = |(Mf m - ν m) + (ν m - Mo m)| := by rw [← h1]
      _ ≤ |Mf m - ν m| + |ν m - Mo m| := abs_add_le _ _
      _ ≤ 2 * (Λ : ℤ) := by linarith [hMfν m]
  have hdΛz : (d : ℤ) * Λ ≤ n := by exact_mod_cast hdΛ
  have hfar' : Real.log ((2 * n : ℕ) : ℝ) ^ (2 : ℕ) ≤ ((Z : ℤ) + 1 : ℤ) := by
    have : ((Z : ℝ) + 1) = (((Z : ℤ) + 1 : ℤ) : ℝ) := by push_cast; ring
    rw [← this]; exact hfar
  have hjMf : Real.log ((2 * n : ℕ) : ℝ) ^ (2 : ℕ) ≤ (mnorm (j - Mf) : ℝ) := by
    refine le_trans hfar' ?_
    exact_mod_cast hfj
  have hMfMo' : Real.log ((2 * n : ℕ) : ℝ) ^ (2 : ℕ) ≤ (mnorm (Mf - Mo) : ℝ) := by
    refine le_trans hfar' ?_
    have h1 : |Mf l₁ - Mo l₁| ≤ mnorm (Mf - Mo) := by
      have := abs_coord_le_mnorm (Mf - Mo) l₁
      simpa using this
    have : ((Z : ℤ) + 1) ≤ mnorm (Mf - Mo) := by linarith
    exact_mod_cast this
  obtain ⟨m1, hm1, hm1b⟩ := hchem (2 * n) (by omega) j hj Mf hMf
    (by exact le_trans hjn hn2) hjMf
  obtain ⟨m2, hm2, hm2b⟩ := hchem (2 * n) (by omega) Mf hMf Mo hMo
    (by
      have : mnorm ν + (d : ℤ) * Λ ≤ ((2 * n : ℕ) : ℤ) := by push_cast; linarith
      exact le_trans hMfn this) hMfMo'
  obtain ⟨c1, hc10, hc1m, hc1S, hc1adj⟩ := pclose_chem_walk Cinf j Mf m1 hm1
  obtain ⟨c2, hc20, hc2m, hc2S, hc2adj⟩ := pclose_chem_walk Cinf Mf Mo m2 hm2
  -- the bounds on the lengths of the walks
  have hm1N : m1 ≤ Cn * ((mnorm j).toNat + (mnorm ν).toNat + d * Λ) := by
    have h1 : mnorm (j - Mf) ≤ mnorm j + mnorm Mf := glw2_mnorm_sub_le _ _
    have h2 : mnorm (j - Mf) ≤ ((mnorm j).toNat : ℤ) + ((mnorm ν).toNat : ℤ) + (d : ℤ) * Λ := by
      have e1 : (((mnorm j).toNat : ℕ) : ℤ) = mnorm j := Int.toNat_of_nonneg hjnn
      have e2 : (((mnorm ν).toNat : ℕ) : ℤ) = mnorm ν := Int.toNat_of_nonneg hνnn
      have : mnorm ν ≤ mnorm ν := le_rfl
      linarith
    have h3 : (mnorm (j - Mf) : ℝ) ≤ (((mnorm j).toNat + (mnorm ν).toNat + d * Λ : ℕ) : ℝ) := by
      have : (mnorm (j - Mf)) ≤ (((mnorm j).toNat + (mnorm ν).toNat + d * Λ : ℕ) : ℤ) := by
        push_cast; exact h2
      exact_mod_cast this
    have h4 : (m1 : ℝ) ≤ (Cn : ℝ) * (((mnorm j).toNat + (mnorm ν).toNat + d * Λ : ℕ) : ℝ) := by
      calc (m1 : ℝ) ≤ Cch * (mnorm (j - Mf) : ℝ) := hm1b
        _ ≤ Cch * (((mnorm j).toNat + (mnorm ν).toNat + d * Λ : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left h3 hCch
        _ ≤ (Cn : ℝ) * (((mnorm j).toNat + (mnorm ν).toNat + d * Λ : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right hCnR (Nat.cast_nonneg _)
    exact_mod_cast h4
  have hm2N : m2 ≤ Cn * (d * (2 * Λ)) := by
    have h3 : (mnorm (Mf - Mo) : ℝ) ≤ ((d * (2 * Λ) : ℕ) : ℝ) := by
      have : mnorm (Mf - Mo) ≤ ((d * (2 * Λ) : ℕ) : ℤ) := by push_cast; exact hMfMo
      exact_mod_cast this
    have h4 : (m2 : ℝ) ≤ (Cn : ℝ) * ((d * (2 * Λ) : ℕ) : ℝ) := by
      calc (m2 : ℝ) ≤ Cch * (mnorm (Mf - Mo) : ℝ) := hm2b
        _ ≤ Cch * ((d * (2 * Λ) : ℕ) : ℝ) := mul_le_mul_of_nonneg_left h3 hCch
        _ ≤ (Cn : ℝ) * ((d * (2 * Λ) : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right hCnR (Nat.cast_nonneg _)
    exact_mod_cast h4
  -- the second walk stays in the box of radius `2n`
  have hcent : ∀ s, s ≤ m2 → ∀ y' ∈ rboxShift k (c2 s), y' ∈ cent d (kmax * (2 * n + 1)) := by
    intro s hs y' hy' m
    have h1 := glws_tile_coord_le k hk (c2 s) y' hy' m
    have h2 : mnorm (c2 s) ≤ ((2 * n : ℕ) : ℤ) := by
      have h3 := glws_walk_mnorm c2 hc2adj s hs
      rw [hc20] at h3
      have h4 : mnorm (c2 s) ≤ mnorm (c2 s - Mf) + mnorm Mf := by
        have := glw2_mnorm_add_le (c2 s - Mf) Mf
        simpa using this
      have hMfn' : mnorm Mf ≤ (n : ℤ) + (d : ℤ) * Λ := by linarith
      have h6 : (1 + 2 * Cn) * d * Λ ≤ n := hsize
      have hMfn' : mnorm Mf ≤ (n : ℤ) + (d : ℤ) * Λ := by linarith
      exact glws_walk_size n Cn d Λ m2 s _ _ (by linarith) hMfn' hs hm2N h6
    exact le_trans h1 (glws_scale_le kmax n _ h2)
  -- the length of the path
  have hlen : ∃ l₀ : Fin d, Real.log ((kmax * (2 * n + 1) : ℕ) : ℝ) ^ γp ≤
      ((|glws_corner k Mf l₀ - glws_corner k Mo l₀| : ℤ) : ℝ) + 1 := by
    refine ⟨l₁, ?_⟩
    have h1 : |glws_corner k Mf l₁ - glws_corner k Mo l₁| =
        (k l₁ : ℤ) * |Mf l₁ - Mo l₁| := by
      simp only [glws_corner]
      rw [show 1 + (k l₁ : ℤ) * Mf l₁ - (1 + (k l₁ : ℤ) * Mo l₁) =
        (k l₁ : ℤ) * (Mf l₁ - Mo l₁) by ring, abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
    have hkl : (1 : ℤ) ≤ (k l₁ : ℤ) := by exact_mod_cast hk l₁
    have h2 : |Mf l₁ - Mo l₁| ≤ |glws_corner k Mf l₁ - glws_corner k Mo l₁| := by
      rw [h1]; nlinarith [abs_nonneg (Mf l₁ - Mo l₁)]
    have h3 : (2 * (Z : ℤ) + 2) ≤ |glws_corner k Mf l₁ - glws_corner k Mo l₁| := le_trans hfo h2
    have h4 : (2 * (Z : ℝ) + 2) ≤ ((|glws_corner k Mf l₁ - glws_corner k Mo l₁| : ℤ) : ℝ) := by
      exact_mod_cast h3
    linarith
  -- the lighting
  have hbox : ∀ m, min (glws_corner k Mf m) (glws_corner k Mo m) ≤ y m ∧
      y m ≤ max (glws_corner k Mf m) (glws_corner k Mo m) :=
    fun m => ⟨le_trans (hcov m).1 (hy m).1, le_trans (hy m).2 (hcov m).2⟩
  have hnm : n0lc ≤ kmax * (2 * n + 1) :=
    le_trans hn0lc (le_trans (by omega : n ≤ 2 * n + 1) (Nat.le_mul_of_pos_left _ hkmax1))
  have hlit := hcore (kmax * (2 * n + 1)) hnm N hN zc τ j hfired Mf Mo m1 m2 c1 c2
    hc10 hc1m hc1S hc1adj hc20 hc2m hc2S hc2adj (glws_corner k Mf) (glws_corner k Mo)
    (glws_corner_mem k hk Mf) (glws_corner_mem k hk Mo) hcent hlen y hbox
  have harith := glws_time_arith Cn K d kmax Z Λ m1 m2 (mnorm j).toNat (mnorm ν).toNat hdpos hZ1
    hΛ3 hm1N hm2N
  have hd0' : (0 : ℤ) < 2 * (d : ℤ) := hd0
  have hmono := pclose_pos_mono hd0' η hlow N zc
    (show τ + (m1 + m2) * ∏ l, k l + ((m2 + 1) * (∑ i, k i) ^ d) ^ d ≤
      τ + (Cn * K) * ((mnorm j).toNat + (mnorm ν).toNat) +
      (9 * Cn * K * d + ((6 * Cn * d + 1) * kmax ^ d) ^ d) * Z ^ d by
      have := harith
      simp only [hK, hkmax] at this ⊢
      omega) hlit
  exact hmono

/-- **The generalized spreading step.** -/
theorem glws_light_near (hd : 2 ≤ d) (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (k : Fin d → ℕ) (hk : ∀ i, 0 < k i)
    (Cinf : Set (Site d)) (hgood : ∀ j ∈ Cinf, StronglyBoxCrossed η k j)
    (n0h : ℕ) (hole : ∀ n : ℕ, n0h ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf →
      (componentIn Cinfᶜ x).Finite ∧ ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2))
    (Cch : ℝ) (hCch : 0 ≤ Cch) (n0c : ℕ)
    (hchem : ∀ n : ℕ, n0c ≤ n → ∀ x ∈ Cinf, ∀ y ∈ Cinf, mnorm x ≤ (n : ℤ) →
      Real.log n ^ (2 : ℕ) ≤ (mnorm (x - y) : ℝ) →
      ∃ m : ℕ, chemDist Cinf x y = (m : ℕ∞) ∧ (m : ℝ) ≤ Cch * (mnorm (x - y) : ℝ))
    (γp : ℝ) (hγp : 0 < γp) (hpf : glws_PF d γp η) :
    ∃ A B n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ (N : ℕ), 1 ≤ N → ∀ (zc : Site d) (τ : ℕ) (j : Site d),
      j ∈ Cinf → mnorm j ≤ (n : ℤ) → glws_Fired η N k zc τ j → ∀ ν : Site d,
      mnorm ν ≤ (n : ℤ) → ∀ y : Site d,
      (∀ m, (k m : ℤ) * (ν m - (glws_Zn γp n : ℤ)) + 1 ≤ y m ∧
        y m ≤ (k m : ℤ) * (ν m + (glws_Zn γp n : ℤ) + 1)) →
      0 < wave η N zc (τ + A * ((mnorm j).toNat + (mnorm ν).toNat) + B * (glws_Zn γp n) ^ d) y := by
  classical
  have hdpos : 0 < d := by omega
  set kmax : ℕ := ∑ i, k i with hkmax
  set Cn : ℕ := ⌈Cch⌉₊ with hCn
  set l₁ : Fin d := ⟨0, hdpos⟩ with hl₁
  obtain ⟨n1, hasym⟩ := glws_asymp_ln γp hγp kmax Cn d
  obtain ⟨A, B, n0k, hkey⟩ := glws_light_near_key hd η hlow hhigh k hk Cinf hgood Cch hCch n0c
    hchem γp hγp hpf l₁
  refine ⟨A, B, max (max n1 n0h) (max n0k n0c), ?_⟩
  intro n hn N hN zc τ j hj hjn hfired ν hνn y hy
  have hn1 : n1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn0h : n0h ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn0k : n0k ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  obtain ⟨h2n, hZ1, hrZ, hfar, hsize, hPF⟩ := hasym n hn1
  set Z : ℕ := glws_Zn γp n with hZ
  set r : ℕ := glws_rn n with hr
  set Λ : ℕ := Z + 1 + r with hΛ
  have hΛ3 : Λ ≤ 3 * Z := by omega
  have hdΛ : d * Λ ≤ n := by
    refine le_trans ?_ hsize
    calc d * Λ = 1 * d * Λ := by ring
      _ ≤ (1 + 2 * Cn) * d * Λ := by
        apply Nat.mul_le_mul_right
        apply Nat.mul_le_mul_right
        omega
  -- the two rows of macroscopic sites on either side of the target
  have hΛn : Λ ≤ n := le_trans (Nat.le_mul_of_pos_left Λ hdpos) hdΛ
  have hr_le : Real.log ((n + Λ : ℕ) : ℝ) ^ ((5 : ℝ) / 2) ≤ (r : ℝ) := by
    have h1 : Real.log ((2 * n : ℕ) : ℝ) ^ ((5 : ℝ) / 2) ≤ (r : ℝ) := Nat.le_ceil _
    refine le_trans ?_ h1
    have hpos : (0 : ℝ) < ((n + Λ : ℕ) : ℝ) := by
      have : 0 < n + Λ := by omega
      exact_mod_cast this
    have hle : ((n + Λ : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
      have : n + Λ ≤ 2 * n := by omega
      exact_mod_cast this
    exact Real.rpow_le_rpow (Real.log_nonneg (by
      have : (1 : ℝ) ≤ ((n + Λ : ℕ) : ℝ) := by
        have : 1 ≤ n + Λ := by omega
        exact_mod_cast this
      exact this)) (Real.log_le_log hpos hle) (by norm_num)
  have hrowc : ∀ β : Site d, (∀ m, ν m - (Λ : ℤ) ≤ β m ∧ β m + (r : ℤ) ≤ ν m + Λ) →
      ∀ t : ℕ, t ≤ r → β + (t : ℤ) • unit l₁ ∈ cent d (n + Λ) := by
    intro β hβ t ht m
    have h1 := hβ m
    have h2 : (β + (t : ℤ) • unit l₁) m = β m + (t : ℤ) * (if m = l₁ then 1 else 0) := by
      simp [glws_unit_apply]
    have h3 : (0 : ℤ) ≤ (t : ℤ) * (if m = l₁ then 1 else 0) := by
      split_ifs <;> simp
    have h4 : (t : ℤ) * (if m = l₁ then 1 else 0) ≤ (r : ℤ) := by
      have : (t : ℤ) ≤ r := by exact_mod_cast ht
      split_ifs
      · linarith
      · simp
    have h5 := abs_coord_le_mnorm ν m
    have h6 : |ν m| ≤ (n : ℤ) := le_trans h5 hνn
    rw [abs_le] at h6 ⊢
    rw [h2]
    push_cast
    constructor <;> linarith [h1.1, h1.2, h6.1, h6.2]
  have hrow : ∀ β : Site d, (∀ m, ν m - (Λ : ℤ) ≤ β m ∧ β m + (r : ℤ) ≤ ν m + Λ) →
      ∃ t : ℕ, t ≤ r ∧ β + (t : ℤ) • unit l₁ ∈ Cinf := fun β hβ =>
    glws_row_hole Cinf (n + Λ) (hole (n + Λ) (by omega)) l₁ β r hr_le (hrowc β hβ)
  have hcoord : ∀ (β : Site d) (t : ℕ), t ≤ r → ∀ m,
      β m ≤ (β + (t : ℤ) • unit l₁) m ∧ (β + (t : ℤ) • unit l₁) m ≤ β m + (r : ℤ) := by
    intro β t ht m
    have h2 : (β + (t : ℤ) • unit l₁) m = β m + (t : ℤ) * (if m = l₁ then 1 else 0) := by
      simp [glws_unit_apply]
    have h3 : (0 : ℤ) ≤ (t : ℤ) * (if m = l₁ then 1 else 0) := by
      split_ifs <;> simp
    have h4 : (t : ℤ) * (if m = l₁ then 1 else 0) ≤ (r : ℤ) := by
      have : (t : ℤ) ≤ r := by exact_mod_cast ht
      split_ifs
      · linarith
      · simp
    rw [h2]
    constructor <;> linarith
  have hΛz : (Λ : ℤ) = (Z : ℤ) + 1 + r := by simp [hΛ]
  obtain ⟨tm, htm, hMm⟩ := hrow (fun m => ν m - (Λ : ℤ)) (fun m => by
    constructor
    · exact le_rfl
    · linarith)
  obtain ⟨tp, htp, hMp⟩ := hrow (fun m => ν m + ((Z : ℤ) + 1)) (fun m => by
    constructor
    · linarith [(Int.natCast_nonneg Z), (Int.natCast_nonneg r)]
    · linarith)
  set Mm : Site d := (fun m => ν m - (Λ : ℤ)) + (tm : ℤ) • unit l₁ with hMmdef
  set Mp : Site d := (fun m => ν m + ((Z : ℤ) + 1)) + (tp : ℤ) • unit l₁ with hMpdef
  have hMm1 : ∀ m, ν m - (Λ : ℤ) ≤ Mm m ∧ Mm m ≤ ν m - (Z : ℤ) - 1 := by
    intro m
    have := hcoord (fun m => ν m - (Λ : ℤ)) tm htm m
    constructor <;> linarith [this.1, this.2]
  have hMp1 : ∀ m, ν m + (Z : ℤ) + 1 ≤ Mp m ∧ Mp m ≤ ν m + Λ := by
    intro m
    have := hcoord (fun m => ν m + ((Z : ℤ) + 1)) tp htp m
    constructor <;> linarith [this.1, this.2]
  have hMmν : ∀ m, |Mm m - ν m| ≤ (Λ : ℤ) := by
    intro m
    have := hMm1 m
    rw [abs_le]
    constructor <;> linarith [this.1, this.2, Int.natCast_nonneg Z, Int.natCast_nonneg r]
  have hMpν : ∀ m, |Mp m - ν m| ≤ (Λ : ℤ) := by
    intro m
    have := hMp1 m
    rw [abs_le]
    constructor <;> linarith [this.1, this.2, Int.natCast_nonneg Z, Int.natCast_nonneg r]
  have hgap : (2 * (Z : ℤ) + 2) ≤ Mp l₁ - Mm l₁ := by
    have h1 := (hMm1 l₁).2
    have h2 := (hMp1 l₁).1
    linarith
  have hfo : (2 * (Z : ℤ) + 2) ≤ |Mm l₁ - Mp l₁| := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    exact hgap
  have hfo' : (2 * (Z : ℤ) + 2) ≤ |Mp l₁ - Mm l₁| := by
    rw [abs_of_nonneg (by linarith)]
    exact hgap
  have hcov := glws_cover k hk ν Z Mm Mp (fun m => (hMm1 m).2) (fun m => (hMp1 m).1)
  by_cases hcase : (Z : ℤ) + 1 ≤ mnorm (j - Mm)
  · exact hkey n hn0k N hN zc τ j hj hjn hfired ν hνn y hy Mm Mp hMm hMp hcase hfo hMmν hMpν hcov
  · -- then `M_+` is far from `j`
    have hcase' : (Z : ℤ) + 1 ≤ mnorm (j - Mp) := by
      have h1 : mnorm (Mp - Mm) ≥ 2 * (Z : ℤ) + 2 := by
        have := abs_coord_le_mnorm (Mp - Mm) l₁
        simp only [Pi.sub_apply] at this
        rw [abs_of_nonneg (by linarith)] at this
        linarith
      have h2 : mnorm (Mp - Mm) ≤ mnorm (Mp - j) + mnorm (j - Mm) := pub_mnorm_sub_le Mp j Mm
      have h3 : mnorm (j - Mp) = mnorm (Mp - j) := pub_mnorm_sub_comm j Mp
      push Not at hcase
      linarith
    refine hkey n hn0k N hN zc τ j hj hjn hfired ν hνn y hy Mp Mm hMp hMm hcase' hfo' hMpν hMmν ?_
    intro m
    have := hcov m
    rw [min_comm, max_comm]
    exact this

end Exploding
