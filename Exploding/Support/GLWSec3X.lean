/-
Proposition 5.1 of the paper (generalized last wave): the macroscopic site of a microscopic site,
and the lit tile near a lit site far from the origin.

If the last wave is positive at `x`, `x` far from the origin, the last stretch of the path joining
`x` to the origin is a long lit path, so a tile of `C_∞` within a polylogarithmic distance of `x` is
lit a polylogarithmic time later.
-/
import Exploding.Support.GLWSec3W

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

/-- The macroscopic site of a microscopic site: the index of the tile containing it. -/
def glws_nu (k : Fin d → ℕ) (x : Site d) : Site d := fun m => (x m - 1) / (k m : ℤ)

theorem glws_mem_tile_nu (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (x : Site d) :
    x ∈ rboxShift k (glws_nu k x) := by
  intro m
  obtain ⟨h1, h2⟩ := glws_floor_div (x m - 1) (k m) (hk m)
  simp only [glws_nu]
  constructor <;> linarith

theorem glws_nu_abs (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (x : Site d) (m : Fin d) :
    |glws_nu k x m| ≤ |x m| + 1 := by
  simp only [glws_nu]
  exact pclose_ediv_abs (x m) (k m) (hk m)

theorem glws_nu_lip (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (x y : Site d) (m : Fin d) :
    |glws_nu k x m - glws_nu k y m| ≤ |x m - y m| := by
  simp only [glws_nu]
  obtain ⟨h1, h2⟩ := glws_floor_div (x m - 1) (k m) (hk m)
  obtain ⟨g1, g2⟩ := glws_floor_div (y m - 1) (k m) (hk m)
  set u := (x m - 1) / (k m : ℤ) with hu
  set v := (y m - 1) / (k m : ℤ) with hv
  have hk1 : (1 : ℤ) ≤ (k m : ℤ) := by exact_mod_cast hk m
  -- `k (u - v)` is within `k` of `x m - y m`
  have e1 : (k m : ℤ) * (u - v) < (x m - y m) + k m := by nlinarith
  have e2 : (x m - y m) - k m < (k m : ℤ) * (u - v) := by nlinarith
  by_contra hcon
  push Not at hcon
  have hcon' : |x m - y m| + 1 ≤ |u - v| := by
    have := Int.add_one_le_iff.mpr hcon
    exact this
  rcases le_total 0 (u - v) with h | h
  · rw [abs_of_nonneg h] at hcon'
    have : (k m : ℤ) * (|x m - y m| + 1) ≤ (k m : ℤ) * (u - v) :=
      mul_le_mul_of_nonneg_left hcon' (by linarith)
    nlinarith [le_abs_self (x m - y m), abs_nonneg (x m - y m)]
  · rw [abs_of_nonpos h] at hcon'
    have : (k m : ℤ) * (|x m - y m| + 1) ≤ (k m : ℤ) * (-(u - v)) :=
      mul_le_mul_of_nonneg_left hcon' (by linarith)
    nlinarith [neg_abs_le (x m - y m), abs_nonneg (x m - y m)]

theorem glws_nu_corner (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (j : Site d) :
    glws_nu k (glws_corner k j) = j := by
  funext m
  simp only [glws_nu, glws_corner]
  have hk0 : (k m : ℤ) ≠ 0 := by exact_mod_cast (hk m).ne'
  rw [show 1 + (k m : ℤ) * j m - 1 = (k m : ℤ) * j m by ring]
  exact Int.mul_ediv_cancel_left _ hk0

theorem glws_mnorm_nu_lip (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (x y : Site d) :
    mnorm (glws_nu k x - glws_nu k y) ≤ mnorm (x - y) := by
  unfold mnorm
  refine Finset.sum_le_sum fun m _ => ?_
  simp only [Pi.sub_apply]
  exact glws_nu_lip k hk x y m

/-- Along a path of adjacent sites, a site `q` steps before the end is within `q` of the end. -/
theorem glws_path_coord_rev {m : ℕ} (z : ℕ → Site d)
    (hadj : ∀ i, i < m → (lattice d).Adj (z i) (z (i + 1))) (l : Fin d) :
    ∀ q, q ≤ m → |z (m - q) l - z m l| ≤ q := by
  intro q
  induction q with
  | zero => intro _; simp
  | succ q ih =>
    intro hq
    have h1 := ih (by omega)
    have h2 := glws_adj_coord (hadj (m - (q + 1)) (by omega)) l
    have e : m - (q + 1) + 1 = m - q := by omega
    rw [e] at h2
    have h3 : |z (m - (q + 1)) l - z m l| ≤ |z (m - q) l - z (m - (q + 1)) l| +
        |z (m - q) l - z m l| := by
      have := abs_add_le (z (m - (q + 1)) l - z (m - q) l) (z (m - q) l - z m l)
      rw [abs_sub_comm (z (m - (q + 1)) l) (z (m - q) l)] at this
      simpa using this
    push_cast
    linarith

/-- **The lit tile near a lit site far from the origin.** -/
theorem glws_tail_tile (hd : 2 ≤ d) (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (k : Fin d → ℕ) (hk : ∀ i, 0 < k i)
    (Cinf : Set (Site d)) (hgood : ∀ j ∈ Cinf, StronglyBoxCrossed η k j)
    (n0h : ℕ) (hole : ∀ n : ℕ, n0h ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf →
      (componentIn Cinfᶜ x).Finite ∧ ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2))
    (γp : ℝ) (hγp : 0 < γp) (hpf : glws_PF d γp η) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ (N : ℕ), 1 ≤ N → ∀ x ∈ (cent d n : Set (Site d)),
      glws_Pn γp (∑ i, k i) d n ≤ (mnorm x).toNat → ∀ t : ℕ, 0 < wave η N (0 : Site d) t x →
      ∃ j ∈ Cinf, glws_Fired η N k 0 (t + (glws_Pn γp (∑ i, k i) d n) ^ d + ∏ l, k l) j ∧
        mnorm (j - glws_nu k x) ≤
          (d : ℤ) * (2 * (glws_Pn γp (∑ i, k i) d n : ℤ) + ((∑ i, k i : ℕ) : ℤ)) := by
  classical
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  set kmax : ℕ := ∑ i, k i with hkmax
  obtain ⟨n0pt, hpt⟩ := glws_path_to_tile hd η hlow hhigh k hk Cinf hgood n0h hole γp hpf
  obtain ⟨n1, hn1⟩ := glws_asymp_Pn γp hγp kmax d
  refine ⟨max n1 n0pt, fun n hn N hN x hx hPx t hpos => ?_⟩
  have hn1' : n1 ≤ n := le_trans (le_max_left _ _) hn
  have hn0pt : n0pt ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨h3, hPn⟩ := hn1 n hn1'
  set r : ℕ := glws_r2 n with hr
  set Pn : ℕ := glws_Pn γp kmax d n with hPn_def
  have hkmax1 : 1 ≤ kmax := by
    have h0 : 0 < d := by omega
    exact le_trans (hk ⟨0, h0⟩)
      (Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))
  have hPn_ge : (kmax * (r + 2)) ^ d ≤ Pn := Nat.le_add_right _ _
  have hPn_ge2 : ⌈Real.log ((2 * n : ℕ) : ℝ) ^ γp⌉₊ ≤ Pn := Nat.le_add_left _ _
  have hPn1 : 1 ≤ Pn := by
    have : 1 ≤ (kmax * (r + 2)) ^ d := Nat.one_le_pow _ _ (Nat.mul_pos (by omega) (by omega))
    omega
  obtain ⟨m, z, hz0, hzm, hadj, hinj, hposz⟩ := glws_path_extract η hlow hhigh hd0 N 0 t x hpos
  have hm : Pn ≤ m := by
    have h1 := glws_walk_mnorm z hadj m le_rfl
    rw [hz0, hzm] at h1
    have h2 : mnorm (x - 0) = mnorm x := by simp
    rw [h2] at h1
    have hnn : 0 ≤ mnorm x := by unfold mnorm; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    have : (Pn : ℤ) ≤ m := by
      have e : (((mnorm x).toNat : ℕ) : ℤ) = mnorm x := Int.toNat_of_nonneg hnn
      have : (Pn : ℤ) ≤ (((mnorm x).toNat : ℕ) : ℤ) := by exact_mod_cast hPx
      linarith
    exact_mod_cast this
  obtain ⟨p, hp⟩ : ∃ p, Pn = p + 1 := ⟨Pn - 1, by omega⟩
  -- the last `p + 1` sites of the path
  set w : ℕ → Site d := fun i => z (m - p + i) with hw
  have hw0 : w 0 = z (m - p) := by simp [hw]
  have hwp : w p = x := by
    have : m - p + p = m := by omega
    simp [hw, this, hzm]
  have hrev : ∀ i, i ≤ p → ∀ l, |w i l - x l| ≤ (p : ℤ) := by
    intro i hi l
    have e : m - p + i = m - (p - i) := by omega
    have := glws_path_coord_rev z hadj l (p - i) (by omega)
    rw [hzm] at this
    simp only [hw, e]
    have h2 : ((p - i : ℕ) : ℤ) ≤ p := by exact_mod_cast Nat.sub_le p i
    linarith
  have hcent : ∀ i, i ≤ p → w i ∈ cent d (2 * n) := by
    intro i hi l
    have h1 := hrev i hi l
    have h2 := hx l
    have h3 : (p : ℤ) ≤ n := by exact_mod_cast (by omega : p ≤ n)
    have h4 : ((2 * n : ℕ) : ℤ) = 2 * (n : ℤ) := by push_cast; ring
    rw [h4]
    calc |w i l| = |(w i l - x l) + x l| := by ring_nf
      _ ≤ |w i l - x l| + |x l| := abs_add_le _ _
      _ ≤ 2 * (n : ℤ) := by linarith
  have hwadj : ∀ i, i < p → (lattice d).Adj (w i) (w (i + 1)) := by
    intro i hi
    have : m - p + (i + 1) = (m - p + i) + 1 := by omega
    simp only [hw, this]
    exact hadj (m - p + i) (by omega)
  have hwinj : ∀ i j, i ≤ p → j ≤ p → w i = w j → i = j := by
    intro i j hi hj h
    have := hinj (m - p + i) (m - p + j) (by omega) (by omega) h
    omega
  have hwpos : ∀ i, i ≤ p → 0 < wave η N 0 t (w i) := fun i hi => hposz _ (by omega)
  have hlenR : Real.log ((2 * n : ℕ) : ℝ) ^ γp ≤ ((p + 1 : ℕ) : ℝ) := by
    have h1 : Real.log ((2 * n : ℕ) : ℝ) ^ γp ≤ ((⌈Real.log ((2 * n : ℕ) : ℝ) ^ γp⌉₊ : ℕ) : ℝ) :=
      Nat.le_ceil _
    have h2 : ⌈Real.log ((2 * n : ℕ) : ℝ) ^ γp⌉₊ ≤ p + 1 := by omega
    exact le_trans h1 (by exact_mod_cast h2)
  have hS : (kmax * (r + 2)) ^ d ≤ p + 1 := by omega
  obtain ⟨j, hj, hfired, htile⟩ := hpt (2 * n) (le_trans hn0pt (by omega)) r (Nat.le_ceil _) N hN
    0 t p w hcent hwinj hwadj hwpos hlenR hS
  refine ⟨j, hj, ?_, ?_⟩
  · have : t + (p + 1) ^ d + ∏ l, k l = t + Pn ^ d + ∏ l, k l := by rw [hp]
    rw [← this]
    exact hfired
  · -- the position of the tile
    have hcj := htile (glws_corner k j) (glws_corner_mem k hk j)
    have hcx : ∀ l, |glws_corner k j l - x l| ≤ 2 * (p : ℤ) + (kmax : ℤ) := by
      intro l
      have h1 := hcj l
      have h2 := hrev 0 (Nat.zero_le p) l
      have h3 : |glws_corner k j l - x l| ≤ |glws_corner k j l - w 0 l| + |w 0 l - x l| := by
        have := abs_add_le (glws_corner k j l - w 0 l) (w 0 l - x l)
        simpa using this
      linarith
    have h4 : mnorm (glws_corner k j - x) ≤ (d : ℤ) * (2 * (p : ℤ) + kmax) :=
      glws_mnorm_le_coord _ _ hcx
    have h5 := glws_mnorm_nu_lip k hk (glws_corner k j) x
    rw [glws_nu_corner k hk] at h5
    have hPnz : (Pn : ℤ) = (p : ℤ) + 1 := by rw [hp]; push_cast; ring
    have hd1 : (0 : ℤ) ≤ (d : ℤ) := Int.natCast_nonneg d
    have hmul : (d : ℤ) * (2 * (p : ℤ) + kmax) ≤ (d : ℤ) * (2 * (Pn : ℤ) + kmax) :=
      mul_le_mul_of_nonneg_left (by linarith) hd1
    linarith

end Exploding
