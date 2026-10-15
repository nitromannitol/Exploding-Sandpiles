import Exploding.Support.ArxivVolumeCells

/-!
# A finite grid of slow nearest-site cells

For each sufficiently large scale, this module selects a finite grid of the
signed slow sites.  It proves the exact grid cardinality, the slow and fast
time inequalities, and containment of every selected half-open nearest-site
cell in the source box.
-/

namespace Exploding

open LatticeProb

/-- The scale divisor used for the finite grid. -/
def ceVolumeGridQ (d : ℕ) : ℕ := 10000 * d

/-- The quotient scale of the finite grid. -/
def ceVolumeGridM (d t : ℕ) : ℕ := t / ceVolumeGridQ d

/-- The first grid coordinate determines the slow-site index `n`. -/
def ceVolumeGridN (d : ℕ) (hd : 2 ≤ d) (t : ℕ)
    (u : Fin d → Fin (ceVolumeGridM d t)) : ℕ :=
  960 * d * ceVolumeGridM d t + (u ⟨0, by omega⟩).val

/-- The second grid coordinate determines a nonnegative transverse index. -/
def ceVolumeGridK (d : ℕ) (hd : 2 ≤ d) (t : ℕ)
    (u : Fin d → Fin (ceVolumeGridM d t)) : ℤ :=
  (u ⟨1, by omega⟩).val

/-- The remaining grid coordinates form a nonnegative element of the empty-capable fiber. -/
def ceVolumeGridZ (d t : ℕ) (u : Fin d → Fin (ceVolumeGridM d t)) :
    Fin (d - 2) → ℤ :=
  fun i => (u ⟨(i : ℕ) + 2, by omega⟩).val

/-- The selected slow site associated with one point of the finite grid. -/
def ceVolumeGridCenter (d : ℕ) (hd : 2 ≤ d) (t : ℕ)
    (u : Fin d → Fin (ceVolumeGridM d t)) : Site d :=
  ceVolumeSlowSite d hd
    ((3 + 8 * ceVolumeGridN d hd t u : ℕ) : ℤ)
    (4 * ceVolumeGridK d hd t u) (ceVolumeGridZ d t u)

/-- The first coordinate of a grid center recovers its index `n`. -/
theorem ceVolumeGridCenter_apply_zero (d : ℕ) (hd : 2 ≤ d) (t : ℕ)
    (u : Fin d → Fin (ceVolumeGridM d t)) :
    ceVolumeGridCenter d hd t u ⟨0, by omega⟩ =
      ((3 + 8 * ceVolumeGridN d hd t u : ℕ) : ℤ) := by
  simp [ceVolumeGridCenter, ceVolumeSlowSite]

/-- The second coordinate of a grid center is four times its index `k`. -/
theorem ceVolumeGridCenter_apply_one (d : ℕ) (hd : 2 ≤ d) (t : ℕ)
    (u : Fin d → Fin (ceVolumeGridM d t)) :
    ceVolumeGridCenter d hd t u ⟨1, by omega⟩ = 4 * ceVolumeGridK d hd t u := by
  simp [ceVolumeGridCenter, ceVolumeSlowSite]

/-- The extra coordinates of a grid center are exactly its fiber coordinates. -/
theorem ceVolumeGridCenter_apply_extra (d : ℕ) (hd : 2 ≤ d) (t : ℕ)
    (u : Fin d → Fin (ceVolumeGridM d t)) (i : Fin (d - 2)) :
    ceVolumeGridCenter d hd t u ⟨(i : ℕ) + 2, by omega⟩ =
      ceVolumeGridZ d t u i := by
  simp [ceVolumeGridCenter, ceVolumeSlowSite, ceVolumeGridZ]

/-- The quotient grid has at least one hundred points in each coordinate. -/
theorem ceVolumeGrid_division_bounds (d : ℕ) (hd : 2 ≤ d) (t : ℕ)
    (ht : 1000000 * d ≤ t) :
    100 ≤ ceVolumeGridM d t ∧
      ceVolumeGridQ d * ceVolumeGridM d t ≤ t ∧
      t < ceVolumeGridQ d * (ceVolumeGridM d t + 1) ∧
      ceVolumeGridQ d * (ceVolumeGridM d t + 1) ≤
        2 * ceVolumeGridQ d * ceVolumeGridM d t := by
  let q := ceVolumeGridQ d
  let m := ceVolumeGridM d t
  have hq : 0 < q := by
    dsimp [q, ceVolumeGridQ]
    omega
  have hlarge : 100 * q ≤ t := by
    dsimp [q, ceVolumeGridQ]
    nlinarith
  have hm : 100 ≤ m := by
    dsimp [m]
    exact (Nat.le_div_iff_mul_le hq).2 hlarge
  have hlow : q * m ≤ t := by
    dsimp [m]
    have h := Nat.div_mul_le_self t q
    rw [Nat.mul_comm (t / q) q] at h
    exact h
  have hqm : q ≤ q * m := by
    have hmul := Nat.mul_le_mul_left q hm
    nlinarith [hmul]
  have hupper : t < q * (m + 1) := by
    have hdiv : t / q < m + 1 := by dsimp [m]; exact Nat.lt_succ_self _
    have hmul := (Nat.div_lt_iff_lt_mul hq).1 hdiv
    simpa [m, Nat.mul_comm] using hmul
  have hdouble : q * (m + 1) ≤ 2 * q * m := by
    rw [Nat.mul_add]
    nlinarith [hqm]
  exact ⟨hm, by simpa [q, m] using hlow,
    by simpa [q, m] using hupper, by simpa [q, m] using hdouble⟩

/-- The finite grid of selected slow sites. -/
def ceVolumeGridCenters (d : ℕ) (hd : 2 ≤ d) (t : ℕ) : Finset (Site d) :=
  Finset.univ.image (ceVolumeGridCenter d hd t)

/-- Distinct grid indices select distinct lattice sites. -/
theorem ceVolumeGridCenter_injective (d : ℕ) (hd : 2 ≤ d) (t : ℕ) :
    Function.Injective (ceVolumeGridCenter d hd t) := by
  intro u v huv
  have h0 := congrFun huv ⟨0, by omega⟩
  rw [ceVolumeGridCenter_apply_zero, ceVolumeGridCenter_apply_zero] at h0
  have hn : ceVolumeGridN d hd t u = ceVolumeGridN d hd t v := by
    have hnat : 3 + 8 * ceVolumeGridN d hd t u =
        3 + 8 * ceVolumeGridN d hd t v := by exact_mod_cast h0
    omega
  have h1 := congrFun huv ⟨1, by omega⟩
  rw [ceVolumeGridCenter_apply_one, ceVolumeGridCenter_apply_one] at h1
  have hk : (u ⟨1, by omega⟩).val = (v ⟨1, by omega⟩).val := by
    dsimp [ceVolumeGridK] at h1
    have hnat : 4 * (u ⟨1, by omega⟩).val = 4 * (v ⟨1, by omega⟩).val := by
      exact_mod_cast h1
    omega
  have hfirst : (u ⟨0, by omega⟩).val = (v ⟨0, by omega⟩).val := by
    dsimp [ceVolumeGridN] at hn
    omega
  funext i
  apply Fin.ext
  by_cases hi0 : (i : ℕ) = 0
  · have hi : i = ⟨0, by omega⟩ := Fin.ext hi0
    rw [hi]
    exact hfirst
  · by_cases hi1 : (i : ℕ) = 1
    · have hi : i = ⟨1, by omega⟩ := Fin.ext hi1
      rw [hi]
      exact hk
    · let j : Fin (d - 2) := ⟨(i : ℕ) - 2, by omega⟩
      have hij : (⟨(j : ℕ) + 2, by omega⟩ : Fin d) = i := by
        apply Fin.ext
        dsimp [j]
        omega
      have hex := congrFun huv (⟨(j : ℕ) + 2, by omega⟩ : Fin d)
      rw [ceVolumeGridCenter_apply_extra, ceVolumeGridCenter_apply_extra] at hex
      dsimp [ceVolumeGridZ] at hex
      have hval : (u ⟨(j : ℕ) + 2, by omega⟩).val =
          (v ⟨(j : ℕ) + 2, by omega⟩).val := by
        exact_mod_cast hex
      rw [hij] at hval
      exact hval

/-- The finite image contains exactly `m^d` distinct lattice sites. -/
theorem ceVolumeGridCenters_card (d : ℕ) (hd : 2 ≤ d) (t : ℕ) :
    (ceVolumeGridCenters d hd t).card = (ceVolumeGridM d t) ^ d := by
  rw [ceVolumeGridCenters, Finset.card_image_of_injective _
    (ceVolumeGridCenter_injective d hd t)]
  simp

/-- In dimension two the grid is nonempty and its transverse `Fin 0` sum is empty. -/
theorem ceVolumeGrid_d2_nonvacuous (t : ℕ) (ht : 2000000 ≤ t) :
    0 < (ceVolumeGridCenters 2 (by omega) t).card ∧
      ∀ u : Fin 2 → Fin (ceVolumeGridM 2 t),
        (∑ i : Fin (2 - 2), Int.natAbs (ceVolumeGridZ 2 t u i)) = 0 := by
  have hm : 0 < ceVolumeGridM 2 t := by
    have h := (ceVolumeGrid_division_bounds 2 (by omega) t (by omega)).1
    omega
  constructor
  · rw [ceVolumeGridCenters_card]
    exact Nat.pow_pos hm
  · intro u
    simp

/-- Every selected center has its slow index at least one. -/
theorem ceVolumeGrid_index_pos (d : ℕ) (hd : 2 ≤ d) (t : ℕ)
    (ht : 1000000 * d ≤ t) (u : Fin d → Fin (ceVolumeGridM d t)) :
    1 ≤ ceVolumeGridN d hd t u := by
  obtain ⟨hm, hqm, _, _⟩ := ceVolumeGrid_division_bounds d hd t ht
  have hdpos : 0 < d := by omega
  have hmpos : 0 < ceVolumeGridM d t := by omega
  have hprod : 0 < d * ceVolumeGridM d t := Nat.mul_pos hdpos hmpos
  dsimp [ceVolumeGridN]
  nlinarith [hprod]

/-- The quotient scale gives a tighter upper bound useful for the slow-site time. -/
theorem ceVolumeGrid_time_scale (d : ℕ) (hd : 2 ≤ d) (t : ℕ)
    (ht : 1000000 * d ≤ t) :
    10000 * (d * ceVolumeGridM d t) ≤ t ∧
      t < 10100 * (d * ceVolumeGridM d t) := by
  obtain ⟨hm, hqm, hqhi, _⟩ := ceVolumeGrid_division_bounds d hd t ht
  have hfac : 100 * (ceVolumeGridM d t + 1) ≤
      101 * ceVolumeGridM d t := by omega
  constructor
  · dsimp [ceVolumeGridQ] at hqm
    nlinarith
  · have hprod :
        ceVolumeGridQ d * (ceVolumeGridM d t + 1) ≤
          10100 * (d * ceVolumeGridM d t) := by
      dsimp [ceVolumeGridQ]
      nlinarith [Nat.mul_le_mul_left (100 * d) hfac]
    exact lt_of_lt_of_le hqhi hprod

/-- The selected slow index is bounded above by `961*d*m`. -/
theorem ceVolumeGrid_index_le (d : ℕ) (hd : 2 ≤ d) (t : ℕ)
    (ht : 1000000 * d ≤ t) (u : Fin d → Fin (ceVolumeGridM d t)) :
    ceVolumeGridN d hd t u ≤ 961 * (d * ceVolumeGridM d t) := by
  have hm := (ceVolumeGrid_division_bounds d hd t ht).1
  have hd1 : 1 ≤ d := by omega
  have hmprod : ceVolumeGridM d t ≤ d * ceVolumeGridM d t := by
    have h := Nat.mul_le_mul_right (ceVolumeGridM d t) hd1
    simpa using h
  have hu : (u ⟨0, by omega⟩).val < ceVolumeGridM d t := (u ⟨0, by omega⟩).isLt
  dsimp [ceVolumeGridN]
  nlinarith [hmprod, hu]

/-- Nonnegative fiber coordinates contribute at most `(d-2)*m` to their path length. -/
theorem ceVolumeGrid_extra_sum_le (d : ℕ) (hd : 2 ≤ d) (t : ℕ)
    (u : Fin d → Fin (ceVolumeGridM d t)) :
    (∑ i : Fin (d - 2), Int.natAbs (ceVolumeGridZ d t u i)) ≤
      (d - 2) * ceVolumeGridM d t := by
  calc
    (∑ i : Fin (d - 2), Int.natAbs (ceVolumeGridZ d t u i)) ≤
        ∑ _i : Fin (d - 2), ceVolumeGridM d t := by
      apply Finset.sum_le_sum
      intro i hi
      have hzi : Int.natAbs (ceVolumeGridZ d t u i) =
          (u ⟨(i : ℕ) + 2, by omega⟩).val := by
        simp [ceVolumeGridZ]
      rw [hzi]
      exact Nat.le_of_lt (u ⟨(i : ℕ) + 2, by omega⟩).isLt
    _ = (d - 2) * ceVolumeGridM d t := by simp

/-- The grid's slow and fast deadlines are both at most the selected scale. -/
theorem ceVolumeGrid_timing (d : ℕ) (hd : 2 ≤ d) (t : ℕ)
    (ht : 1000000 * d ≤ t) (u : Fin d → Fin (ceVolumeGridM d t)) :
    1 ≤ ceVolumeGridN d hd t u ∧
      t < 12 * ceVolumeGridN d hd t u ∧
      3 + 8 * ceVolumeGridN d hd t u +
          Int.natAbs (4 * ceVolumeGridK d hd t u) +
          (∑ i : Fin (d - 2), Int.natAbs (ceVolumeGridZ d t u i)) + 2 ≤ t := by
  have hm := (ceVolumeGrid_division_bounds d hd t ht).1
  have hscale := ceVolumeGrid_time_scale d hd t ht
  have hindexlow : 960 * (d * ceVolumeGridM d t) ≤ ceVolumeGridN d hd t u := by
    dsimp [ceVolumeGridN]
    nlinarith
  have hindexhigh := ceVolumeGrid_index_le d hd t ht u
  have hprodpos : 0 < d * ceVolumeGridM d t := by
    exact Nat.mul_pos (by omega) (by omega)
  have hslow : t < 12 * ceVolumeGridN d hd t u := by
    nlinarith [hscale.2, hindexlow]
  have hk : Int.natAbs (4 * ceVolumeGridK d hd t u) = 4 * (u ⟨1, by omega⟩).val := by
    simp [ceVolumeGridK, Int.natAbs_mul, Int.natAbs_natCast]
  have hkb : Int.natAbs (4 * ceVolumeGridK d hd t u) ≤
      4 * ceVolumeGridM d t := by
    rw [hk]
    omega
  have hsum := ceVolumeGrid_extra_sum_le d hd t u
  have hdcoef : d + 2 ≤ 2 * d := by omega
  have hcoef := Nat.mul_le_mul_right (ceVolumeGridM d t) hdcoef
  have hextra : 4 * ceVolumeGridM d t + (d - 2) * ceVolumeGridM d t ≤
      2 * (d * ceVolumeGridM d t) := by
    have hcoefEq : (d - 2) + 4 = d + 2 := by omega
    calc
      4 * ceVolumeGridM d t + (d - 2) * ceVolumeGridM d t =
          ((d - 2) + 4) * ceVolumeGridM d t := by ring
      _ = (d + 2) * ceVolumeGridM d t := by rw [hcoefEq]
      _ ≤ 2 * (d * ceVolumeGridM d t) := by
        simpa [Nat.mul_assoc] using hcoef
  have hmprod : ceVolumeGridM d t ≤ d * ceVolumeGridM d t := by
    have h := Nat.mul_le_mul_right (ceVolumeGridM d t) (show 1 ≤ d by omega)
    simpa using h
  have hfive : 5 ≤ d * ceVolumeGridM d t := by omega
  have hdeadline :
      3 + 8 * ceVolumeGridN d hd t u +
          Int.natAbs (4 * ceVolumeGridK d hd t u) +
          (∑ i : Fin (d - 2), Int.natAbs (ceVolumeGridZ d t u i)) + 2 ≤
        7691 * (d * ceVolumeGridM d t) := by
    omega
  have hbudget : 7691 * (d * ceVolumeGridM d t) ≤ t := by
    omega
  exact ⟨ceVolumeGrid_index_pos d hd t ht u, hslow,
    le_trans hdeadline hbudget⟩

/-- Every non-first coordinate of a selected center lies between zero and `4m`. -/
theorem ceVolumeGridCenter_coord_bounds (d : ℕ) (hd : 2 ≤ d) (t : ℕ)
    (u : Fin d → Fin (ceVolumeGridM d t)) (i : Fin d)
    (hi : i ≠ ⟨0, by omega⟩) :
    0 ≤ ceVolumeGridCenter d hd t u i ∧
      ceVolumeGridCenter d hd t u i ≤ (4 * ceVolumeGridM d t : ℤ) := by
  have hzero : (i : ℕ) ≠ 0 := by
    intro h
    apply hi
    exact Fin.ext h
  by_cases hone : i = ⟨1, by omega⟩
  · subst i
    rw [ceVolumeGridCenter_apply_one]
    dsimp [ceVolumeGridK]
    have hu := (u ⟨1, by omega⟩).isLt
    constructor <;> norm_cast <;> omega
  · have honeVal : (i : ℕ) ≠ 1 := by
      intro h
      apply hone
      exact Fin.ext h
    have htwo : 2 ≤ (i : ℕ) := by omega
    let j : Fin (d - 2) := ⟨(i : ℕ) - 2, by omega⟩
    have hij : (⟨(j : ℕ) + 2, by omega⟩ : Fin d) = i := by
      apply Fin.ext
      dsimp [j]
      omega
    rw [← hij, ceVolumeGridCenter_apply_extra]
    dsimp [ceVolumeGridZ]
    have hu := (u ⟨(j : ℕ) + 2, by omega⟩).isLt
    constructor <;> norm_cast <;> omega

/-- The open source box used for the selected nearest-site cells. -/
def ceVolumeGridOmega (d : ℕ) (hd : 2 ≤ d) : Set (Fin d → ℝ) :=
  {y | (3 / 4 : ℝ) < y ⟨0, by omega⟩ ∧ y ⟨0, by omega⟩ < 4 / 5 ∧
    ∀ i : Fin d, i ≠ ⟨0, by omega⟩ →
      |y i| < 1 / (100 * (d : ℝ))}

/-- Every actual half-open nearest-site cell of the grid lies in the source box. -/
theorem ceVolumeGridCell_subset (d : ℕ) (hd : 2 ≤ d) (t : ℕ)
    (ht : 1000000 * d ≤ t) (u : Fin d → Fin (ceVolumeGridM d t)) :
    ceVolumeCell d t (ceVolumeGridCenter d hd t u) ⊆ ceVolumeGridOmega d hd := by
  obtain ⟨hm, hqm, hqhi, hqdouble⟩ := ceVolumeGrid_division_bounds d hd t ht
  have htposN : 0 < t := by
    have hqpos : 0 < ceVolumeGridQ d := by
      dsimp [ceVolumeGridQ]
      omega
    have hmpos : 0 < ceVolumeGridM d t := by omega
    have hprod := Nat.mul_pos hqpos hmpos
    omega
  have htpos : 0 < (t : ℝ) := by exact_mod_cast htposN
  have hdpos : 0 < (d : ℝ) := by positivity
  have hmR : 100 ≤ (ceVolumeGridM d t : ℝ) := by exact_mod_cast hm
  have ht50 : 50 * (d : ℝ) < (t : ℝ) := by
    exact_mod_cast (by omega : 50 * d < t)
  have hP : 200 ≤ d * ceVolumeGridM d t := by
    have hmul := Nat.mul_le_mul_right (ceVolumeGridM d t) (show 2 ≤ d by omega)
    have hm2 := Nat.mul_le_mul_left 2 hm
    nlinarith [hmul, hm2]
  have hscale := ceVolumeGrid_time_scale d hd t ht
  have hscaleLoR :
      10000 * ((d : ℝ) * (ceVolumeGridM d t : ℝ)) ≤ (t : ℝ) := by
    exact_mod_cast hscale.1
  have hscaleHiR :
      (t : ℝ) < 10100 * ((d : ℝ) * (ceVolumeGridM d t : ℝ)) := by
    exact_mod_cast hscale.2
  have hPposR : 0 < (d : ℝ) * (ceVolumeGridM d t : ℝ) := by
    positivity
  have hP200R : 200 ≤ (d : ℝ) * (ceVolumeGridM d t : ℝ) := by
    exact_mod_cast hP
  have hnlow :
      960 * (d * ceVolumeGridM d t) ≤ ceVolumeGridN d hd t u := by
    dsimp [ceVolumeGridN]
    nlinarith
  have hnhigh := ceVolumeGrid_index_le d hd t ht u
  have hnlowR :
      960 * ((d : ℝ) * (ceVolumeGridM d t : ℝ)) ≤
        (ceVolumeGridN d hd t u : ℝ) := by exact_mod_cast hnlow
  have hnhighR :
      (ceVolumeGridN d hd t u : ℝ) ≤
        961 * ((d : ℝ) * (ceVolumeGridM d t : ℝ)) := by exact_mod_cast hnhigh
  intro y hy
  have hcoords := (ceVolumeCell_mem_iff d t (ceVolumeGridCenter d hd t u)
    (by omega) y).mp hy
  have hc0 :
      ((ceVolumeGridCenter d hd t u ⟨0, by omega⟩ : ℤ) : ℝ) =
        3 + 8 * (ceVolumeGridN d hd t u : ℝ) := by
    rw [ceVolumeGridCenter_apply_zero]
    norm_cast
  have hc0lo : 7680 * ((d : ℝ) * (ceVolumeGridM d t : ℝ)) ≤
      ((ceVolumeGridCenter d hd t u ⟨0, by omega⟩ : ℤ) : ℝ) := by
    rw [hc0]
    nlinarith [hnlowR]
  have hc0hi :
      ((ceVolumeGridCenter d hd t u ⟨0, by omega⟩ : ℤ) : ℝ) ≤
        7688 * ((d : ℝ) * (ceVolumeGridM d t : ℝ)) + 3 := by
    rw [hc0]
    nlinarith [hnhighR]
  have hfirstlo :
      (3 / 4 : ℝ) <
        ((((ceVolumeGridCenter d hd t u ⟨0, by omega⟩ : ℤ) : ℝ) - 1 / 2) /
          (t : ℝ)) := by
    rw [lt_div_iff₀ htpos]
    nlinarith [hc0lo, hscaleHiR, hPposR]
  have hfirsthi :
      ((((ceVolumeGridCenter d hd t u ⟨0, by omega⟩ : ℤ) : ℝ) + 1 / 2) /
        (t : ℝ)) < 4 / 5 := by
    rw [div_lt_iff₀ htpos]
    nlinarith [hc0hi, hscaleLoR, hP200R]
  refine ⟨hfirstlo.trans (hcoords ⟨0, by omega⟩).1,
    (hcoords ⟨0, by omega⟩).2.trans_lt hfirsthi, ?_⟩
  intro i hi
  have hxi := ceVolumeGridCenter_coord_bounds d hd t u i hi
  have hxiR :
      0 ≤ (ceVolumeGridCenter d hd t u i : ℝ) ∧
        (ceVolumeGridCenter d hd t u i : ℝ) ≤ 4 * (ceVolumeGridM d t : ℝ) := by
    exact_mod_cast hxi
  have hdmR : (d : ℝ) ≤ (d : ℝ) * (ceVolumeGridM d t : ℝ) := by
    have hm1 : 1 ≤ (ceVolumeGridM d t : ℝ) := by linarith [hmR]
    calc
      (d : ℝ) = (d : ℝ) * 1 := by ring
      _ ≤ (d : ℝ) * (ceVolumeGridM d t : ℝ) :=
        mul_le_mul_of_nonneg_left hm1 (le_of_lt hdpos)
  have hcenterHi := mul_le_mul_of_nonneg_left hxiR.2
    (by positivity : 0 ≤ (100 : ℝ) * (d : ℝ))
  have hmargin : 50 * (d : ℝ) ≤ 50 * ((d : ℝ) * (ceVolumeGridM d t : ℝ)) := by
    nlinarith [hdmR]
  have hlow :
      -(1 / (100 * (d : ℝ))) <
        ((((ceVolumeGridCenter d hd t u i : ℤ) : ℝ) - 1 / 2) / (t : ℝ)) := by
    rw [lt_div_iff₀ htpos]
    field_simp [ne_of_gt hdpos]
    nlinarith [ht50, hxiR.1]
  have hhigh :
      ((((ceVolumeGridCenter d hd t u i : ℤ) : ℝ) + 1 / 2) / (t : ℝ)) <
        1 / (100 * (d : ℝ)) := by
    rw [div_lt_iff₀ htpos]
    field_simp [ne_of_gt hdpos]
    nlinarith [hcenterHi, hmargin, hscaleLoR, hPposR]
  exact abs_lt.mpr ⟨hlow.trans (hcoords i).1,
    (hcoords i).2.trans_lt hhigh⟩

end Exploding
