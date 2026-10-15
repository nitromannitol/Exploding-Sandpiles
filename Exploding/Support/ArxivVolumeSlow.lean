import Exploding.Support.CESlow4
import Exploding.Support.CEProof

/-!
# Slow sites in the stacked checkerboard

This module proves the slow-site bound used in the volume argument.  The site
carrier keeps the first two integer coordinates and indexes the remaining
coordinates by `Fin (d - 2)`, including the empty fiber when `d = 2`.
-/

namespace Exploding

open LatticeProb

/-- The lattice site with first coordinates `a`, `b` and remaining coordinates `z`.
For `d = 2`, the remaining coordinate type is empty. -/
def ceVolumeSlowSite (d : ℕ) (hd : 2 ≤ d) (a b : ℤ) (z : Fin (d - 2) → ℤ) :
    Site d :=
  fun i =>
    if h0 : (i : ℕ) = 0 then a
    else if h1 : (i : ℕ) = 1 then b
    else z ⟨(i : ℕ) - 2, by omega⟩

/-- The threshold-three odometer vanishes at every signed transverse copy of
`(3 + 8n, 4k)` before time `12n`.  The cylinder supersolution has second-wave
time `12n + 8` there, and the pointwise stack comparison transfers its zero
bound to every choice of the remaining integer coordinates. -/
theorem ce_podo_zero_signed_slow_site (d : ℕ) (hd : 2 ≤ d) (n : ℕ)
    (_hn : 1 ≤ n) (k : ℤ) (z : Fin (d - 2) → ℤ) (t : ℕ)
    (ht : t < 12 * n) :
    podo (fun y => ceEta d y + 3 * dirac (0 : Site d) y) t
      (ceVolumeSlowSite d hd ((3 + 8 * n : ℕ) : ℤ) (4 * k) z) = 0 := by
  let a : ℤ := ((3 + 8 * n : ℕ) : ℤ)
  let b : ℤ := 4 * k
  let x : Site d := ceVolumeSlowSite d hd a b z
  have h0 : 0 < d := by omega
  have h1 : 1 < d := by omega
  have hx0 : x ⟨0, h0⟩ = a := by
    simp [x, ceVolumeSlowSite]
  have hx1 : x ⟨1, h1⟩ = b := by
    simp [x, ceVolumeSlowSite]
  let x₂ : Site 2 := fun i => if (i : ℕ) = 0 then a else b
  have hx₂0 : x₂ 0 = a := by simp [x₂]
  have hx₂1 : x₂ 1 = b := by simp [x₂]
  have hproject :
      (fun i : Fin 2 =>
        if (i : ℕ) = 0 then x ⟨0, h0⟩ else x ⟨1, h1⟩) = x₂ := by
    funext i
    fin_cases i <;> simp [x₂, hx0, hx1]
  have ha_pos : 0 < a := by
    dsimp [a]
    omega
  have hfold : cels_fold a = a := by
    unfold cels_fold
    rw [if_pos (by omega : 0 ≤ a)]
  have hmod_a : a % 4 = 3 := by
    dsimp [a]
    omega
  have hmod_b : b % 4 = 0 := by
    dsimp [b]
    omega
  have htau : cels_tau a 0 = 12 * (n : ℤ) + 8 := by
    dsimp [a]
    exact cels_tau_axis n
  have htime_nat : t < 12 * n + 8 := by omega
  have htime : (t : ℤ) < 12 * (n : ℤ) + 8 := by
    exact_mod_cast htime_nat
  have hzero_origin : ¬ (a = 0 ∧ (0 : ℤ) = 0) := by
    dsimp [a]
    omega
  have hu : cels_u a 0 = 0 := by
    unfold cels_u zeta1
    rw [hmod_a]
    norm_num
  have hW : cels_W (t : ℤ) a 0 = 0 := by
    unfold cels_W
    rw [if_neg hzero_origin]
    rw [if_pos (by rw [htau]; exact htime)]
  have hwp : cels_wP t x₂ = 0 := by
    unfold cels_wP cels_w cels_cw
    rw [hx₂0, hx₂1, hfold, hmod_b, hu, hW]
    norm_num
  have h2bound := cels_podo_le t x₂
  rw [hwp] at h2bound
  have h2nonneg :=
    aux_podo_nonneg (fun y => ceEta 2 y + 3 * dirac (0 : Site 2) y) t x₂
  have h2zero : podo (fun y => ceEta 2 y + 3 * dirac (0 : Site 2) y) t x₂ = 0 := by
    omega
  have hstack := ce_stack_le_2D d hd t x
  rw [aux_ce_explodingPile_eq d hd, aux_ce_explodingPile_eq 2 le_rfl,
    hproject, h2zero] at hstack
  have hnonneg :=
    aux_podo_nonneg (fun y => ceEta d y + 3 * dirac (0 : Site d) y) t x
  have hx :
      podo (fun y => ceEta d y + 3 * dirac (0 : Site d) y) t x = 0 := by
    omega
  simpa [x, a, b] using hx

end Exploding
