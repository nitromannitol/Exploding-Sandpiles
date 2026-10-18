import Exploding.Support.ArxivP1Crossing
import Exploding.Support.AllHighPodoFront
import Exploding.Support.AllHighLastArrival

/-!
# Approximate subadditivity at the endpoint

At parameter one, the actual background law is concentrated on the all-high
configuration. The ordinary odometer and last-wave fronts then give arrival
times differing by at most one, uniformly over all sites.
-/

namespace Exploding

open MeasureTheory
open LatticeProb

/-- The origin-raised all-high pile does not stabilize, since its ordinary
odometer front reaches sites of arbitrarily large Manhattan norm. -/
theorem all_high_pile_not_stabilizable (d : ℕ) (hd : 2 ≤ d) :
    ¬ Stabilizable
      (fun x : Site d => 2 * (d : ℤ) - 1 + (1 : ℤ) * dirac (0 : Site d) x) := by
  rintro ⟨T, hT⟩
  let i0 : Fin d := ⟨0, by omega⟩
  let x0 : Site d := fun i => if i = i0 then (T + 1 : ℤ) else 0
  have hxnorm : mnorm x0 = (T + 1 : ℤ) := by
    have hcoord (i : Fin d) :
        |x0 i| = if i = i0 then (T + 1 : ℤ) else 0 := by
      by_cases hi : i = i0
      · simp [x0, hi, abs_of_nonneg (show (0 : ℤ) ≤ (T + 1 : ℤ) by omega)]
      · simp [x0, hi]
    simp only [mnorm]
    simp_rw [hcoord]
    simp
  have hstable := hT (T + 2) (by omega)
  have hpos : 0 < podo
      (fun y : Site d => 2 * (d : ℤ) - 1 + dirac (0 : Site d) y) (T + 2) x0 := by
    exact (all_high_podo_pos_iff d (T + 2) x0).2 (by rw [hxnorm]; omega)
  have hstable' : podo
      (fun y : Site d => 2 * (d : ℤ) - 1 + dirac (0 : Site d) y) (T + 2) x0 =
        podo (fun y : Site d => 2 * (d : ℤ) - 1 + dirac (0 : Site d) y) T x0 := by
    simpa only [one_mul] using congrFun hstable x0
  have hposT : 0 < podo
      (fun y : Site d => 2 * (d : ℤ) - 1 + dirac (0 : Site d) y) T x0 := by
    rw [← hstable']
    exact hpos
  have hfront := (all_high_podo_pos_iff d T x0).1 hposT
  rw [hxnorm] at hfront
  omega

/-- The explosion threshold of the all-high background is one. -/
theorem all_high_explosionThreshold (d : ℕ) (hd : 2 ≤ d) :
    explosionThreshold (fun _ : Site d => 2 * (d : ℤ) - 1) = 1 := by
  unfold explosionThreshold
  have hmem : 1 ∈ {n : ℕ | 1 ≤ n ∧
      ¬ Stabilizable (fun x => 2 * (d : ℤ) - 1 + n * dirac (0 : Site d) x)} := by
    simp only [Set.mem_setOf_eq]
    constructor
    · norm_num
    · simpa using all_high_pile_not_stabilizable d hd
  have hleast := Nat.sInf_mem ⟨1, hmem⟩
  exact Nat.le_antisymm (Nat.sInf_le hmem) hleast.1

/-- The exploding-pile arrival time of the all-high background is one more
than the Manhattan norm. -/
theorem all_high_arrival (d : ℕ) (hd : 2 ≤ d) (x : Site d) :
    arrival (fun _ : Site d => 2 * (d : ℤ) - 1) x =
      (((mnorm x).toNat + 1 : ℕ) : ℕ∞) := by
  let r : ℤ := mnorm x
  let k : ℕ := r.toNat + 1
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact mnorm_nonneg x
  have hr_cast : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr_nonneg
  have hthreshold :
      explosionThreshold (fun _ : Site d => 2 * (d : ℤ) - 1) = 1 :=
    all_high_explosionThreshold d hd
  have hfront (n : ℕ) :
      0 < podo (explodingPile (fun _ : Site d => 2 * (d : ℤ) - 1)) n x ↔ r < (n : ℤ) := by
    change 0 < podo
      (fun y : Site d => 2 * (d : ℤ) - 1 +
        (explosionThreshold (fun _ : Site d => 2 * (d : ℤ) - 1) : ℤ) *
          dirac (0 : Site d) y) n x ↔ r < (n : ℤ)
    rw [hthreshold]
    simpa [r] using (all_high_podo_pos_iff d n x)
  have hk_pos : 1 ≤ k := by
    dsimp [k]
    omega
  have hr_lt_k : r < (k : ℤ) := by
    rw [← hr_cast]
    dsimp [k]
    exact_mod_cast Nat.lt_succ_self r.toNat
  have hupper : arrival (fun _ : Site d => 2 * (d : ℤ) - 1) x ≤ (k : ℕ∞) := by
    unfold arrival
    exact sInf_le ⟨k, rfl, hk_pos, (hfront k).2 hr_lt_k⟩
  have hlower : (k : ℕ∞) ≤ arrival (fun _ : Site d => 2 * (d : ℤ) - 1) x := by
    unfold arrival
    refine le_sInf ?_
    rintro t ⟨n, rfl, hn, hpos⟩
    have hr_lt_n : r < (n : ℤ) := (hfront n).1 hpos
    have hrnat_lt_n_int : (r.toNat : ℤ) < (n : ℤ) := by
      simpa [hr_cast] using hr_lt_n
    have hrnat_lt_n : r.toNat < n := by
      exact_mod_cast hrnat_lt_n_int
    have hk_le_n : k ≤ n := by
      dsimp [k]
      omega
    exact ENat.coe_le_coe.mpr hk_le_n
  have hresult : arrival (fun _ : Site d => 2 * (d : ℤ) - 1) x = (k : ℕ∞) :=
    le_antisymm hupper hlower
  simpa [r, k] using hresult

/-- At parameter one, the all-high arrival formulas give the endpoint
approximate-subadditivity bound with constants one and zero. -/
theorem approximate_subadditive_p1 (d : ℕ) (hd : 2 ≤ d) :
    ∀ᵐ η ∂(toyLaw d (1 : ℝ)), ∃ C1 C2 : ℕ, ∀ x : Site d,
      arrival η x ≤ lastArrival η (0 : Site d) x + (C1 : ℕ∞) ∧
        lastArrival η (0 : Site d) x ≤ arrival η x + (C2 : ℕ∞) := by
  rw [toyLaw_one_eq_dirac, MeasureTheory.ae_dirac_eq]
  simp only [Filter.Eventually, Filter.mem_pure]
  refine ⟨1, 0, fun x => ?_⟩
  rw [all_high_arrival d hd x, all_high_last_arrival_eq d hd 0 x]
  simp only [sub_zero]
  have hmax_le : max 1 (mnorm x).toNat ≤ (mnorm x).toNat + 1 := by
    exact max_le (by omega) (by omega)
  have hsucc_le : (mnorm x).toNat + 1 ≤ max 1 (mnorm x).toNat + 1 := by
    exact Nat.add_le_add_right (Nat.le_max_right 1 (mnorm x).toNat) 1
  constructor
  · rw [← Nat.cast_add]
    exact ENat.coe_le_coe.mpr hsucc_le
  · rw [← Nat.cast_add]
    exact ENat.coe_le_coe.mpr hmax_le

end Exploding
