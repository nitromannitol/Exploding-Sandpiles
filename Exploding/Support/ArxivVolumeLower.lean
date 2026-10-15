import Exploding.Support.ArxivVolumeGrid
import Exploding.Support.ArxivVolumeFast
import Exploding.Support.ArxivVolumeSlow
import Exploding.Support.ArxivVolumeCells

/-!
# A positive volume bound for translated supports

The selected grid cells lie in the symmetric difference of the actual
threshold-three odometer support and its translate by `e₂/t`. Their disjoint
measurable union has volume bounded below by a positive constant depending only
on the dimension, including when the extra-coordinate fiber is `Fin 0`.
-/

namespace Exploding

open LatticeProb MeasureTheory

/-- The actual positive support of the threshold-three odometer at scale `t`. -/
def ceVolumeAtTime (d t : ℕ) : Set (Fin d → ℝ) :=
  {y : Fin d → ℝ | 0 < podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) t
    (nearestSite ((t : ℝ) • y))}

/-- A fixed positive lower-bound constant for the translated support difference. -/
noncomputable def ceVolumeLowerConstant (d : ℕ) : ℝ :=
  (1 / (20000 * (d : ℝ))) ^ d

/-- The lower-bound constant is strictly positive in every dimension at least two. -/
theorem ceVolumeLowerConstant_pos (d : ℕ) (hd : 2 ≤ d) :
    0 < ceVolumeLowerConstant d := by
  unfold ceVolumeLowerConstant
  positivity

/-- The parallel odometer is monotone across every finite time interval. -/
theorem ceVolumePodo_mono_time {d : ℕ} (σ : Site d → ℤ) {s t : ℕ}
    (hst : s ≤ t) (x : Site d) : podo σ s x ≤ podo σ t x := by
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih => exact le_trans ih (podo_mono_step σ t x)

/-- Adding the second coordinate unit vector changes a grid center's slow site to its
corresponding fast site. -/
theorem ceVolumeGridCenter_add_e₂ (d : ℕ) (hd : 2 ≤ d) (t : ℕ)
    (u : Fin d → Fin (ceVolumeGridM d t)) :
    ceVolumeGridCenter d hd t u + ceVolumeE₂ d hd =
      ceVolumeSlowSite d hd
        ((3 + 8 * ceVolumeGridN d hd t u : ℕ) : ℤ)
        (4 * ceVolumeGridK d hd t u + 1) (ceVolumeGridZ d t u) := by
  ext i
  by_cases hi0 : (i : ℕ) = 0
  · have hi : i = ⟨0, by omega⟩ := Fin.ext hi0
    rw [hi]
    simp [ceVolumeGridCenter, ceVolumeSlowSite, ceVolumeE₂, unit]
  · by_cases hi1 : (i : ℕ) = 1
    · have hi : i = ⟨1, by omega⟩ := Fin.ext hi1
      rw [hi]
      simp [ceVolumeGridCenter, ceVolumeSlowSite, ceVolumeE₂, unit]
    · let j : Fin (d - 2) := ⟨(i : ℕ) - 2, by omega⟩
      have hj : (⟨(j : ℕ) + 2, by omega⟩ : Fin d) = i := by
        apply Fin.ext
        dsimp [j]
        omega
      have hne : (⟨(j : ℕ) + 2, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by
        intro h
        have := congrArg Fin.val h
        dsimp [j] at this
        omega
      rw [← hj]
      change ceVolumeGridCenter d hd t u ⟨(j : ℕ) + 2, by omega⟩ +
          ceVolumeE₂ d hd ⟨(j : ℕ) + 2, by omega⟩ =
        ceVolumeSlowSite d hd ((3 + 8 * ceVolumeGridN d hd t u : ℕ) : ℤ)
          (4 * ceVolumeGridK d hd t u + 1) (ceVolumeGridZ d t u)
            ⟨(j : ℕ) + 2, by omega⟩
      rw [ceVolumeGridCenter_apply_extra]
      simp [ceVolumeSlowSite, ceVolumeE₂, unit, j, hne]

/-- Every selected grid cell lies in the symmetric difference with the translated
actual support. The slow-site zero and fast-site firing are used at the same scale. -/
theorem ceVolumeGridCell_subset_translationDiff (d : ℕ) (hd : 2 ≤ d) (t : ℕ)
    (ht : 1000000 * d ≤ t) (u : Fin d → Fin (ceVolumeGridM d t)) :
    ceVolumeCell d t (ceVolumeGridCenter d hd t u) ⊆
      symmDiff (ceVolumeAtTime d t)
        {y : Fin d → ℝ | y + ceVolumeShift d t hd ∈ ceVolumeAtTime d t} := by
  let σ : Site d → ℤ := fun x => ceEta d x + 3 * dirac (0 : Site d) x
  have htime := ceVolumeGrid_timing d hd t ht u
  have hslow : podo σ t (ceVolumeGridCenter d hd t u) = 0 := by
    simpa [σ, ceVolumeGridCenter] using
      (ce_podo_zero_signed_slow_site d hd (ceVolumeGridN d hd t u)
        htime.1 (ceVolumeGridK d hd t u) (ceVolumeGridZ d t u) t htime.2.1)
  have hdeadline :
      (3 + 8 * ceVolumeGridN d hd t u) + Int.natAbs (4 * ceVolumeGridK d hd t u) +
        (∑ i : Fin (d - 2), Int.natAbs (ceVolumeGridZ d t u i)) + 2 ≤ t :=
    htime.2.2
  have hfast :
      0 < podo σ
        ((3 + 8 * ceVolumeGridN d hd t u) + Int.natAbs (4 * ceVolumeGridK d hd t u) +
          (∑ i : Fin (d - 2), Int.natAbs (ceVolumeGridZ d t u i)) + 2)
        (ceVolumeGridCenter d hd t u + ceVolumeE₂ d hd) := by
    rw [ceVolumeGridCenter_add_e₂]
    simpa [σ] using
      (ce_podo_pos_signed_fast_site d hd (ceVolumeGridN d hd t u) htime.1
        (ceVolumeGridK d hd t u) (ceVolumeGridZ d t u))
  have hfastAtT :
      0 < podo σ t (ceVolumeGridCenter d hd t u + ceVolumeE₂ d hd) := by
    have hmono := ceVolumePodo_mono_time σ hdeadline
      (ceVolumeGridCenter d hd t u + ceVolumeE₂ d hd)
    exact lt_of_lt_of_le hfast hmono
  intro y hy
  have hsite : nearestSite ((t : ℝ) • y) = ceVolumeGridCenter d hd t u :=
    Set.mem_setOf_eq.mp hy
  have hyAbsent : y ∉ ceVolumeAtTime d t := by
    intro h
    change 0 < podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) t
      (nearestSite ((t : ℝ) • y)) at h
    rw [hsite, hslow] at h
    omega
  have hyShiftCell :
      y + ceVolumeShift d t hd ∈
        ceVolumeCell d t (ceVolumeGridCenter d hd t u + ceVolumeE₂ d hd) :=
    (ceVolumeCell_translate_mem d t hd (by omega)
      (ceVolumeGridCenter d hd t u) y).mp hy
  have hsiteShift :
      nearestSite ((t : ℝ) • (y + ceVolumeShift d t hd)) =
        ceVolumeGridCenter d hd t u + ceVolumeE₂ d hd :=
    Set.mem_setOf_eq.mp hyShiftCell
  have hyShiftPresent : y + ceVolumeShift d t hd ∈ ceVolumeAtTime d t := by
    change 0 < podo (fun x => ceEta d x + 3 * dirac (0 : Site d) x) t
      (nearestSite ((t : ℝ) • (y + ceVolumeShift d t hd)))
    rw [hsiteShift]
    simpa [σ] using hfastAtT
  apply Set.mem_symmDiff.mpr
  exact Or.inr ⟨hyShiftPresent, hyAbsent⟩

/-- The actual translated support differs by at least `c_d` inside the source box at
every scale `t ≥ 1,000,000 d`. The bound follows from the `m^d` disjoint grid cells. -/
theorem ce_volume_translation_lower (d : ℕ) (hd : 2 ≤ d) (t : ℕ)
    (ht : 1000000 * d ≤ t) :
    ENNReal.ofReal (ceVolumeLowerConstant d) ≤
      volume ((symmDiff (ceVolumeAtTime d t)
        {y : Fin d → ℝ | y + ceVolumeShift d t hd ∈ ceVolumeAtTime d t}) ∩
        ceVolumeGridOmega d hd) := by
  classical
  let S := ceVolumeGridCenters d hd t
  have hcard : S.card = (ceVolumeGridM d t) ^ d := by
    dsimp [S]
    exact ceVolumeGridCenters_card d hd t
  have hpair : Set.PairwiseDisjoint (↑S : Set (Site d)) (ceVolumeCell d t) := by
    intro x hx x' hx' hxx'
    exact ceVolumeCell_disjoint d t x x' hxx'
  have hmeas : ∀ x ∈ S, MeasurableSet (ceVolumeCell d t x) := by
    intro x hx
    exact measurableSet_ceVolumeCell d t x (by omega)
  have hunionSubset :
      (⋃ x ∈ S, ceVolumeCell d t x) ⊆
        (symmDiff (ceVolumeAtTime d t)
          {y : Fin d → ℝ | y + ceVolumeShift d t hd ∈ ceVolumeAtTime d t}) ∩
          ceVolumeGridOmega d hd := by
    intro y hy
    simp only [Set.mem_iUnion] at hy
    rcases hy with ⟨x, hx, hyx⟩
    have hxImage : x ∈ S := hx
    rcases Finset.mem_image.mp hxImage with ⟨u, hu, rfl⟩
    exact ⟨ceVolumeGridCell_subset_translationDiff d hd t ht u hyx,
      ceVolumeGridCell_subset d hd t ht u hyx⟩
  have hunionMeasure :
      volume (⋃ x ∈ S, ceVolumeCell d t x) =
        ENNReal.ofReal (((ceVolumeGridM d t : ℝ) / (t : ℝ)) ^ d) := by
    calc
      volume (⋃ x ∈ S, ceVolumeCell d t x) =
          ∑ x ∈ S, volume (ceVolumeCell d t x) := measure_biUnion_finset hpair hmeas
      _ = (S.card : ENNReal) * ENNReal.ofReal ((1 / (t : ℝ)) ^ d) := by
        simp_rw [ceVolumeCell_volume d t _ (by omega)]
        rw [Finset.sum_const, nsmul_eq_mul]
      _ = ENNReal.ofReal (((ceVolumeGridM d t : ℝ) / (t : ℝ)) ^ d) := by
        rw [hcard, ← ENNReal.ofReal_natCast ((ceVolumeGridM d t) ^ d)]
        rw [← ENNReal.ofReal_mul (by positivity :
          0 ≤ (((ceVolumeGridM d t) ^ d : ℕ) : ℝ))]
        congr 1
        push_cast
        field_simp
        ring
  have hratio :
      1 / (20000 * (d : ℝ)) ≤ (ceVolumeGridM d t : ℝ) / (t : ℝ) := by
    obtain ⟨_, _, hqhi, hdouble⟩ := ceVolumeGrid_division_bounds d hd t ht
    have hcoef : 2 * ceVolumeGridQ d * ceVolumeGridM d t =
        20000 * d * ceVolumeGridM d t := by
      simp [ceVolumeGridQ]
      omega
    have htupper : t ≤ 20000 * d * ceVolumeGridM d t :=
      Nat.le_of_lt (by rw [← hcoef]; exact lt_of_lt_of_le hqhi hdouble)
    have htposN : 0 < t := by omega
    have htpos : 0 < (t : ℝ) := by exact_mod_cast htposN
    have hdpos : 0 < 20000 * (d : ℝ) := by positivity
    rw [div_le_div_iff₀ hdpos htpos]
    have htupperR : (t : ℝ) ≤ 20000 * (d : ℝ) * (ceVolumeGridM d t : ℝ) := by
      exact_mod_cast htupper
    nlinarith [htupperR]
  have hpow :
      (1 / (20000 * (d : ℝ))) ^ d ≤
        ((ceVolumeGridM d t : ℝ) / (t : ℝ)) ^ d := by
    exact pow_le_pow_left₀ (by positivity) hratio d
  calc
    ENNReal.ofReal (ceVolumeLowerConstant d) ≤
        volume (⋃ x ∈ S, ceVolumeCell d t x) := by
      rw [hunionMeasure, ceVolumeLowerConstant]
      exact ENNReal.ofReal_le_ofReal hpow
    _ ≤ volume ((symmDiff (ceVolumeAtTime d t)
        {y : Fin d → ℝ | y + ceVolumeShift d t hd ∈ ceVolumeAtTime d t}) ∩
        ceVolumeGridOmega d hd) := measure_mono hunionSubset

end Exploding
