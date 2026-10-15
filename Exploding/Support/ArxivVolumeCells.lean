import Exploding.Support.ArxivVolumeSlow

/-!
# Nearest-site cells and their volume

At a positive integer scale, the actual nearest-site map partitions Euclidean space
into coordinate boxes that are open at their left faces and closed at their right
faces. These cells are measurable and have the expected exact Lebesgue volume.
-/

namespace Exploding

open LatticeProb MeasureTheory

/-- The points whose scaled nearest site is `x`, using the project's actual rounding map. -/
def ceVolumeCell (d t : ℕ) (x : Site d) : Set (Fin d → ℝ) :=
  {y | nearestSite ((t : ℝ) • y) = x}

/-- A scaled nearest-site cell is the product of half-open coordinate intervals.
The left endpoint is excluded and the right endpoint is included. -/
theorem ceVolumeCell_mem_iff (d t : ℕ) (x : Site d) (ht : 1 ≤ t)
    (y : Fin d → ℝ) :
    y ∈ ceVolumeCell d t x ↔ ∀ i : Fin d,
      (((x i : ℤ) : ℝ) - 1 / 2) / (t : ℝ) < y i ∧
        y i ≤ (((x i : ℤ) : ℝ) + 1 / 2) / (t : ℝ) := by
  change nearestSite ((t : ℝ) • y) = x ↔ _
  have htpos : 0 < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
  constructor
  · intro h i
    have hceil : ⌈(t : ℝ) * y i - 1 / 2⌉ = x i := by
      simpa only [nearestSite, Pi.smul_apply, smul_eq_mul] using congrFun h i
    have hceil' := Int.ceil_eq_iff.mp hceil
    constructor
    · apply (div_lt_iff₀ htpos).2
      rcases hceil' with ⟨hleft, _⟩
      nlinarith
    · apply (le_div_iff₀ htpos).2
      rcases hceil' with ⟨_, hright⟩
      nlinarith
  · intro h
    funext i
    apply Int.ceil_eq_iff.mpr
    simp only [Pi.smul_apply, smul_eq_mul]
    constructor
    · have hleft := (div_lt_iff₀ htpos).mp (h i).1
      nlinarith
    · have hright := (le_div_iff₀ htpos).mp (h i).2
      nlinarith

/-- A nearest-site cell is exactly a finite product of `Ioc` intervals. -/
theorem ceVolumeCell_eq_pi_Ioc (d t : ℕ) (x : Site d) (ht : 1 ≤ t) :
    ceVolumeCell d t x = Set.pi Set.univ (fun i : Fin d =>
      Set.Ioc ((((x i : ℤ) : ℝ) - 1 / 2) / (t : ℝ))
        ((((x i : ℤ) : ℝ) + 1 / 2) / (t : ℝ))) := by
  ext y
  rw [ceVolumeCell_mem_iff d t x ht y]
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioc]

/-- The actual nearest-site cells at a fixed positive scale are pairwise disjoint. -/
theorem ceVolumeCell_disjoint (d t : ℕ) (x x' : Site d) (hxx' : x ≠ x') :
    Disjoint (ceVolumeCell d t x) (ceVolumeCell d t x') := by
  rw [Set.disjoint_left]
  intro y hy hy'
  exact hxx' ((Set.mem_setOf_eq.mp hy).symm.trans (Set.mem_setOf_eq.mp hy'))

/-- Every positive-scale nearest-site cell is Lebesgue measurable. -/
theorem measurableSet_ceVolumeCell (d t : ℕ) (x : Site d) (ht : 1 ≤ t) :
    MeasurableSet (ceVolumeCell d t x) := by
  rw [ceVolumeCell_eq_pi_Ioc d t x ht]
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)

/-- The exact `ENNReal` Lebesgue volume of a positive-scale nearest-site cell. -/
theorem ceVolumeCell_volume (d t : ℕ) (x : Site d) (ht : 1 ≤ t) :
    volume (ceVolumeCell d t x) = ENNReal.ofReal ((1 / (t : ℝ)) ^ d) := by
  rw [ceVolumeCell_eq_pi_Ioc d t x ht, Real.volume_pi_Ioc]
  have hwidth (i : Fin d) :
      ((((x i : ℤ) : ℝ) + 1 / 2) / (t : ℝ)) -
          ((((x i : ℤ) : ℝ) - 1 / 2) / (t : ℝ)) = 1 / (t : ℝ) := by
    field_simp
    ring
  simp_rw [hwidth]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ (1 / (t : ℝ) : ℝ)) d]

/-- At scale one in dimension one, the left face for the zero site is excluded
and the right face is included, matching the tie-breaking in `nearestSite`. -/
theorem ceVolumeCell_unit_endpoints :
    (fun _ : Fin 1 => (-1 / 2 : ℝ)) ∉ ceVolumeCell 1 1 (0 : Site 1) ∧
    (fun _ : Fin 1 => (1 / 2 : ℝ)) ∈ ceVolumeCell 1 1 (0 : Site 1) := by
  constructor
  · intro h
    have hcoord := (ceVolumeCell_mem_iff 1 1 (0 : Site 1) (by norm_num)
      (fun _ : Fin 1 => (-1 / 2 : ℝ))).mp h 0
    norm_num at hcoord
  · rw [ceVolumeCell_mem_iff 1 1 (0 : Site 1) (by norm_num)]
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    norm_num

/-- The second coordinate unit site, available in dimensions at least two. -/
def ceVolumeE₂ (d : ℕ) (hd : 2 ≤ d) : Site d :=
  unit ⟨1, by omega⟩

/-- Translation by the second coordinate unit vector divided by the scale. -/
noncomputable def ceVolumeShift (d t : ℕ) (hd : 2 ≤ d) : Fin d → ℝ :=
  fun i => ((ceVolumeE₂ d hd i : ℤ) : ℝ) / (t : ℝ)

/-- Adding an integer vector before rounding translates the actual nearest site by it. -/
theorem nearestSite_add_int {d : ℕ} (y : Fin d → ℝ) (z : Site d) :
    nearestSite (y + fun i => (z i : ℝ)) = nearestSite y + z := by
  funext i
  change ⌈y i + (z i : ℝ) - 1 / 2⌉ = ⌈y i - 1 / 2⌉ + z i
  rw [show y i + (z i : ℝ) - 1 / 2 = (z i : ℝ) + (y i - 1 / 2) by ring]
  rw [Int.ceil_intCast_add]
  abel

/-- Scaling a translated point by `t` adds the second coordinate unit vector. -/
theorem ceVolume_scale_shift (d t : ℕ) (hd : 2 ≤ d) (ht : 1 ≤ t)
    (y : Fin d → ℝ) :
    (t : ℝ) • (y + ceVolumeShift d t hd) =
      (t : ℝ) • y + fun i => (ceVolumeE₂ d hd i : ℝ) := by
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
  ext i
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  dsimp [ceVolumeShift]
  field_simp

/-- Translation by `e₂/t` carries membership in the cell of `x` to the cell of
`x + e₂`, with the converse holding as well. -/
theorem ceVolumeCell_translate_mem (d t : ℕ) (hd : 2 ≤ d) (ht : 1 ≤ t)
    (x : Site d) (y : Fin d → ℝ) :
    y ∈ ceVolumeCell d t x ↔
      y + ceVolumeShift d t hd ∈ ceVolumeCell d t (x + ceVolumeE₂ d hd) := by
  change nearestSite ((t : ℝ) • y) = x ↔
    nearestSite ((t : ℝ) • (y + ceVolumeShift d t hd)) = x + ceVolumeE₂ d hd
  rw [ceVolume_scale_shift d t hd ht y, nearestSite_add_int]
  constructor
  · intro h
    simp [h]
  · exact add_right_cancel

/-- Translation by `e₂/t` maps each cell exactly onto the cell of `x + e₂`. -/
theorem ceVolumeCell_translate (d t : ℕ) (hd : 2 ≤ d) (ht : 1 ≤ t)
    (x : Site d) :
    Set.image (fun y : Fin d → ℝ => y + ceVolumeShift d t hd) (ceVolumeCell d t x) =
      ceVolumeCell d t (x + ceVolumeE₂ d hd) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (ceVolumeCell_translate_mem d t hd ht x z).mp hz
  · intro hy
    refine ⟨y - ceVolumeShift d t hd, ?_, ?_⟩
    · apply (ceVolumeCell_translate_mem d t hd ht x (y - ceVolumeShift d t hd)).mpr
      simpa using hy
    · simp

end Exploding
