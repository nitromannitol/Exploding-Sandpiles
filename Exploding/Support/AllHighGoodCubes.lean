import Exploding.Support.CrossingTimeAux
import Exploding.Support.ArxivP1Crossing

/-!
# All-high good cubes at every scale

Every line of a nonempty cube contains a high site in the constant all-high
configuration. The deterministic propagation theorem therefore makes every
cube good, including all its translates. Under the actual parameter-one law,
all macroscopic sites are consequently good at every positive scale.
-/

namespace Exploding

open LatticeProb MeasureTheory

/-- The constant all-high configuration is good at every scale. At scale zero
the cube and its closure are empty, so that case is vacuous. -/
theorem all_high_good_cube (d : ℕ) (hd : 2 ≤ d) (k : ℕ) :
    GoodCube (fun _ : Site d => 2 * (d : ℤ) - 1) k := by
  apply aux_ct_propagate d k hd (fun _ : Site d => 2 * (d : ℤ) - 1)
  · intro x
    exact ⟨by omega, le_rfl⟩
  · intro i y hy
    exact ⟨y, ⟨hy i, fun _ _ => rfl⟩, rfl⟩

/-- Every translated all-high cube is good. -/
theorem all_high_good_at (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (i : Site d) :
    GoodAt (fun _ : Site d => 2 * (d : ℤ) - 1) k i := by
  exact all_high_good_cube d hd k

/-- All macroscopic sites are good for the all-high configuration. -/
theorem all_high_good_sites_eq_univ (d : ℕ) (hd : 2 ≤ d) (k : ℕ) :
    goodSites (fun _ : Site d => 2 * (d : ℤ) - 1) k = Set.univ := by
  exact Set.eq_univ_of_forall (all_high_good_at d hd k)

/-- Under the actual parameter-one law, every macroscopic site is good
simultaneously at every positive scale. -/
theorem good_sites_all_scales_p1 (d : ℕ) (hd : 2 ≤ d) :
    ∀ᵐ η ∂(toyLaw d (1 : ℝ)),
      ∀ k : ℕ, 1 ≤ k → goodSites η k = Set.univ := by
  rw [toyLaw_one_eq_dirac, MeasureTheory.ae_dirac_eq]
  simp only [Filter.Eventually, Filter.mem_pure]
  intro k _hk
  exact all_high_good_sites_eq_univ d hd k

end Exploding
