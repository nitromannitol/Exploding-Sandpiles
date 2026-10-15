import Exploding.Support.CrossingTimeAux
import Exploding.Support.SubCrossTime
import Exploding.Support.ArxivP1Crossing

/-!
# Terminal-one characterization for finite crossing cubes

For a background bounded above by the top height in the actual law, the delivered-seed
crossing odometer stays at most one and is nondecreasing. On the finite cube, coordinatewise
eventual value one is therefore equivalent to a common positive all-one time. The toy law has
this height bound throughout its source parameter range, including its Dirac endpoint, so the
existing positive volume deadline characterizes the same event together with terminal value one.
-/

namespace Exploding

open LatticeProb MeasureTheory
open scoped Classical

/-- On a background bounded by `2d - 1`, terminal value one at each cube site is equivalent
to a common positive time at which the delivered-seed crossing odometer is one on the cube. -/
theorem crossOdo_terminal_one_iff {d : ℕ}
    (η : Site d → ℤ)
    (hη : ∀ x : Site d, η x ≤ 2 * (d : ℤ) - 1)
    (k : ℕ) (i : Fin d) (z : Site d) :
    (∀ x ∈ cube d k, ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      crossOdo η k i z t x = 1) ↔
      ∃ n : ℕ, 1 ≤ n ∧
        ∀ x ∈ cube d k, crossOdo η k i z n x = 1 := by
  let S : Set (Site d) := (cube d k)ᶜ ∪ line d k i z
  let w0 : Site d → ℤ := fun x => if x ∈ line d k i z then 1 else 0
  have hw0_le : ∀ x, w0 x ≤ 1 := by
    intro x
    dsimp [w0]
    split_ifs <;> norm_num
  have hw0_nonneg : ∀ x, 0 ≤ w0 x := by
    intro x
    dsimp [w0]
    split_ifs <;> norm_num
  have hupper (t : ℕ) (x : Site d) : crossOdo η k i z t x ≤ 1 := by
    change fodo S η w0 t x ≤ 1
    exact fodo_le_one S η w0 hη hw0_le hw0_nonneg t x
  have hmono {s t : ℕ} (hst : s ≤ t) (x : Site d) :
      crossOdo η k i z s x ≤ crossOdo η k i z t x := by
    simpa [crossOdo, S, w0] using
      (aux_ct_propagate_fodo_mono_time S η w0 hst x)
  constructor
  · intro h
    have htail : ∀ x ∈ cube d k,
        ∀ᶠ t : ℕ in Filter.atTop, crossOdo η k i z t x = 1 := by
      intro x hx
      obtain ⟨T, hT⟩ := h x hx
      rw [Filter.eventually_atTop]
      exact ⟨T, fun t ht => hT t ht⟩
    have hcommon : ∀ᶠ t : ℕ in Filter.atTop,
        ∀ x ∈ cube d k, crossOdo η k i z t x = 1 :=
      (Filter.eventually_all_finite (aux_ct_assemble_cube_finite d k)).2 htail
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hcommon
    refine ⟨max 1 T, by omega, ?_⟩
    intro x hx
    exact hT (max 1 T) (by omega) x hx
  · rintro ⟨n, _hn, hhit⟩ x hx
    refine ⟨n, ?_⟩
    intro t hnt
    have hlow := hmono hnt x
    rw [hhit x hx] at hlow
    exact le_antisymm (hupper t x) hlow

/-- Under the actual toy law, every site almost surely has one of its two source heights,
for all `0 < p ≤ 1`, including the all-high Dirac endpoint. -/
theorem toyLaw_ae_height_bounds (d : ℕ) (hd : 2 ≤ d)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    ∀ᵐ η ∂(toyLaw d p), ∀ x : Site d,
      2 * (d : ℤ) - 2 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1 := by
  rcases lt_or_eq_of_le hp1 with hplt | heq
  · exact aux_ct_ae_bounded d hd p hp hplt
  · subst p
    rw [toyLaw_one_eq_dirac, MeasureTheory.ae_dirac_eq]
    simp only [Filter.Eventually, Filter.mem_pure]
    intro x
    change 2 * (d : ℤ) - 2 ≤ 2 * (d : ℤ) - 1 ∧
      2 * (d : ℤ) - 1 ≤ 2 * (d : ℤ) - 1
    constructor <;> omega

/-- Almost surely, the existing positive volume-bounded crossing witness on every permitted
seed is equivalent to terminal value one on the cube together with that same deadline witness. -/
theorem toyLaw_ae_goodCube_terminal_iff (d : ℕ) (hd : 2 ≤ d)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    ∀ᵐ η ∂(toyLaw d p), ∀ k : ℕ,
      GoodCube η k ↔
        ∀ (i : Fin d) (z : Site d), z ∈ closureN (cube d k) →
          (∀ x ∈ cube d k, ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
            crossOdo η k i z t x = 1) ∧
          (∃ n : ℕ, 1 ≤ n ∧ n ≤ k ^ d ∧
            ∀ x ∈ cube d k, crossOdo η k i z n x = 1) := by
  filter_upwards [toyLaw_ae_height_bounds d hd p hp hp1] with η hη
  intro k
  constructor
  · intro hgood i z hz
    obtain ⟨n, hn1, hnk, hhit⟩ :=
      (crossingTime_le_iff η k i z (k ^ d)).mp (hgood i z hz)
    constructor
    · exact (crossOdo_terminal_one_iff η (fun x => (hη x).2) k i z).2
        ⟨n, hn1, hhit⟩
    · exact ⟨n, hn1, hnk, hhit⟩
  · intro h i z hz
    obtain ⟨_, ⟨n, hn1, hnk, hhit⟩⟩ := h i z hz
    exact (crossingTime_le_iff η k i z (k ^ d)).2 ⟨n, hn1, hnk, hhit⟩

end Exploding
