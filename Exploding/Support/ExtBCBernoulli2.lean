/-
Measurability of the Bernoulli site box-crossing event: it is determined by the
finitely many coordinates in the box.
-/
import Exploding.Support.ExtBCBernoulli

open Exploding LatticeProb MeasureTheory Filter
open scoped Classical Topology ENNReal

namespace Exploding

variable {d : ℕ}

/-- A set of configurations determined by finitely many coordinates is measurable. -/
theorem xbc_measurableSet_of_determined {S : Type*} (F : Finset S) (E : Set (S → Bool))
    (hE : ∀ ω ω' : S → Bool, (∀ z ∈ F, ω z = ω' z) → (ω ∈ E ↔ ω' ∈ E)) :
    MeasurableSet E := by
  classical
  set π : (S → Bool) → (F → Bool) := fun ω z => ω z with hπ
  have hπm : Measurable π := measurable_pi_lambda _ fun z => measurable_pi_apply _
  have hsat : E = π ⁻¹' (π '' E) := by
    ext ω
    refine ⟨fun h => ⟨ω, h, rfl⟩, ?_⟩
    rintro ⟨ω', hω', hωω'⟩
    refine (hE ω' ω ?_).mp hω'
    intro z hz
    exact congrFun hωω' ⟨z, hz⟩
  rw [hsat]
  exact hπm (Set.Finite.measurableSet (Set.toFinite _))

/-- The lattice box `xap11_ball` is the sup-norm box `cent`. -/
theorem xbc_mem_ball {n : ℕ} {x : Site d} : x ∈ xap11_ball d n ↔ x ∈ cent d n := by
  rw [xap11_ball, Fintype.mem_piFinset, cent]
  simp only [Finset.mem_Icc, Set.mem_setOf_eq]
  constructor
  · intro h i
    rw [abs_le]
    exact ⟨by linarith [(h i).1], (h i).2⟩
  · intro h i
    have := (abs_le.mp (h i))
    exact ⟨this.1, this.2⟩

/-- The crossing event depends only on the coordinates in the box. -/
theorem xbc_crosses_determined (n : ℕ) (i : Fin d) (ω ω' : Site d → Bool)
    (h : ∀ z ∈ xap11_ball d n, ω z = ω' z) :
    xbc_Crosses d n i ω ↔ xbc_Crosses d n i ω' := by
  constructor
  · rintro ⟨x, y, hx, hy, hxb, hyb, hpath⟩
    refine ⟨x, y, hx, hy, hxb, hyb, ?_⟩
    refine xap_rtg_mono (fun a b hab => ?_) hpath
    refine ⟨hab.1, hab.2.1, hab.2.2.1, ?_, ?_⟩
    · rw [← h a (xbc_mem_ball.mpr hab.2.1)]
      exact hab.2.2.2.1
    · rw [← h b (xbc_mem_ball.mpr hab.2.2.1)]
      exact hab.2.2.2.2
  · rintro ⟨x, y, hx, hy, hxb, hyb, hpath⟩
    refine ⟨x, y, hx, hy, hxb, hyb, ?_⟩
    refine xap_rtg_mono (fun a b hab => ?_) hpath
    refine ⟨hab.1, hab.2.1, hab.2.2.1, ?_, ?_⟩
    · rw [h a (xbc_mem_ball.mpr hab.2.1)]
      exact hab.2.2.2.1
    · rw [h b (xbc_mem_ball.mpr hab.2.2.1)]
      exact hab.2.2.2.2

/-- The Bernoulli site box-crossing event is measurable. -/
theorem xbc_measurableSet_Crosses (n : ℕ) (i : Fin d) :
    MeasurableSet {ω : Site d → Bool | xbc_Crosses d n i ω} :=
  xbc_measurableSet_of_determined (xap11_ball d n) _
    fun _ _ h => xbc_crosses_determined n i _ _ h

/-- **The star duality.**  If the box has no open nearest-neighbour crossing in direction
`i`, then it contains a star-connected closed barrier of at least the box side length.  This
is the standard planar / hypersurface duality (a minimal closed cut has at least the side
length), stated here as the reusable finite input of the supercritical box-crossing lemma. -/
def xbc_StarDuality (d : ℕ) : Prop :=
  ∀ (n : ℕ) (i : Fin d) (ω : Site d → Bool), ¬ xbc_Crosses d n i ω →
    ∃ s : ℕ, 2 * n + 1 ≤ s ∧
      ∃ Γ ∈ xap11_starSets (xap11_ball d n) s, ∀ z ∈ Γ, ω z = false

end Exploding
