/-
Deterministic growth along the schedule: the seed box is toppled, each layer added by the
schedule lies next to the current box in a direction of `J` and is spanned along the other
directions, so by growth by a layer (`xsb_grow_up`, `xsb_grow_down`) every box of the schedule is
toppled inside `B`; the last box is the target.
-/
import Exploding.Support.ExtSchSchedGeom
import Exploding.Support.ExtSchSchedLayer

namespace Exploding

open LatticeProb

variable {d : ℕ}

section Grow
variable (P : xss_Plan d) {s : ℕ}

/-- Every box of the schedule up to its last step is toppled inside `B`, by induction on the
step, adding one layer at a time. -/
theorem xsg2_top_box (hP : xss_Valid P s) (hL : 1 ≤ P.L)
    {B : Set (Site d)} (hB : xsb_box P.LO P.HI ⊆ B) {η : Site d → ℤ}
    (hseed : ∀ x ∈ xsb_box P.lo0 P.hi0, xsch_Top P.J B η x)
    (hlayers : ∀ t < xss_steps P s,
      xsch_Sp (P.J.erase (xss_dir P hP.1 t)) (xss_layer P t) η) :
    ∀ n, n ≤ xss_steps P s → ∀ x ∈ xss_box P n, xsch_Top P.J B η x := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [xss_box_zero P hP]
    exact hseed
  | succ t ih =>
    intro ht
    have hT : ∀ x ∈ xsb_box (xss_lo P t) (xss_hi P t), xsch_Top P.J B η x :=
      ih (Nat.le_of_succ_le ht)
    have hlt : t < xss_steps P s := ht
    have hne : ∀ j, xss_lo P t j ≤ xss_hi P t j := fun j => (xsg_corners_le P hP hL t j).2.1
    have hLB : xss_layer P t ⊆ B := (xss_layer_subset_target P hP t).trans hB
    rcases xss_step_shape P hP t with h | ⟨hbox, hlay⟩ | ⟨hbox, hlay⟩
    · rw [h]
      exact hT
    · rw [hbox]
      have hLB' : xsb_layerUp (xss_lo P t) (xss_hi P t) (xss_dir P hP.1 t) ⊆ B := by
        rw [← hlay]
        exact hLB
      have hSp : xsch_Sp (P.J.erase (xss_dir P hP.1 t))
          (xsb_layerUp (xss_lo P t) (xss_hi P t) (xss_dir P hP.1 t)) η := by
        rw [← hlay]
        exact hlayers t hlt
      exact xsb_grow_up (xss_dir_mem P hP.1 t) hne hT hLB' hSp
    · rw [hbox]
      have hLB' : xsb_layerDown (xss_lo P t) (xss_hi P t) (xss_dir P hP.1 t) ⊆ B := by
        rw [← hlay]
        exact hLB
      have hSp : xsch_Sp (P.J.erase (xss_dir P hP.1 t))
          (xsb_layerDown (xss_lo P t) (xss_hi P t) (xss_dir P hP.1 t)) η := by
        rw [← hlay]
        exact hlayers t hlt
      exact xsb_grow_down (xss_dir_mem P hP.1 t) hne hT hLB' hSp

/-- **Growth along the schedule.** -/
theorem xsr_top_of_layers (hP : xss_Valid P s) (hL : 1 ≤ P.L)
    {B : Set (Site d)} (hB : xsb_box P.LO P.HI ⊆ B) {η : Site d → ℤ}
    (hseed : ∀ x ∈ xsb_box P.lo0 P.hi0, xsch_Top P.J B η x)
    (hlayers : ∀ t < xss_steps P s,
      xsch_Sp (P.J.erase (xss_dir P hP.1 t)) (xss_layer P t) η) :
    ∀ x ∈ xsb_box P.LO P.HI, xsch_Top P.J B η x := by
  rw [← xss_box_final P hP]
  exact xsg2_top_box P hP hL hB hseed hlayers _ le_rfl

end Grow

end Exploding
