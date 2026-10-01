/-
The general-dimension Poincaré lemma modulo two, needed to extend the planar
`ec_star_conn` argument to `ℤ^d`: a closed one-cochain of edge functions is the
coboundary of a site function.  The proof splits off the first coordinate and
integrates along it, using the codimension-one slice as the inductive datum.
-/
import Exploding.Support.ECProofPoincare
import Exploding.Support.Percolation

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- Antiderivative in `ZMod 2` of a function of one integer variable. -/
noncomputable def xmh3_anti (g : ℤ → ZMod 2) : ℤ → ZMod 2 := Classical.choose (ec_cum_exists g)

theorem xmh3_anti_zero (g : ℤ → ZMod 2) : xmh3_anti g 0 = 0 :=
  (Classical.choose_spec (ec_cum_exists g)).1

theorem xmh3_anti_succ (g : ℤ → ZMod 2) (x : ℤ) :
    xmh3_anti g (x + 1) = xmh3_anti g x + g x :=
  (Classical.choose_spec (ec_cum_exists g)).2 x

/-- The antiderivative along the first coordinate of an edge function. -/
noncomputable def xmh3_antiFirst {n : ℕ}
    (H : (i : Fin (n+1)) → Site (n+1) → ZMod 2) (w : Site n) : ℤ → ZMod 2 :=
  xmh3_anti (fun t => H 0 (Fin.cons t w))

theorem xmh3_antiFirst_zero {n : ℕ}
    (H : (i : Fin (n+1)) → Site (n+1) → ZMod 2) (w : Site n) :
    xmh3_antiFirst H w 0 = 0 := xmh3_anti_zero _

theorem xmh3_antiFirst_succ {n : ℕ}
    (H : (i : Fin (n+1)) → Site (n+1) → ZMod 2) (w : Site n) (x : ℤ) :
    xmh3_antiFirst H w (x + 1) = xmh3_antiFirst H w x + H 0 (Fin.cons x w) :=
  xmh3_anti_succ _ x

/-! ### Elementary `Fin` manipulations -/

theorem xmh3_cons_zero_add {n : ℕ} (w : Site n) (i : Fin n) :
    Fin.cons (0 : ℤ) (w + unit i) = Fin.cons (0 : ℤ) w + unit i.succ := by
  ext j
  refine Fin.cases ?_ ?_ j
  · simp [Fin.cons_zero, unit]
  · intro k
    simp only [Fin.cons_succ, Pi.add_apply]
    by_cases h : k = i
    · subst h
      simp [unit, Pi.single_eq_same]
    · have h' : k.succ ≠ i.succ := fun hh => h (Fin.succ_inj.mp hh)
      simp [unit, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']

theorem xmh3_tail_add_succ {n : ℕ} (p : Site (n+1)) (i : Fin n) :
    Fin.tail (p + unit i.succ) = Fin.tail p + unit i := by
  ext j
  simp only [Fin.tail, Pi.add_apply]
  by_cases h : j = i
  · subst h
    simp [unit, Pi.single_eq_same]
  · have h' : j.succ ≠ i.succ := fun hh => h (Fin.succ_inj.mp hh)
    simp [unit, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']

theorem xmh3_self_cons {n : ℕ} (p : Site (n+1)) :
    Fin.cons (p 0) (Fin.tail p) = p := Fin.cons_self_tail p

theorem xmh3_add_zero_cons {n : ℕ} (p : Site (n+1)) :
    p + unit (0 : Fin (n+1)) = Fin.cons (p 0 + 1) (Fin.tail p) := by
  ext j
  refine Fin.cases ?_ ?_ j
  · simp [Fin.cons_zero, unit, Pi.single_eq_same]
  · intro k
    simp only [Fin.cons_succ, Fin.tail, Pi.add_apply]
    simp [unit]

theorem xmh3_add_succ_cons {n : ℕ} (p : Site (n+1)) (i : Fin n) :
    p + unit i.succ = Fin.cons (p 0) (Fin.tail p + unit i) := by
  ext j
  refine Fin.cases ?_ ?_ j
  · simp [Fin.cons_zero, unit]
  · intro k
    simp only [Fin.cons_succ, Fin.tail, Pi.add_apply]
    by_cases h : k = i
    · subst h
      simp [unit, Pi.single_eq_same]
    · have h' : k.succ ≠ i.succ := fun hh => h (Fin.succ_inj.mp hh)
      simp [unit, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']

/-! ### Telescoping the difference of the two antiderivatives -/

theorem xmh3_difference_zero {n : ℕ} (H : (i : Fin (n+1)) → Site (n+1) → ZMod 2)
    (hclosed : ∀ i j, i ≠ j → ∀ p : Site (n+1),
      H i p + H j (p + unit i) = H j p + H i (p + unit j))
    (w : Site n) (i : Fin n) :
    ∀ x : ℤ, xmh3_antiFirst H (w + unit i) x - xmh3_antiFirst H w x =
      H i.succ (Fin.cons x w) - H i.succ (Fin.cons 0 w) := by
  set f : ℤ → ZMod 2 := fun x => xmh3_antiFirst H (w + unit i) x - xmh3_antiFirst H w x
    - (H i.succ (Fin.cons x w) - H i.succ (Fin.cons 0 w))
  have hstep : ∀ x, f (x + 1) = f x := by
    intro x
    have h := hclosed 0 i.succ (Fin.succ_ne_zero i).symm (Fin.cons x w)
    rw [xmh3_add_zero_cons (Fin.cons x w),
      xmh3_add_succ_cons (Fin.cons x w) i, Fin.tail_cons, Fin.cons_zero] at h
    simp only [f, xmh3_antiFirst_succ]
    rw [← sub_eq_zero]
    have key : H 0 (Fin.cons x (w + unit i)) + H i.succ (Fin.cons x w)
        = H 0 (Fin.cons x w) + H i.succ (Fin.cons (x + 1) w) := by
      rw [add_comm (H 0 (Fin.cons x (w + unit i))) (H i.succ (Fin.cons x w))]
      exact h.symm
    linear_combination key
  have hf0 : f 0 = 0 := by simp [f, xmh3_antiFirst_zero]
  intro x
  have hx : f x = 0 := by
    induction x using Int.induction_on with
    | zero => exact hf0
    | succ m hm => exact (hstep m).trans hm
    | pred m hm =>
        have e : -(m : ℤ) - 1 + 1 = -(m : ℤ) := by ring
        have h := hstep (-(m : ℤ) - 1)
        rw [e] at h
        exact h.symm.trans hm
  simpa only [f, sub_eq_zero] using hx

/-! ### The Poincaré lemma -/

theorem xmh3_poincare (d : ℕ) (H : (i : Fin d) → Site d → ZMod 2)
    (hclosed : ∀ i j, i ≠ j → ∀ p : Site d,
      H i p + H j (p + unit i) = H j p + H i (p + unit j)) :
    ∃ F : Site d → ZMod 2, ∀ i p, F (p + unit i) = F p + H i p := by
  induction d with
  | zero => exact ⟨fun _ => 0, fun i => Fin.elim0 i⟩
  | succ n ih =>
    set H' : (i : Fin n) → Site n → ZMod 2 := fun i w => H i.succ (Fin.cons 0 w)
    have hclosed' : ∀ i j, i ≠ j → ∀ w : Site n,
        H' i w + H' j (w + unit i) = H' j w + H' i (w + unit j) := by
      intro i j hij w
      have h := hclosed i.succ j.succ (fun hh => hij (Fin.succ_inj.mp hh)) (Fin.cons 0 w)
      simp only [H'] at h ⊢
      rw [← xmh3_cons_zero_add w i, ← xmh3_cons_zero_add w j] at h
      exact h
    obtain ⟨P, hP⟩ := ih H' hclosed'
    refine ⟨fun p => xmh3_antiFirst H (Fin.tail p) (p 0) + P (Fin.tail p), ?_⟩
    intro i p
    refine Fin.cases ?_ ?_ i
    · rw [xmh3_add_zero_cons p]
      simp only [Fin.tail_cons, Fin.cons_zero]
      rw [xmh3_antiFirst_succ, xmh3_self_cons p]
      ring
    · intro i
      have htel : xmh3_antiFirst H (Fin.tail p + unit i) (p 0)
            - xmh3_antiFirst H (Fin.tail p) (p 0)
          = H i.succ p - H i.succ (Fin.cons 0 (Fin.tail p)) := by
        have h := xmh3_difference_zero H hclosed (Fin.tail p) i (p 0)
        rwa [xmh3_self_cons p] at h
      rw [xmh3_add_succ_cons p i]
      simp only [Fin.tail_cons, Fin.cons_zero]
      rw [hP i (Fin.tail p)]
      simp only [H']
      rw [show xmh3_antiFirst H (Fin.tail p + unit i) (p 0)
            = xmh3_antiFirst H (Fin.tail p) (p 0)
              + (H i.succ p - H i.succ (Fin.cons 0 (Fin.tail p))) by
          rw [← htel]; ring]
      ring

end Exploding
