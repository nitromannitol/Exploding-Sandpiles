/-
The mod-two Poincare lemma for the finite box `cent d n`: a one-cochain of edge
functions that is closed on every unit square lying in the box is the coboundary of a
site function on the box.  This is the finite-box analogue of `xmh3_poincare`, proved
by splitting off the first coordinate and integrating along the interval `[-n, n]`.
-/
import Exploding.Support.ExtMHProof4
import Exploding.Support.Percolation

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-! ### Antiderivative with a box base -/

/-- Antiderivative in `ZMod 2` of a function of one integer variable, normalised at
`-n`. -/
noncomputable def xmb_antiN (n : ℕ) (g : ℤ → ZMod 2) : ℤ → ZMod 2 :=
  fun x => xmh3_anti g x - xmh3_anti g (-(n : ℤ))

theorem xmb_antiN_neg (n : ℕ) (g : ℤ → ZMod 2) : xmb_antiN n g (-(n : ℤ)) = 0 := by
  simp [xmb_antiN]

theorem xmb_antiN_succ (n : ℕ) (g : ℤ → ZMod 2) (x : ℤ) :
    xmb_antiN n g (x + 1) = xmb_antiN n g x + g x := by
  simp only [xmb_antiN, xmh3_anti_succ]
  abel

/-! ### `Fin.cons` helpers -/

theorem xmb_cons_add {m : ℕ} (c : ℤ) (w : Site m) (i : Fin m) :
    Fin.cons c (w + unit i) = Fin.cons c w + unit i.succ := by
  ext j
  refine Fin.cases ?_ ?_ j
  · simp [Fin.cons_zero, unit]
  · intro k
    simp only [Fin.cons_succ, Pi.add_apply]
    by_cases h : k = i
    · subst h; simp [unit, Pi.single_eq_same]
    · have h' : k.succ ≠ i.succ := fun hh => h (Fin.succ_inj.mp hh)
      simp [unit, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']

/-- A `Fin.cons` lies in the box when its head and tail do. -/
theorem xmb_cons_mem_cent {m n : ℕ} {t : ℤ} {w : Site m}
    (ht : |t| ≤ (n : ℤ)) (hw : w ∈ cent m n) : Fin.cons t w ∈ cent (m + 1) n := by
  intro j
  refine Fin.cases ?_ ?_ j
  · simpa using ht
  · intro l; simpa using hw l

/-! ### The bounded telescoping identity -/

theorem xmb_box_difference (n m : ℕ) (H : (i : Fin (m + 1)) → Site (m + 1) → ZMod 2)
    (hclosed : ∀ i j : Fin (m + 1), i ≠ j → ∀ p : Site (m + 1), p ∈ cent (m + 1) n →
      p + unit i ∈ cent (m + 1) n → p + unit j ∈ cent (m + 1) n →
      H i p + H j (p + unit i) = H j p + H i (p + unit j))
    (w : Site m) (hw : w ∈ cent m n) (i : Fin m) (hwi : w + unit i ∈ cent m n)
    {x : ℤ} (hx : -(n : ℤ) ≤ x) (hxn : x ≤ (n : ℤ)) :
    xmb_antiN n (fun t => H 0 (Fin.cons t (w + unit i))) x
        - xmb_antiN n (fun t => H 0 (Fin.cons t w)) x
      = H i.succ (Fin.cons x w) - H i.succ (Fin.cons (-(n : ℤ)) w) := by
  set g0 : ℤ → ZMod 2 := fun t => H 0 (Fin.cons t w) with hg0
  set g1 : ℤ → ZMod 2 := fun t => H 0 (Fin.cons t (w + unit i)) with hg1
  set F : ℤ → ZMod 2 := fun t => xmb_antiN n g1 t - xmb_antiN n g0 t
    - (H i.succ (Fin.cons t w) - H i.succ (Fin.cons (-(n : ℤ)) w)) with hF
  have hstep : ∀ t : ℤ, -(n : ℤ) ≤ t → t ≤ (n : ℤ) - 1 → F (t + 1) = F t := by
    intro t ht htlt
    have htabs : |t| ≤ (n : ℤ) := abs_le.mpr ⟨ht, by omega⟩
    have ht1abs : |t + 1| ≤ (n : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
    have e0 : Fin.cons t w + unit (0 : Fin (m + 1)) = Fin.cons (t + 1) w := by
      rw [xmh3_add_zero_cons (Fin.cons t w)]; simp
    have e1 : Fin.cons t w + unit i.succ = Fin.cons t (w + unit i) := by
      rw [xmh3_add_succ_cons (Fin.cons t w) i]; simp
    have hp0 : Fin.cons t w ∈ cent (m + 1) n := xmb_cons_mem_cent htabs hw
    have hp1 : Fin.cons t w + unit (0 : Fin (m + 1)) ∈ cent (m + 1) n := by
      rw [e0]; exact xmb_cons_mem_cent ht1abs hw
    have hp2 : Fin.cons t w + unit i.succ ∈ cent (m + 1) n := by
      rw [e1]; exact xmb_cons_mem_cent htabs hwi
    have hc := hclosed 0 i.succ (Fin.succ_ne_zero i).symm (Fin.cons t w) hp0 hp1 hp2
    rw [e0, e1] at hc
    have key : g1 t - g0 t
        = H i.succ (Fin.cons (t + 1) w) - H i.succ (Fin.cons t w) := by
      simp only [hg0, hg1] at hc ⊢
      rw [sub_eq_sub_iff_add_eq_add]
      rw [add_comm (H 0 (Fin.cons t (w + unit i))),
        add_comm (H i.succ (Fin.cons (t + 1) w))]
      exact hc.symm
    have hsub : F (t + 1) - F t = 0 := by
      have e : F (t + 1) - F t
          = (g1 t - g0 t)
            - (H i.succ (Fin.cons (t + 1) w) - H i.succ (Fin.cons t w)) := by
        simp only [hF, xmb_antiN_succ]
        ring
      rw [e, key, sub_self]
    exact sub_eq_zero.mp hsub
  have hFk : ∀ k : ℕ, k ≤ 2 * n → F (-(n : ℤ) + (k : ℤ)) = 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [Nat.cast_zero, add_zero]
      simp [hF, xmb_antiN_neg]
    | succ k ih =>
      intro hk
      have hk' : k ≤ 2 * n := by omega
      have hkn : (k : ℤ) ≤ 2 * (n : ℤ) := by exact_mod_cast hk'
      have hstepk := hstep (-(n : ℤ) + (k : ℤ)) (by omega) (by omega)
      have e : -(n : ℤ) + ((k + 1 : ℕ) : ℤ) = -(n : ℤ) + (k : ℤ) + 1 := by push_cast; ring
      rw [e, hstepk, ih hk']
  have hxint : x = -(n : ℤ) + (((x + n).toNat : ℕ) : ℤ) := by
    have h0 : 0 ≤ x + (n : ℤ) := by omega
    rw [Int.toNat_of_nonneg h0]; ring
  have hk2 : (x + n).toNat ≤ 2 * n := by
    have h0 : (0 : ℤ) ≤ x + (n : ℤ) := by omega
    have hcast : (((x + n).toNat : ℕ) : ℤ) = x + (n : ℤ) := Int.toNat_of_nonneg h0
    have : (((x + n).toNat : ℕ) : ℤ) ≤ ((2 * n : ℕ) : ℤ) := by
      rw [hcast]; push_cast; omega
    exact_mod_cast this
  have hfin := hFk ((x + n).toNat) hk2
  have hfin' : xmb_antiN n (fun t => H 0 (Fin.cons t (w + unit i))) x
      - xmb_antiN n (fun t => H 0 (Fin.cons t w)) x
      - (H i.succ (Fin.cons x w) - H i.succ (Fin.cons (-(n : ℤ)) w)) = 0 := by
    rw [hxint]
    simpa only [hg0, hg1] using hfin
  exact sub_eq_zero.mp hfin'

/-! ### The finite-box Poincare lemma -/

theorem xmb_boxPoincare (n : ℕ) : ∀ d : ℕ, ∀ (H : (i : Fin d) → Site d → ZMod 2),
    (∀ i j : Fin d, i ≠ j → ∀ p : Site d, p ∈ cent d n →
      p + unit i ∈ cent d n → p + unit j ∈ cent d n →
      H i p + H j (p + unit i) = H j p + H i (p + unit j)) →
    ∃ F : Site d → ZMod 2, ∀ i p, p ∈ cent d n → p + unit i ∈ cent d n →
      F (p + unit i) = F p + H i p := by
  intro d
  induction d with
  | zero =>
    intro H _hclosed
    exact ⟨fun _ => 0, fun i => Fin.elim0 i⟩
  | succ m ih =>
    intro H hclosed
    set H' : (i : Fin m) → Site m → ZMod 2 := fun i w => H i.succ (Fin.cons (-(n : ℤ)) w)
      with hH'
    have hclosed' : ∀ i j : Fin m, i ≠ j → ∀ w : Site m, w ∈ cent m n →
        w + unit i ∈ cent m n → w + unit j ∈ cent m n →
        H' i w + H' j (w + unit i) = H' j w + H' i (w + unit j) := by
      intro i j hij w hw hwi hwj
      simp only [hH']
      have e0 : Fin.cons (-(n : ℤ)) w + unit i.succ = Fin.cons (-(n : ℤ)) (w + unit i) := by
        rw [xmh3_add_succ_cons (Fin.cons (-(n : ℤ)) w) i]; simp
      have e1 : Fin.cons (-(n : ℤ)) w + unit j.succ = Fin.cons (-(n : ℤ)) (w + unit j) := by
        rw [xmh3_add_succ_cons (Fin.cons (-(n : ℤ)) w) j]; simp
      have hmem : Fin.cons (-(n : ℤ)) w ∈ cent (m + 1) n :=
        xmb_cons_mem_cent (by simp) hw
      have hmem_i : Fin.cons (-(n : ℤ)) w + unit i.succ ∈ cent (m + 1) n := by
        rw [e0]; exact xmb_cons_mem_cent (by simp) hwi
      have hmem_j : Fin.cons (-(n : ℤ)) w + unit j.succ ∈ cent (m + 1) n := by
        rw [e1]; exact xmb_cons_mem_cent (by simp) hwj
      have hij' : (i.succ : Fin (m + 1)) ≠ j.succ := fun h => hij (Fin.succ_inj.mp h)
      have hc := hclosed i.succ j.succ hij' (Fin.cons (-(n : ℤ)) w) hmem hmem_i hmem_j
      rw [e0, e1] at hc
      exact hc
    obtain ⟨P, hP⟩ := ih H' hclosed'
    refine ⟨fun p => xmb_antiN n (fun t => H 0 (Fin.cons t (Fin.tail p))) (p 0)
      + P (Fin.tail p), ?_⟩
    intro i p hp hpi
    have hw : Fin.tail p ∈ cent m n := fun j => hp j.succ
    have hx0 : -(n : ℤ) ≤ p 0 := (abs_le.mp (hp 0)).1
    have hxn0 : p 0 ≤ (n : ℤ) := (abs_le.mp (hp 0)).2
    induction i using Fin.cases with
    | zero =>
      rw [xmh3_add_zero_cons p]
      simp only [Fin.tail_cons, Fin.cons_zero]
      rw [xmb_antiN_succ]
      have hg : H 0 (Fin.cons (p 0) (Fin.tail p)) = H 0 p := by rw [xmh3_self_cons p]
      rw [hg]
      abel
    | succ i =>
      rw [xmh3_add_succ_cons p i] at hpi ⊢
      simp only [Fin.tail_cons, Fin.cons_zero] at hpi ⊢
      have hwi : Fin.tail p + unit i ∈ cent m n := by
        intro j
        exact hpi j.succ
      obtain hdif := xmb_box_difference n m H hclosed (Fin.tail p) hw i hwi hx0 hxn0
      have hdif' : xmb_antiN n (fun t => H 0 (Fin.cons t (Fin.tail p + unit i))) (p 0)
          = xmb_antiN n (fun t => H 0 (Fin.cons t (Fin.tail p))) (p 0)
            + (H i.succ (Fin.cons (p 0) (Fin.tail p))
              - H i.succ (Fin.cons (-(n : ℤ)) (Fin.tail p))) := by
        rw [← hdif]; ring
      rw [hP i (Fin.tail p) hw hwi, hdif']
      have hH'i : H' i (Fin.tail p) = H i.succ (Fin.cons (-(n : ℤ)) (Fin.tail p)) := rfl
      rw [hH'i, show H i.succ (Fin.cons (p 0) (Fin.tail p)) = H i.succ p from by
        rw [xmh3_self_cons p]]
      ring

end Exploding
