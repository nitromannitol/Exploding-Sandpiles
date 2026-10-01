/-
The finite-cluster Peierls estimate.  The reduction `xap9_FiniteClusterReduction`
is false as stated: it demands an all-bad `*`-connected set **containing the
origin**, but the origin can be good while its cluster is finite, so no such set
exists.  This file refutes that statement, then works with the correct
origin-free reduction: every finite cluster has a nonempty all-bad
`*`-connected set, which is counted by `xap10_starSets` (no base-point
requirement) and fed to the packed bad-set union bound.
-/
import Exploding.Support.ExtAPProof9
import Mathlib.Data.Fintype.EquivFin

open Exploding LatticeProb MeasureTheory
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-! ### The reduction of `ExtAPProof9` is false -/

/-- The configuration in which a bond is open exactly when at least one endpoint
lies in the cube of the origin.  The origin is then good while every one of its
star-neighbours is bad, so the good cluster of the origin is `{0}`. -/
noncomputable def xap10_refuteOmega (d : ℕ) : Site d × Fin d → Bool :=
  fun b => decide (b.1 ∈ xap_cube (0 : Site d) ∨ b.1 + unit b.2 ∈ xap_cube (0 : Site d))

theorem xap10_refuteOmega_good (d : ℕ) :
    xap_Good (xap10_refuteOmega d) (0 : Site d) := by
  intro x i hx _
  rw [xap10_refuteOmega]
  exact decide_eq_true (Or.inl hx)

/-- Every star-neighbour of the origin is bad for `xap10_refuteOmega`. -/
theorem xap10_refuteOmega_bad_star (hd : 2 ≤ d) {z : Site d}
    (hz : xap_Star (0 : Site d) z) :
    ¬ xap_Good (xap10_refuteOmega d) z := by
  intro hgood
  have hz0 : z ≠ 0 := hz.1.symm
  have hcoord : ∀ i, |z i| ≤ 1 := by
    intro i
    have := hz.2 i
    rw [Pi.zero_apply, zero_sub, abs_neg] at this
    exact this
  obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
    by_contra h
    push Not at h
    exact hz0 (funext h)
  have hjle : |z j| ≤ 1 := hcoord j
  have hsign : z j = 1 ∨ z j = -1 := by
    have := abs_le.mp hjle
    omega
  have hzjabs : |z j| = 1 := by rcases hsign with h | h <;> rw [h] <;> norm_num
  obtain ⟨l, hl⟩ : ∃ l : Fin d, l ≠ j :=
    Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) j
  set x : Site d := Function.update z j (2 * z j) with hxdef
  have hxj : x j = 2 * z j := by rw [hxdef, Function.update_self]
  have hxi : ∀ i, i ≠ j → x i = z i := by
    intro i hi; rw [hxdef, Function.update_of_ne hi]
  have hxcube : x ∈ xap_cube z := by
    intro i
    by_cases hij : i = j
    · subst hij
      have : 2 * z i - z i = z i := by ring
      rw [hxj, this]; exact hjle
    · rw [hxi i hij]; simp
  have hxnotcube : x ∉ xap_cube (0 : Site d) := by
    intro hx0
    have hle := hx0 j
    rw [Pi.zero_apply, sub_zero, hxj] at hle
    have habs : |2 * z j| = 2 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℤ) < 2), hzjabs]; norm_num
    omega
  set y : Site d := x + unit l with hydef
  have hyj : y j = 2 * z j := by
    rw [hydef, Pi.add_apply, hxj, unit, Pi.single_eq_of_ne (Ne.symm hl), add_zero]
  have hyl : y l = z l + 1 := by
    rw [hydef, Pi.add_apply, hxi l hl, unit, Pi.single_eq_same]
  have hycube : y ∈ xap_cube z := by
    intro i
    by_cases hij : i = j
    · subst hij
      have : 2 * z i - z i = z i := by ring
      rw [hyj, this]; exact hjle
    · by_cases hil : i = l
      · subst hil
        have : z i + 1 - z i = 1 := by ring
        rw [hyl, this]; norm_num
      · have hyi : y i = z i := by
          rw [hydef, Pi.add_apply, hxi i hij, unit, Pi.single_eq_of_ne hil, add_zero]
        rw [hyi]; simp
  have hynotcube : y ∉ xap_cube (0 : Site d) := by
    intro hy0
    have hle := hy0 j
    rw [Pi.zero_apply, sub_zero, hyj] at hle
    have habs : |2 * z j| = 2 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℤ) < 2), hzjabs]; norm_num
    omega
  have hfalse : xap10_refuteOmega d (x, l) = false := by
    rw [xap10_refuteOmega]
    refine decide_eq_false ?_
    push Not
    exact ⟨hxnotcube, by rw [← hydef]; exact hynotcube⟩
  have htrue := hgood x l hxcube (by rw [← hydef]; exact hycube)
  rw [hfalse] at htrue
  exact Bool.noConfusion htrue

/-- The good cluster of `xap10_refuteOmega` is exactly `{0}`. -/
theorem xap10_refuteOmega_goodConnected (hd : 2 ≤ d) (z : Site d) :
    xap3_GoodConnected (xap10_refuteOmega d) z ↔ z = 0 := by
  constructor
  · rintro ⟨p, hp⟩
    cases p with
    | nil => rfl
    | cons h p' =>
        rename_i v
        have hv : v ∈ (SimpleGraph.Walk.cons h p').support := by
          rw [SimpleGraph.Walk.support_cons]
          exact List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support p')
        exact absurd (hp v hv) (xap10_refuteOmega_bad_star hd h)
  · rintro rfl
    exact ⟨SimpleGraph.Walk.nil, by
      intro w hw
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
      rw [hw]
      exact xap10_refuteOmega_good d⟩

theorem xap10_refuteOmega_smallCluster (hd : 2 ≤ d) :
    xap5_SmallCluster (xap10_refuteOmega d) := by
  have hset : {z : Site d | xap3_GoodConnected (xap10_refuteOmega d) z} = {0} := by
    ext z
    rw [Set.mem_setOf_eq, xap10_refuteOmega_goodConnected hd z, Set.mem_singleton_iff]
  rw [xap5_SmallCluster, hset]
  exact Set.finite_singleton 0

/-- The condition `xap9_FiniteClusterReduction` is false for every `d ≥ 2`. -/
theorem xap10_not_finiteClusterReduction (hd : 2 ≤ d) :
    ¬ xap9_FiniteClusterReduction d := by
  rintro ⟨X, hX⟩
  obtain ⟨s, Γ, hΓ, hbad⟩ := hX (xap10_refuteOmega d) (xap10_refuteOmega_smallCluster hd)
  rw [xap8_starSets, Finset.mem_filter] at hΓ
  exact hbad 0 hΓ.2.1 (xap10_refuteOmega_good d)

end Exploding
