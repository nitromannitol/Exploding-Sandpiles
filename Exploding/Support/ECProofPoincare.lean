/-
Planar topology for the percolation step of Proposition 7.1: a mod-two cocycle on the
square lattice `ℤ × ℤ` that vanishes on every unit square is a coboundary, and the
outer boundary of a connected set is `*`-connected.
-/
import Mathlib

namespace Exploding

open Relation

/-! ### Reflexive-transitive closure of a symmetric relation -/

theorem ec_rtg_symm {α : Type*} {R : α → α → Prop} (h : ∀ a b, R a b → R b a) {a b : α}
    (hab : ReflTransGen R a b) : ReflTransGen R b a := by
  induction hab with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih => exact ReflTransGen.head (h _ _ hbc) ih

/-! ### Cumulative sums over `ℤ` in characteristic two -/

theorem ec_zmod2_add_self (a : ZMod 2) : a + a = 0 := CharTwo.add_self_eq_zero a

/-- Antiderivative of `g : ℤ → ZMod 2`. -/
theorem ec_cum_exists (g : ℤ → ZMod 2) :
    ∃ S : ℤ → ZMod 2, S 0 = 0 ∧ ∀ x, S (x + 1) = S x + g x := by
  refine ⟨fun x => if 0 ≤ x then ∑ i ∈ Finset.range x.toNat, g (i : ℤ)
      else ∑ i ∈ Finset.range (-x).toNat, g (-1 - (i : ℤ)), by simp, ?_⟩
  intro x
  by_cases hx : 0 ≤ x
  · have h1 : 0 ≤ x + 1 := by omega
    have h2 : (x + 1).toNat = x.toNat + 1 := by omega
    simp only [if_pos hx, if_pos h1, h2, Finset.sum_range_succ]
    congr 2
    omega
  · have h1 : ¬ 0 ≤ x := hx
    by_cases hx1 : x = -1
    · subst hx1
      simp only [show (0 : ℤ) ≤ -1 + 1 by norm_num, if_true, show ¬ (0 : ℤ) ≤ -1 by norm_num,
        if_false]
      norm_num
      exact (ec_zmod2_add_self _).symm
    · have h2 : ¬ 0 ≤ x + 1 := by omega
      have h3 : (-x).toNat = (-(x + 1)).toNat + 1 := by omega
      simp only [if_neg h1, if_neg h2, h3, Finset.sum_range_succ]
      have h4 : (-1 - (((-(x + 1)).toNat : ℕ) : ℤ)) = x := by omega
      rw [h4]
      set a := ∑ i ∈ Finset.range (-(x + 1)).toNat, g (-1 - (i : ℤ))
      have := ec_zmod2_add_self (g x)
      calc a = a + (g x + g x) := by rw [this, add_zero]
        _ = a + g x + g x := by ring


theorem ec_z2_step : ∀ a b c d e f g h : ZMod 2, g + c = f + h →
    ((a + b = d + e + g) ↔ (a + (b + c) = d + (e + f) + h)) := by decide

/-- **Poincaré lemma on the square lattice modulo two.**  A pair of edge functions
`H` (horizontal) and `V` (vertical) that sums to zero around every unit square is
the coboundary of a function `f`. -/
theorem ec_poincare (H V : ℤ × ℤ → ZMod 2)
    (hsq : ∀ p : ℤ × ℤ, H p + V (p + (1, 0)) = V p + H (p + (0, 1))) :
    ∃ f : ℤ × ℤ → ZMod 2, ∀ p, f (p + (1, 0)) = f p + H p ∧ f (p + (0, 1)) = f p + V p := by
  obtain ⟨S1, hS10, hS1⟩ := ec_cum_exists (fun x => H (x, 0))
  have h2 : ∀ x : ℤ, ∃ S : ℤ → ZMod 2, S 0 = 0 ∧ ∀ y, S (y + 1) = S y + V (x, y) :=
    fun x => ec_cum_exists (fun y => V (x, y))
  choose S2 hS20 hS2 using h2
  refine ⟨fun p => S1 p.1 + S2 p.1 p.2, ?_⟩
  intro p
  obtain ⟨x, y⟩ := p
  refine ⟨?_, ?_⟩
  · have key : ∀ y : ℤ, S1 (x + 1) + S2 (x + 1) y = S1 x + S2 x y + H (x, y) := by
      intro y
      have step : ∀ y : ℤ, (S1 (x + 1) + S2 (x + 1) y = S1 x + S2 x y + H (x, y)) ↔
          (S1 (x + 1) + S2 (x + 1) (y + 1) = S1 x + S2 x (y + 1) + H (x, y + 1)) := by
        intro y
        rw [hS2 (x + 1) y, hS2 x y]
        have hs := hsq (x, y)
        simp only [Prod.mk_add_mk, add_zero] at hs
        exact ec_z2_step _ _ _ _ _ _ _ _ hs
      induction y using Int.induction_on with
      | zero => rw [hS20, hS20, hS1 x]; simp
      | succ n ih => exact (step n).1 ih
      | pred n ih =>
        have := (step (-(n : ℤ) - 1)).2
        have e : (-(n : ℤ) - 1 + 1) = -(n : ℤ) := by ring
        rw [e] at this
        exact this ih
    simp only [Prod.mk_add_mk, add_zero]
    exact key y
  · simp only [Prod.mk_add_mk, add_zero]
    rw [hS2 x y]; ring

end Exploding
