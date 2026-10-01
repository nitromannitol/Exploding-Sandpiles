/-
Proposition 5.1 of the paper (generalized last wave): the event that a tile is strongly box-crossing
depends on the background only through the tile.
-/
import Exploding.Support.GLWSec3AE

open MeasureTheory ProbabilityTheory Exploding LatticeProb Filter

namespace Exploding

variable {d : ℕ}

/-- The frozen odometer of a set containing the complement of `T` depends on the background only
through `T`. -/
theorem glws_fodo_congr (S T : Set (Site d)) (hS : Tᶜ ⊆ S) (s0 s0' w0 : Site d → ℤ)
    (heq : ∀ x ∈ T, s0 x = s0' x) (t : ℕ) : fodo S s0 w0 t = fodo S s0' w0 t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext x
    rw [fodo_succ, fodo_succ]
    by_cases hx : x ∈ S
    · simp [hx]
    · have hxT : x ∈ T := by
        by_contra h
        exact hx (hS h)
      simp only [hx, if_false]
      unfold fconf
      rw [ih, heq x hxT]

/-- Being strongly box-crossing depends on the background only through the tile. -/
theorem glws_sbc_congr (k : Fin d → ℕ) (j : Site d) (η η' : Site d → ℤ)
    (heq : ∀ x ∈ rboxShift k j, η x = η' x) :
    StronglyBoxCrossed η k j ↔ StronglyBoxCrossed η' k j := by
  have h : ∀ (i : Fin d) (z : Site d),
      fodo ((rboxShift k j)ᶜ ∪ rline k j i z) η (Set.indicator (rline k j i z) 1) (∏ l, k l) =
      fodo ((rboxShift k j)ᶜ ∪ rline k j i z) η' (Set.indicator (rline k j i z) 1) (∏ l, k l) :=
    fun i z => glws_fodo_congr _ (rboxShift k j) (fun x hx => Or.inl hx) η η' _ heq _
  unfold StronglyBoxCrossed
  simp only [h]

end Exploding
