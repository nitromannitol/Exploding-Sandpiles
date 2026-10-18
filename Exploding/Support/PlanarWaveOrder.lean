import Exploding.Support.SquareLowerBoundExponential

/-!
# Least positive covering order of the planar cube

On the homogeneous height-two background `η ≡ 2` in dimension two, the `m`-wave from the origin
covers the cube `cent 2 n` at some time for every `m` at least `(2 * 2) ^ (2 * n)`, by the
exponential square lower bound. So the set of positive orders whose wave covers the cube is
nonempty, and its least element is the unique least positive covering order. This file proves only this
object and existence statement, with a nonvacuity consumer at `n = 1`. It makes no logarithmic
rate claim.
-/

open Exploding LatticeProb

namespace Exploding

/-- For `n ≥ 1` on the homogeneous height-two background in dimension two, there is a unique least
positive order `M` whose `M`-wave from the origin covers every site of `cent 2 n`, each site at
some time. Leastness is taken among positive covering orders. -/
theorem planar_wave_least_order_exists_unique (n : ℕ) (hn : 1 ≤ n) :
    ∃! M : ℕ,
      1 ≤ M ∧
      (∀ x ∈ cent 2 n, ∃ t : ℕ,
        0 < wave (fun _ : Site 2 => (2 : ℤ)) M (0 : Site 2) t x) ∧
      (∀ m : ℕ, 1 ≤ m →
        (∀ x ∈ cent 2 n, ∃ t : ℕ,
          0 < wave (fun _ : Site 2 => (2 : ℤ)) m (0 : Site 2) t x) → M ≤ m) := by
  classical
  have hex : ∃ m : ℕ, 1 ≤ m ∧
      ∀ x ∈ cent 2 n, ∃ t : ℕ, 0 < wave (fun _ : Site 2 => (2 : ℤ)) m (0 : Site 2) t x := by
    refine ⟨4 ^ (2 * n), Nat.one_le_pow _ _ (by norm_num), ?_⟩
    exact Exploding.square_lower_bound_exponential 2 le_rfl (fun _ : Site 2 => (2 : ℤ))
      (fun _ => by norm_num) n hn (4 ^ (2 * n)) (by norm_num)
  refine ⟨Nat.find hex, ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2,
    fun m hm hcov => Nat.find_min' hex ⟨hm, hcov⟩⟩, ?_⟩
  rintro M ⟨hM1, hM2, hM3⟩
  exact le_antisymm (hM3 _ (Nat.find_spec hex).1 (Nat.find_spec hex).2)
    (Nat.find_min' hex ⟨hM1, hM2⟩)

/-- Nonvacuity at `n = 1`: the least positive covering order of `cent 2 1` exists and is unique,
obtained by applying `planar_wave_least_order_exists_unique` with `1 ≤ 1`. -/
theorem planar_wave_least_order_one :
    ∃! M : ℕ,
      1 ≤ M ∧
      (∀ x ∈ cent 2 1, ∃ t : ℕ,
        0 < wave (fun _ : Site 2 => (2 : ℤ)) M (0 : Site 2) t x) ∧
      (∀ m : ℕ, 1 ≤ m →
        (∀ x ∈ cent 2 1, ∃ t : ℕ,
          0 < wave (fun _ : Site 2 => (2 : ℤ)) m (0 : Site 2) t x) → M ≤ m) :=
  planar_wave_least_order_exists_unique 1 le_rfl

end Exploding
