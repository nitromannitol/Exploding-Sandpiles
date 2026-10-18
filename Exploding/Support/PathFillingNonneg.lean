/-
Nonnegativity from the path-filling hypothesis, with no closed producer input.

Let `η ≤ 2d - 1` hold at every site, and let `x` be a site with `η x < 0`. For every
exponent `γ` and threshold `n0`, the detour producer `exists_path_avoiding_site` gives a box
size `n ≥ n0` and an injective nearest-neighbour path `z` of length `m` with `(log n)^γ ≤ m`,
whose range `S` lies in the box, has `x` in its bounding rectangle, and does not contain `x`.
Path-filling (`PathFillingHyp`) at that path, run for time `t = m ^ d`, gives `1 ≤ fodo S η`
at `x`. The negative-site barrier `fodo_eq_zero_of_neg`, applied to the same `S` and seeds,
gives `0` at `x`. This contradiction is the whole argument.

Only `η ≤ 2d - 1` is used, on the full-measure event where it holds. No sign assumption on the
background enters, and no stationarity or recurrence is used.
-/
import Exploding.Support.Hypotheses
import Exploding.Support.PathFillingBarrier
import Exploding.Support.PathFillingDetour

namespace Exploding

open LatticeProb MeasureTheory

/-- If the background is almost surely at most `2d - 1` and the path-filling hypothesis
holds, then the background is almost surely nonnegative. -/
theorem pathFillingHyp_nonneg {d : ℕ} (hd : 2 ≤ d) (P : Measure (Site d → ℤ))
    (hη : ∀ᵐ η ∂P, ∀ x, η x ≤ 2 * (d : ℤ) - 1) (hpath : PathFillingHyp d P) :
    ∀ᵐ η ∂P, ∀ x, 0 ≤ η x := by
  obtain ⟨γ, hγ, hH3⟩ := hpath
  filter_upwards [hη, hH3] with η hηη hH3η
  intro x
  by_contra hneg
  have hneg' : η x < 0 := not_le.mp hneg
  obtain ⟨n0, hn0⟩ := hH3η
  obtain ⟨n, m, z, hn, hlog, hcent, hinj, hadj, hbr, hx⟩ :=
    exists_path_avoiding_site hd x γ hγ n0
  have hfill := hn0 n hn m z hlog hcent hinj hadj (m ^ d) le_rfl x hbr
  have hzero := fodo_eq_zero_of_neg (z '' {i : ℕ | i < m}) η x hηη hx hneg' (m ^ d)
  rw [hzero] at hfill
  norm_num at hfill

end Exploding
