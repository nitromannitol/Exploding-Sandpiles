import Exploding.Support.SquareGreenOrigin
import Exploding.Support.GLWProofAux

/-!
# Covering wave order against the parallel origin, planar case

A comparison helper for the planar (`d = 2`) ordinary parallel odometer of the pile
`2 + N δ₀`.  If every site of the box `cent 2 n` is eventually reached by a positive `m`-wave
on the constant background `2`, and the odometer at the terminal time `T` vanishes somewhere in
that box, then the origin value at time `T` is strictly below `m`.

The proof reuses `glw_wave_to_explosive_pnonneg`, `glw_wave_to_explosive_pstable` and
`glw_wave_to_explosive_dom`: the terminal odometer `v` is nonnegative and stable, its
off-origin stability is the `d = 2` domination premise, and a dominated `m`-wave cannot be
positive at a site where `v` vanishes.
-/

namespace Exploding

open LatticeProb

/-- **Covering order exceeds the parallel origin.**  Let `v = podo (squareOrigin_pile 2 N) T`
be the terminal odometer of the planar pile `2 + N δ₀`.  If `v` is stationary from time `T`
on, every `x ∈ cent 2 n` is reached by a positive `m`-wave on the background `2` at some time,
and `v x = 0` for some `x ∈ cent 2 n`, then `v 0 < m`. -/
theorem planar_wave_covering_order_gt_parallel_origin (N T n m : ℕ)
    (hT : ∀ t : ℕ, T ≤ t →
      podo (squareOrigin_pile (d := 2) 2 N) t =
        podo (squareOrigin_pile (d := 2) 2 N) T)
    (hcover : ∀ x ∈ cent 2 n, ∃ t : ℕ,
      0 < wave (fun _ : Site 2 => (2 : ℤ)) m (0 : Site 2) t x)
    (hzero : ∃ x : Site 2, x ∈ cent 2 n ∧
      podo (squareOrigin_pile (d := 2) 2 N) T x = 0) :
    podo (squareOrigin_pile (d := 2) 2 N) T (0 : Site 2) < (m : ℤ) := by
  by_contra hcon
  have hmv := not_lt.mp hcon
  have hv0nn : ∀ x : Site 2, 0 ≤ podo (squareOrigin_pile (d := 2) 2 N) T x :=
    fun x => glw_wave_to_explosive_pnonneg _ T x
  have hstable : ∀ x : Site 2, x ≠ (0 : Site 2) →
      (fun _ : Site 2 => (2 : ℤ)) x + lap (podo (squareOrigin_pile (d := 2) 2 N) T) x
        ≤ 2 * ((2 : ℕ) : ℤ) - 1 := by
    intro x hx
    have hp := glw_wave_to_explosive_pstable (squareOrigin_pile (d := 2) 2 N) T hT x
    have hdir : squareOrigin_pile (d := 2) 2 N x = 2 := by
      simp [squareOrigin_pile, dirac, hx]
    rw [hdir] at hp
    exact hp
  have hdom := glw_wave_to_explosive_dom (fun _ : Site 2 => (2 : ℤ)) m
    (podo (squareOrigin_pile (d := 2) 2 N) T) hv0nn hmv hstable
  obtain ⟨x, hxc, hx0⟩ := hzero
  obtain ⟨t, ht⟩ := hcover x hxc
  have hle := hdom t x
  rw [hx0] at hle
  exact lt_irrefl _ (lt_of_lt_of_le ht hle)

end Exploding
