import Exploding.Support.ArxivAllHighWave
import Exploding.Support.SubStep

/-!
# Translation of the all-high one-wave front

This module transports the origin formula to an arbitrary lattice center. It uses
`wave_centre_eq` and the proved origin front, without a new recurrence argument.
-/
namespace Exploding

open LatticeProb

/-- Translating the origin front gives the all-high one-wave indicator ball at any center. -/
theorem allHigh_wave_one_eq_indicator_ball
    (d : ℕ) (hd : 2 ≤ d) (z x : Site d) (t : ℕ) :
    wave (fun _ : Site d => 2 * (d : ℤ) - 1) 1 z t x =
      if mnorm (x - z) ≤ (t : ℤ) then 1 else 0 := by
  rw [wave_centre_eq]
  exact arxivAllHigh_waveFront d hd t (x - z)

end Exploding
