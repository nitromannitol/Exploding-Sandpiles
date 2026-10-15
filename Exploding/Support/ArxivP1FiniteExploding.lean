import Exploding.Support.ArxivAllHighWave
import Exploding.Support.ArxivP1Crossing

/-!
# Finite nonstabilizability at the endpoint

At parameter one, the actual product background law is concentrated on the
all-high configuration. Its first wave is not stabilizable, so the actual law
almost surely has a positive wave index with this property.
-/

namespace Exploding

open MeasureTheory
open LatticeProb

/-- The actual endpoint law almost surely has a positive nonstabilizable wave
at the origin, by its all-high Dirac identity and the deterministic first wave. -/
theorem finite_exploding_p1 (d : ℕ) (hd : 2 ≤ d) :
    ∀ᵐ η ∂(toyLaw d (1 : ℝ)),
      ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d) := by
  rw [toyLaw_one_eq_dirac, MeasureTheory.ae_dirac_eq]
  simp only [Filter.Eventually, Filter.mem_pure]
  exact ⟨1, le_rfl, arxivAllHigh_wave_not_stabilizable d hd⟩

end Exploding
