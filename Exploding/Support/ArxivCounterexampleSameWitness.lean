import Exploding.Support.CEProof
import Exploding.Support.CELow4
import Exploding.Support.CESlow4
import Exploding.Support.ArxivVolumeConclusion

/-!
# The counterexample on one explicit background

The periodic background `ceEta d` satisfies the explosive, arrival-time, and
volume conclusions together. The volume support is identified pointwise with
the support of its actual exploding pile, so every conclusion concerns the same
background and odometer.
-/

namespace Exploding

open LatticeProb Filter MeasureTheory
open scoped Topology

/-- The positive support of the actual exploding pile of `ceEta d` is the
threshold-three support used by the volume obstruction. -/
theorem ce_exploding_support_eq_volume_at_time (d t : ℕ) (hd : 2 ≤ d) :
    {y : Fin d → ℝ | 0 < podo (explodingPile (ceEta d)) t
      (nearestSite ((t : ℝ) • y))} = ceVolumeAtTime d t := by
  rw [aux_ce_explodingPile_eq d hd]
  rfl

/-- All counterexample conclusions hold simultaneously on the explicit
background `ceEta d`. Its volume support is the support of `explodingPile`. -/
theorem ce_arxiv_counterexample_same_witness (d : ℕ) (hd : 2 ≤ d) :
    Explosive (ceEta d) ∧
    (¬ ∀ x : Site d, 2 * (d : ℤ) - 2 ≤ ceEta d x) ∧
    (∀ n : ℕ, arrival (ceEta d) ((n : ℤ) • e1 d) ≠ ⊤) ∧
    3 / 2 ≤ limsup
      (fun n : ℕ => ((arrival (ceEta d) ((n : ℤ) • e1 d)).toNat : ℝ) / (n : ℝ)) atTop ∧
    liminf
      (fun n : ℕ => ((arrival (ceEta d) ((n : ℤ) • e1 d)).toNat : ℝ) / (n : ℝ)) atTop = 1 ∧
    ¬ ∃ B : Set (Fin d → ℝ), MeasurableSet B ∧
      Tendsto (fun t : ℕ => volume (symmDiff
        {y : Fin d → ℝ | 0 < podo (explodingPile (ceEta d)) t
          (nearestSite ((t : ℝ) • y))} B)) atTop (𝓝 0) := by
  have hFin := ce_arrival_finite_of_low d hd (cel_low d hd)
  have hSlow := ce_slow d hd cels_slow2D hFin
  exact ⟨ce_explosive d hd, ce_not_ge d hd, hFin,
    ce_limsup d hd hSlow (cel_bdd d hd), ce_liminf d hd hFin,
    by
      simpa only [ce_exploding_support_eq_volume_at_time d _ hd] using
        ce_volume_no_global_limit d hd⟩

end Exploding
