/-
The finite-cluster case of the Peierls estimate.  If the good cluster of the
origin is finite, its exterior `*`-boundary is a nonempty `*`-connected all-bad
set, so the finite-cluster event is contained in the union, over `s`, of the
events that some member of `xap8_starSets (X s) s` is all bad.  With the union
bound `xap8_starSets_bad_prob_le` this bounds the finite-cluster case by the
geometric series `∑_s (3^d)^{2s} (1 - δ)^{s/3^d}`.

The geometric fact that a finite cluster has such a `*`-connected boundary is
isolated as the hypothesis `xap9_FiniteClusterReduction`; everything after it is
proved.
-/
import Exploding.Support.ExtAPProof8

open Exploding LatticeProb MeasureTheory
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-- The geometric input from Antal–Pisztora's Proposition 2.1 that is not proved
here: a finite good cluster of the origin has an all-bad `*`-connected set of
sites lying in a bounded region `X s` and having `s` sites. -/
def xap9_FiniteClusterReduction (d : ℕ) : Prop :=
  ∃ X : ℕ → Finset (Site d),
    ∀ ω : Site d × Fin d → Bool, xap5_SmallCluster ω →
      ∃ s : ℕ, ∃ Γ ∈ xap8_starSets (X s) s, ∀ z ∈ Γ, ¬ xap_Good ω z

/-- Conditional on `xap9_FiniteClusterReduction`, the finite-cluster case is at
most the geometric series `∑_s (3^d)^{2s} (1 - δ)^{s/3^d}`, which converges as
soon as `3^{2d} (1 - δ)^{1/3^d} < 1`. -/
theorem xap9_smallCluster_prob_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (hred : xap9_FiniteClusterReduction d) :
    bondPercolation d q {ω | xap5_SmallCluster ω} ≤
      ∑' s : ℕ, ((3 ^ d) ^ (2 * s) : ENNReal) * (1 - xap6_delta d q) ^ (s / 3 ^ d) := by
  obtain ⟨X, hX⟩ := hred
  have hsub : {ω : Site d × Fin d → Bool | xap5_SmallCluster ω} ⊆
      ⋃ s : ℕ, {ω | ∃ Γ ∈ xap8_starSets (X s) s, ∀ z ∈ Γ, ¬ xap_Good ω z} := by
    intro ω hω
    obtain ⟨s, Γ, hΓ, hbad⟩ := hX ω hω
    exact Set.mem_iUnion.2 ⟨s, Γ, hΓ, hbad⟩
  calc bondPercolation d q {ω | xap5_SmallCluster ω}
      ≤ bondPercolation d q
          (⋃ s : ℕ, {ω | ∃ Γ ∈ xap8_starSets (X s) s, ∀ z ∈ Γ, ¬ xap_Good ω z}) :=
        measure_mono hsub
    _ ≤ ∑' s : ℕ,
          bondPercolation d q {ω | ∃ Γ ∈ xap8_starSets (X s) s, ∀ z ∈ Γ, ¬ xap_Good ω z} :=
        measure_iUnion_le _
    _ ≤ ∑' s : ℕ, ((3 ^ d) ^ (2 * s) : ENNReal) * (1 - xap6_delta d q) ^ (s / 3 ^ d) :=
        ENNReal.tsum_le_tsum fun s => xap8_starSets_bad_prob_le h0 h1 (X s) s

end Exploding
