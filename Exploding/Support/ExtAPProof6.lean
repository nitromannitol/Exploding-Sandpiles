/-
The packed bad-set probability of the high-density Peierls estimate: the
probability that a `*`-connected set of `s` bad cubes occurs is at most
`(1 - q^N)^{s / 3^d}`, because a `3`-spaced subpacking of it is independent and
covers a `3^{-d}` fraction of the set.
-/
import Exploding.Support.ExtAPProof5

open Exploding LatticeProb MeasureTheory
open scoped Classical

namespace Exploding

variable {d : ℕ}

/-- The good density `δ = q^N`, `N` being the number of bonds of a cube. -/
noncomputable def xap6_delta (d : ℕ) (q : ℝ) : ENNReal :=
  ENNReal.ofReal q ^ (xap_cubeBonds (0 : Site d)).card

/-- The probability that every cube of a finite set is bad is at most
`(1 - δ)^{s / 3^d}`, where `s` is the number of cubes. -/
theorem xap6_badSet_prob_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (Γ : Finset (Site d)) :
    bondPercolation d q {ω | ∀ z ∈ Γ, ¬ xap_Good ω z} ≤
      (1 - xap6_delta d q) ^ (Γ.card / 3 ^ d) := by
  obtain ⟨Γ', hsub, hfar, hcard⟩ := xap3_exists_packing Γ
  have hmono : {ω : Site d × Fin d → Bool | ∀ z ∈ Γ, ¬ xap_Good ω z}
      ⊆ {ω | ∀ z ∈ Γ', ¬ xap_Good ω z} := by
    intro ω hω z hz
    exact hω z (hsub hz)
  have hbase : 1 - xap6_delta d q ≤ 1 := tsub_le_self
  have hexp : Γ.card / 3 ^ d ≤ Γ'.card := by
    exact Nat.div_le_of_le_mul hcard
  calc bondPercolation d q {ω | ∀ z ∈ Γ, ¬ xap_Good ω z}
      ≤ bondPercolation d q {ω | ∀ z ∈ Γ', ¬ xap_Good ω z} := measure_mono hmono
    _ = (1 - xap6_delta d q) ^ Γ'.card := by
        rw [xap6_delta]
        exact xap4_packing_bad_prob h0 h1 Γ' hfar
    _ ≤ (1 - xap6_delta d q) ^ (Γ.card / 3 ^ d) :=
        pow_le_pow_of_le_one (show (0 : ENNReal) ≤ 1 - xap6_delta d q by simp) hbase hexp

end Exploding
