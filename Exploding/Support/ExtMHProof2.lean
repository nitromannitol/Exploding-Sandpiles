/-
The Peierls estimate on `*`-connected closed sets, combining the exponential count of
`*`-connected sets with the finite-cluster expansion, and its assembly into the hole-volume
bound for the infinite cluster of site percolation.
-/
import Exploding.Support.ExtMHProof
import Exploding.Support.ExtMHCount

namespace Exploding

open LatticeProb MeasureTheory Filter

variable {d : ℕ}

/-- **Peierls estimate for `*`-connected closed sets.**  For every site `p` and size `m`, the
probability that some `*`-connected set of `m` closed sites contains `p` is at most `K ^ m`
times `(1 - q) ^ m`, where `K` is the constant of `xmh_StarCount`. -/
theorem xmh2_starconn_closed_prob (hSC : xmh_StarCount d) {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (p : Site d) (m : ℕ) :
    sitePercolation d q {ω : Site d → Bool |
        ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧ xmh_SConn (F : Set (Site d)) ∧
          ∀ x ∈ F, ω x = false}
      ≤ (Classical.choose hSC) ^ m * ENNReal.ofReal (1 - q) ^ m := by
  classical
  have hK := Classical.choose_spec hSC
  obtain ⟨T, hTcard, hTmem⟩ := hK p m
  set T' : Finset (Finset (Site d)) := T.filter (fun F => F.card = m) with hT'
  have hsub : {ω : Site d → Bool |
        ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧ xmh_SConn (F : Set (Site d)) ∧
          ∀ x ∈ F, ω x = false}
      ⊆ {ω : Site d → Bool | ∃ F ∈ T', ∀ x ∈ F, ω x = false} := by
    rintro ω ⟨F, hp, hcard, hconn, hcl⟩
    exact ⟨F, Finset.mem_filter.mpr ⟨hTmem F hp hcard hconn, hcard⟩, hcl⟩
  have hbound : sitePercolation d q
        {ω : Site d → Bool | ∃ F : Finset (Site d), p ∈ F ∧ F.card = m ∧
          xmh_SConn (F : Set (Site d)) ∧ ∀ x ∈ F, ω x = false}
      ≤ (T'.card : ENNReal) * ENNReal.ofReal (1 - q) ^ m :=
    le_trans (measure_mono hsub)
      (xmh_peierls_union h0 h1 T' m fun F hF => (Finset.mem_filter.mp hF).2)
  refine le_trans hbound ?_
  gcongr
  exact_mod_cast le_trans (Finset.card_filter_le _ _) hTcard

end Exploding
