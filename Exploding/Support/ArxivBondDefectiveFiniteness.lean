import Exploding.Support.ArxivBondDefectiveAnimals
import Exploding.Support.ExtMHProof3

/-!
# Finiteness of bond-defective star-connected sets

The rooted finite-animal estimate and Borel–Cantelli exclude every infinite
star-connected set of defective vertices at sufficiently high bond density.
The argument uses the actual bond configuration and assumes no hole-finiteness
or summability premise.
-/

open LatticeProb MeasureTheory Filter

namespace Exploding

/-- At sufficiently high bond density, almost surely there is no infinite
star-connected set all of whose vertices are defective. -/
theorem arxiv_ae_no_infinite_bond_defective_star_set (d : ℕ) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ {q : ℝ}, 0 ≤ q → q ≤ 1 →
      (K : ENNReal) ^ (3 ^ d) *
        ENNReal.ofReal (2 * (d : ℝ) * (1 - q)) < 1 →
      ∀ᵐ ζ ∂(bondPercolation d q),
        ¬ ∃ S : Set (Site d), S.Infinite ∧ xmh_SConn S ∧
          ∀ z ∈ S, rn_siteField ζ z = false := by
  classical
  obtain ⟨K, hK, hAnimal⟩ := arxiv_bond_defective_star_animal_prob_le d
  refine ⟨K, hK, ?_⟩
  intro q hq0 hq1 hnumeric
  let M : ℕ := 3 ^ d
  let b : ENNReal := ENNReal.ofReal (2 * (d : ℝ) * (1 - q))
  let r : ENNReal := (K : ENNReal) ^ M * b
  have hMpos : 0 < M := by
    dsimp [M]
    positivity
  have hr : r < 1 := by
    simpa only [r, b, M] using hnumeric
  have hsub_ne : 1 - r ≠ 0 := by
    intro hzero
    exact (not_le_of_gt hr) (tsub_eq_zero_iff_le.mp hzero)
  let E : Site d → ℕ → Set (RnBond d → Bool) := fun p n =>
    {ζ | ∃ F : Finset (Site d), p ∈ F ∧ F.card = M * n ∧
      xmh_SConn (F : Set (Site d)) ∧ ∀ x ∈ F, rn_siteField ζ x = false}
  have hbound (p : Site d) (n : ℕ) :
      bondPercolation d q (E p n) ≤ r ^ n := by
    have hdiv : (M * n) / (3 ^ d) = n := by
      dsimp [M]
      exact Nat.mul_div_cancel_left n (pow_pos (by omega) d)
    calc
      bondPercolation d q (E p n) ≤
          (K : ENNReal) ^ (M * n) * b ^ ((M * n) / (3 ^ d)) := by
        simpa only [E] using hAnimal p (M * n) hq0 hq1
      _ = r ^ n := by
        rw [hdiv, pow_mul, ← mul_pow]
  have hsum (p : Site d) :
      (∑' n : ℕ, bondPercolation d q (E p n)) ≠ ⊤ := by
    have hgeom : (∑' n : ℕ, r ^ n) ≠ ⊤ := by
      rw [ENNReal.tsum_geometric]
      exact ENNReal.inv_ne_top.mpr hsub_ne
    refine ne_top_of_le_ne_top hgeom (ENNReal.tsum_le_tsum ?_)
    exact hbound p
  have havoid (p : Site d) :
      ∀ᵐ ζ ∂(bondPercolation d q), ∀ᶠ n : ℕ in atTop, ζ ∉ E p n :=
    xmh2_ae_eventually_notMem (bondPercolation d q) (E p) (hsum p)
  have hall : ∀ᵐ ζ ∂(bondPercolation d q),
      ∀ p : Site d, ∀ᶠ n : ℕ in atTop, ζ ∉ E p n :=
    MeasureTheory.ae_all_iff.mpr havoid
  filter_upwards [hall] with ζ hζ
  rintro ⟨S, hSinf, hSconn, hSdef⟩
  obtain ⟨p, hpS⟩ := hSinf.nonempty
  have hpavoid := hζ p
  rw [Filter.eventually_atTop] at hpavoid
  obtain ⟨N, hN⟩ := hpavoid
  let n := max N 1
  have hNn : N ≤ n := le_max_left N 1
  have hnpos : 1 ≤ n := le_max_right N 1
  have hsize : 1 ≤ M * n := by
    have hprod : 0 < M * n := Nat.mul_pos hMpos (by omega)
    omega
  have hencard : (M * n : ℕ∞) ≤ S.encard := by
    rw [Set.Infinite.encard_eq hSinf]
    exact le_top
  obtain ⟨F, hpF, hFS, hFcard, hFconn⟩ :=
    xmh_grow hSconn hpS (M * n) hsize hencard
  have hmem : ζ ∈ E p n := by
    exact ⟨F, hpF, hFcard, hFconn, fun z hz => hSdef z (hFS hz)⟩
  exact hN n hNn hmem

end Exploding
