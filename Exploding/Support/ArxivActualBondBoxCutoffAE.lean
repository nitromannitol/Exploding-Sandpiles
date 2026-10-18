import Exploding.Support.ArxivBondFiniteHoleBoxCutoff
import Exploding.Support.ArxivActualBondClusterHolesAE

/-!
# Infinite actual bond cluster with a uniform box cutoff

Intersecting the actual-cluster hole theorem with the finite-hole box cutoff gives, almost surely,
an infinite actual open-bond cluster whose finite holes meeting large centred boxes obey the
logarithmic-square bound.
-/

open LatticeProb MeasureTheory Filter

namespace Exploding

/-- At high bond density, almost every configuration has an infinite actual open-bond cluster
with `RnHoleProp` and an eventual logarithmic-square cutoff for every finite hole meeting each
centred box. -/
theorem arxiv_actual_bond_box_cutoff_ae (d : ℕ) (hd : 2 ≤ d) :
    ∃ q0 B : ℝ, 0 ≤ q0 ∧ q0 < 1 ∧ 1 ≤ B ∧
      ∀ q : ℝ, q0 ≤ q → q ≤ 1 →
        ∀ᵐ ζ ∂(bondPercolation d q), ∃ i : Site d,
          let I : Set (Site d) := {y : Site d | (openBondGraph ζ).Reachable i y}
          I.Infinite ∧ RnHoleProp d I ∧
            ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ z : Site d,
              z ∈ cent d (4 * n) → z ∉ I →
                (componentIn Iᶜ z).Finite ∧
                  ((componentIn Iᶜ z).ncard : ℝ) ≤
                    B * (Real.log ((n : ℝ) + 2)) ^ (2 : ℕ) := by
  obtain ⟨qBox, B, hqBox0, hqBox1, hB, hboxCutoff⟩ :=
    arxiv_ae_bond_finite_holes_box_cutoff d hd
  obtain ⟨qHoles, hqHoles0, hqHoles1, hclusterHoles⟩ :=
    arxiv_actual_bond_cluster_holes_ae d hd
  let q0 : ℝ := max qBox qHoles
  have hq0 : 0 ≤ q0 := by
    dsimp [q0]
    exact le_trans hqBox0 (le_max_left _ _)
  have hq01 : q0 < 1 := by
    dsimp [q0]
    exact max_lt hqBox1 hqHoles1
  refine ⟨q0, B, hq0, hq01, hB, ?_⟩
  intro q hq hq1
  have hqBox : qBox ≤ q := (le_max_left _ _).trans hq
  have hqHoles : qHoles ≤ q := (le_max_right _ _).trans hq
  have hboxAE := hboxCutoff q hqBox hq1
  have hclusterAE := hclusterHoles q hqHoles hq1
  filter_upwards [hboxAE, hclusterAE] with ζ hbox hcluster
  rcases hbox with ⟨nBox, hbox⟩
  rcases hcluster with ⟨i, hiInfinite, hiHoles⟩
  rcases hiHoles with ⟨nHoles, hHoles⟩
  let n0 : ℕ := max nBox nHoles
  have hnBox : nBox ≤ n0 := by
    dsimp [n0]
    exact le_max_left _ _
  have hnHoles : nHoles ≤ n0 := by
    dsimp [n0]
    exact le_max_right _ _
  refine ⟨i, hiInfinite, ⟨nHoles, hHoles⟩, n0, ?_⟩
  intro n hn z hz hzi
  have hnBox' : nBox ≤ n := hnBox.trans hn
  have hnHoles' : nHoles ≤ 4 * n := by omega
  have hfinite : (componentIn
      ({y : Site d | (openBondGraph ζ).Reachable i y}ᶜ) z).Finite :=
    (hHoles (4 * n) hnHoles' z hz hzi).1
  have hbound := hbox n hnBox' i z hz hzi hfinite
  exact ⟨hfinite, hbound⟩

end Exploding
