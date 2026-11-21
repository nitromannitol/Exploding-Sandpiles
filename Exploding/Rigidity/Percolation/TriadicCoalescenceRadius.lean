/-
Copied from Percolation-Rigidity (https://github.com/nitromannitol/Percolation-Rigidity), commit
d5b6dd0b0019636ea3c88ad0f7da087a6ac194c3, file `Rigidity/Percolation/TriadicCoalescenceRadius.lean`,
licensed under the Apache License 2.0.
Changes: the module paths of the imports (`Rigidity.*` becomes `Exploding.Rigidity.*`); the
namespace `LatticeProb.Percolation` of the Lattice-Probability bond model becomes
`Exploding.LatticeBond`.
-/
import Exploding.Rigidity.Percolation.TriadicCoalescenceScales
import Exploding.Rigidity.Percolation.CrossingRadiusAdapter

/-!
# Coalescence from radius estimates

Crossing-component estimates stated using ℓ¹ path radii at two compatible
scales give a coalescence bound for triadic test cubes.
-/

namespace Rigidity.Percolation

open Exploding.LatticeBond Rigidity.External MeasureTheory
open scoped ENNReal

/-- Radius-based crossing estimates at scales `8t` and `4t` control the
coalescence failure probability in every sufficiently large test cube. -/
theorem TriadicCube.measure_testCube_not_coalesces_le_of_radius {d : ℕ}
    (hd : 0 < d) (Q : TriadicCube d) {interior : Set (Vertex d)}
    (T : IntegerCube d) (hT : T ∈ Q.testCubes interior) (hsize : 61 ≤ T.size)
    (μ : Measure (Configuration d)) (a b : ℕ → ℝ≥0∞)
    (ha : ∀ t : ℕ, 3 ≤ t → ∀ U : IntegerCube d, U.size = 20 * t + 1 →
      (↑U.vertices : Set (Vertex d)) ⊆ T.vertices →
      μ {ω | ¬ HasCrossingComponentConnectingPaths ω (↑U.vertices)
        (fun i => ↑(U.lowerFace i)) (fun i => ↑(U.upperFace i))
        (fun n γ => ∀ z : Vertex d, ∃ i : Fin (n + 1),
          8 * (t : ℤ) < 10 * ∑ k, |γ i k - z k|)} ≤ a t)
    (hb : ∀ t : ℕ, 3 ≤ t → ∀ U : IntegerCube d, U.size = 10 * t + 1 →
      (↑U.vertices : Set (Vertex d)) ⊆ T.vertices →
      μ {ω | ¬ HasCrossingComponentConnectingPaths ω (↑U.vertices)
        (fun i => ↑(U.lowerFace i)) (fun i => ↑(U.upperFace i))
        (fun n γ => ∀ z : Vertex d, ∃ i : Fin (n + 1),
          4 * (t : ℤ) < 10 * ∑ k, |γ i k - z k|)} ≤ b t) :
    ∃ t : ℕ, 3 ≤ t ∧ T.size ≤ 20 * t + 20 ∧
      μ {ω | ¬ LargePathsCoalesce ω (↑T.vertices) Q.largePath} ≤
        (T.size ^ d : ℕ) * (a t + b t) := by
  apply Q.measure_testCube_not_coalesces_le hd T hT hsize μ a b
  · intro t ht U hUs hUT
    calc
      _ ≤ μ {ω | ¬ HasCrossingComponentConnectingPaths ω (↑U.vertices)
          (fun i => ↑(U.lowerFace i)) (fun i => ↑(U.upperFace i))
          (fun n γ => ∀ z : Vertex d, ∃ i : Fin (n + 1),
            8 * (t : ℤ) < 10 * ∑ k, |γ i k - z k|)} := by
        apply measure_mono
        intro ω hbad hgood
        exact hbad (hgood.of_l1_radius t (by omega))
      _ ≤ a t := ha t ht U hUs hUT
  · intro t ht U hUs hUT
    calc
      _ ≤ μ {ω | ¬ HasCrossingComponentConnectingPaths ω (↑U.vertices)
          (fun i => ↑(U.lowerFace i)) (fun i => ↑(U.upperFace i))
          (fun n γ => ∀ z : Vertex d, ∃ i : Fin (n + 1),
            4 * (t : ℤ) < 10 * ∑ k, |γ i k - z k|)} := by
        apply measure_mono
        intro ω hbad hgood
        apply hbad
        apply HasCrossingComponentConnectingPaths.of_l1_radius_le t (4 * t) (by omega)
          (by omega)
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hgood
      _ ≤ b t := hb t ht U hUs hUT

end Rigidity.Percolation
