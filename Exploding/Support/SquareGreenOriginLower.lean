/-
Finite-domain lower origin estimate for the ordinary parallel odometer of the pile
`(2d - 2) + N δ₀`.

For a finite domain `D ∋ 0` containing the support of the odometer at a common terminal time `T`,
where the odometer is constant from `T` on, the origin value obeys
  `N g_D(0,0) - ∑_{y∈D} g_D(0,y) ≤ u_T(0)`,
with `g_D = LatticeProb.Graph.killedGreenReal (lattice d) D` the killed Green function of `ℤ^d`
in the library normalization (expected visits divided by `2d`).

The argument: the terminal configuration is stable, so its heights are at most `2d - 1`
(`glw_wave_to_explosive_pstable`).  Hence on `D` the defect `s₀ - s_T` is at least `N δ₀ - 1`
pointwise.  Multiplying by the nonnegative Green function, summing over `D`, and using the
chip-conservation origin identity `squareOrigin_origin_identity` gives the bound.

The terminal time `T`, the constancy of the odometer from `T` on, and the support of the odometer
on `D` are hypotheses of this estimate.  They are not derived here.
-/
import Exploding.Support.SquareGreenOrigin
import Exploding.Support.GLWProofAux
import LatticeProb.Graph.Zd
import LatticeProb.Network.KilledGreen

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- **Lower origin bound.**  Let `d ≥ 2`, let `N, T : ℕ`, and let `D ∋ 0` be finite.  Suppose the
ordinary odometer of the pile `(2d - 2) + N δ₀` is constant from time `T` on and vanishes off `D`
at time `T`.  Then the origin value satisfies
`N g_D(0,0) - ∑_{y∈D} g_D(0,y) ≤ u_T(0)`, with `g_D` the killed Green function of `lattice d`. -/
theorem squareOrigin_odometer_ge_green (hd : 2 ≤ d) (N T : ℕ)
    (D : Finset (Site d)) (hO : (0 : Site d) ∈ D)
    (hT : ∀ t : ℕ, T ≤ t → podo (squareOrigin_pile (d := d) (2 * (d : ℤ) - 2) N) t
      = podo (squareOrigin_pile (d := d) (2 * (d : ℤ) - 2) N) T)
    (hsupp : ∀ x, x ∉ D → podo (squareOrigin_pile (d := d) (2 * (d : ℤ) - 2) N) T x = 0) :
    (N : ℝ) * LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 0
      - ∑ y ∈ D, LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 y
      ≤ ((podo (squareOrigin_pile (d := d) (2 * (d : ℤ) - 2) N) T 0 : ℤ) : ℝ) := by
  have hd0 : 0 < d := by omega
  haveI : NeZero d := ⟨hd0.ne'⟩
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset D
  have hG : (lattice d).Connected := LatticeProb.Graph.Zd.latticeConnected d
  have hid := squareOrigin_origin_identity hd0 D hO (squareOrigin_pile (d := d) (2 * (d : ℤ) - 2) N) T hsupp
  have hgnn : ∀ v, 0 ≤ LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 v :=
    fun v => LatticeProb.Network.killedGreenReal_nonneg hG D hq 0 v
  -- stability of the terminal configuration: `pconf ≤ 2d - 1`, cast to `ℝ`
  have hstab : ∀ x, ((pconf (squareOrigin_pile (d := d) (2 * (d : ℤ) - 2) N) T x : ℤ) : ℝ)
      ≤ 2 * (d : ℝ) - 1 := by
    intro x
    have h1 : pconf (squareOrigin_pile (d := d) (2 * (d : ℤ) - 2) N) T x ≤ 2 * (d : ℤ) - 1 :=
      glw_wave_to_explosive_pstable (squareOrigin_pile (d := d) (2 * (d : ℤ) - 2) N) T hT x
    exact_mod_cast h1
  -- pointwise: `N δ₀(v) g(v) - g(v) ≤ g(v) (s₀(v) - s_T(v))`
  have hpt : ∀ v ∈ D,
      (N : ℝ) * (if v = 0 then LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 v
        else 0) - LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 v
      ≤ LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 v
        * (((squareOrigin_pile (d := d) (2 * (d : ℤ) - 2) N v : ℤ) : ℝ)
          - ((pconf (squareOrigin_pile (d := d) (2 * (d : ℤ) - 2) N) T v : ℤ) : ℝ)) := by
    intro v _
    have hgv := hgnn v
    have hs := hstab v
    rw [squareOrigin_pile_real (2 * (d : ℤ) - 2) N v]
    push_cast
    split_ifs <;> nlinarith [mul_nonneg hgv (sub_nonneg.mpr hs)]
  have hsum := Finset.sum_le_sum hpt
  have hR : ∑ v ∈ D, ((N : ℝ) * (if v = 0 then LatticeProb.Graph.killedGreenReal (lattice d)
        (D : Set (Site d)) 0 v else 0) - LatticeProb.Graph.killedGreenReal (lattice d)
        (D : Set (Site d)) 0 v)
      = (N : ℝ) * LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 0
        - ∑ y ∈ D, LatticeProb.Graph.killedGreenReal (lattice d) (D : Set (Site d)) 0 y := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', if_pos hO]
  linarith [hid, hR, hsum]

end Exploding
