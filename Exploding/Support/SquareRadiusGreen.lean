import Exploding.Support.LatticeSandpileBridge
import Exploding.Support.SquareGreenOrigin
import LatticeProb.Sandpile.RadiusConsequences
import LatticeProb.Walk.KilledGreenDiagonal

/-!
# Radius and Green origin bound for the square pile

The parallel toppling process started from the background `2d - 2` with `N` extra chips at the
origin. Its global stabilization time is common to the whole process, the positive terminal
support is the integer cube of the cited lower radius, and the odometer at the origin is bounded
by the killed Green function on the finite domain of the cited outer radius.

The only substantive hypotheses are the dimension `d ≥ 2` and the two cited propositions
`LatticeProb.External.FeyDenBoerRedigCubicalCluster` and `LatticeProb.External.FeyLevinePeresRadius`.
The constants `A`, `N0`, `B` and `E` are chosen before `N`. The scalar arithmetic that converts the
bound into a power of `N` is not part of this file.
-/

namespace Exploding

open LatticeProb

/-- **Radius and Green origin bound.** Assume `d ≥ 2` and the two cited propositions. There are
constants `A > 0`, `N0 ≥ 2`, `B > 0` and `E > 0`, chosen before `N`, such that for every `N ≥ N0`
the parallel process of the pile `(2d - 2) + N δ₀` has a common stabilization time `T` after which
its positive support is the integer cube of radius `r`, with `((N + 2d - 2)^(1/d) - 3) / 2 ≤ r`,
and its origin value is at most `N B (log (L + 2) if d = 2, else 1) + (2d - 2) E (L + 1)^2`, where
`L = ⌈A N^(1/d)⌉`. -/
theorem squareRadiusGreen_terminal_bound (d : ℕ) (hd : 2 ≤ d)
    (hFdBR : LatticeProb.External.FeyDenBoerRedigCubicalCluster)
    (hFLP : LatticeProb.External.FeyLevinePeresRadius) :
    ∃ A : ℝ, 0 < A ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
    ∃ B : ℝ, 0 < B ∧ ∃ E : ℝ, 0 < E ∧
    ∀ N : ℕ, N0 ≤ N →
      let s0 : Site d → ℤ := fun x =>
        (2 * (d : ℤ) - 2) + (N : ℤ) * LatticeProb.Sandpile.dirac (0 : Site d) x
      let L : ℕ := Nat.ceil (A * (N : ℝ) ^ (1 / (d : ℝ)))
      ∃ T : ℕ, ∃ r : ℕ,
        (∀ t : ℕ, T ≤ t → Exploding.podo s0 t = Exploding.podo s0 T) ∧
        {x : Site d | 0 < Exploding.podo s0 T x} =
          {x : Site d | ∀ i : Fin d, |x i| ≤ (r : ℤ)} ∧
        (((N : ℝ) + 2 * (d : ℝ) - 2) ^ (1 / (d : ℝ)) - 3) / 2 ≤ (r : ℝ) ∧
        ((Exploding.podo s0 T 0 : ℤ) : ℝ) ≤
          (N : ℝ) * B * (if d = 2 then Real.log ((L : ℝ) + 2) else 1) +
            (2 * (d : ℝ) - 2) * E * ((L : ℝ) + 1) ^ 2 := by
  obtain ⟨A, hA, N0, hN0, hFLPspec⟩ := LatticeProb.Sandpile.flp_specialization hFLP d hd
  -- The diagonal constant `B` and the row-sum constant `E` are chosen before `N`.
  have hdiag : ∃ B : ℝ, 0 < B ∧ ∀ (L : ℕ) (D : Finset (Site d)),
      (∀ z ∈ D, z ∈ LatticeProb.box d L) →
      LatticeProb.Graph.killedGreenReal (LatticeProb.lattice d) (D : Set (Site d)) 0 0 ≤
        B * (if d = 2 then Real.log ((L : ℝ) + 2) else 1) := by
    by_cases h2 : d = 2
    · subst h2
      obtain ⟨C, hC, h⟩ := LatticeProb.GreenTwoSided.killedGreen_diag_two_le_log
      exact ⟨C, hC, fun L D hD => by simpa using h L D hD⟩
    · obtain ⟨C, hC, h⟩ :=
        LatticeProb.GreenTwoSided.killedGreen_diag_le_const_of_three_le (show 3 ≤ d by omega)
      exact ⟨C, hC, fun L D _ => by rw [if_neg h2, mul_one]; exact h D⟩
  obtain ⟨B, hB, hdiagB⟩ := hdiag
  obtain ⟨E, hE, hrow⟩ := LatticeProb.GreenTwoSided.killedGreen_row_sum_le_sq hd
  refine ⟨A, hA, N0, hN0, B, hB, E, hE, fun N hN => ?_⟩
  intro s0 L
  have hN2 : 2 ≤ N := le_trans hN0 hN
  have hs0 : ∀ x : Site d, s0 x =
      (2 * (d : ℤ) - 2) + (N : ℤ) * LatticeProb.Sandpile.dirac (0 : Site d) x :=
    fun x => rfl
  obtain ⟨hstab, r, hcube, hlow⟩ :=
    LatticeProb.Sandpile.fdbr_parallel_terminal hFdBR d hd N hN2 s0 hs0
  obtain ⟨K, hK⟩ := hstab
  have hKt : ∀ t : ℕ, K ≤ t → Exploding.podo s0 t = Exploding.podo s0 K := by
    intro t ht
    simp only [Exploding.podo_eq_sandpile]
    exact hK t ht
  have hcubeK : {x : Site d | 0 < Exploding.podo s0 K x} =
      {x : Site d | ∀ i : Fin d, |x i| ≤ (r : ℤ)} := by
    rw [Exploding.pos_podo_set_eq_sandpile]
    exact hcube K hK
  -- The finite domain: the cube of radius `L = ⌈A N^(1/d)⌉`.
  set D : Finset (Site d) := Finset.Icc (fun _ => -(L : ℤ)) (fun _ => (L : ℤ)) with hD
  have hDbox : ∀ z ∈ D, z ∈ LatticeProb.box d L := by
    intro z hz
    rw [hD, Finset.mem_Icc] at hz
    simp only [LatticeProb.box, Set.mem_setOf_eq]
    exact fun i => abs_le.mpr ⟨hz.1 i, hz.2 i⟩
  have hO : (0 : Site d) ∈ D := by
    rw [hD, Finset.mem_Icc]
    exact ⟨fun i => by simp, fun i => by simp⟩
  -- Outside `D` the odometer at time `K` vanishes: the Fey-Levine-Peres bound and nonnegativity.
  have hsupp : ∀ x : Site d, x ∉ D →
      Exploding.podo (Exploding.squareOrigin_pile (d := d) (2 * (d : ℤ) - 2) N) K x = 0 := by
    intro x hx
    have hnn : 0 ≤ Exploding.podo s0 K x := by
      rw [Exploding.podo_apply_eq_sandpile]
      exact (LatticeProb.Sandpile.podo_isLegal s0).nonneg K x
    have hle : ¬ 0 < Exploding.podo s0 K x := by
      intro hpos
      apply hx
      rw [Exploding.podo_apply_eq_sandpile] at hpos
      have hbd := hFLPspec N hN x ⟨K, hpos⟩
      have hxL : ∀ i : Fin d, |x i| ≤ (L : ℤ) := by
        intro i
        have h1 : ((|x i| : ℤ) : ℝ) ≤ (L : ℝ) := by
          rw [Int.cast_abs]
          exact (hbd i).trans (Nat.le_ceil _)
        exact_mod_cast h1
      rw [hD, Finset.mem_Icc]
      exact ⟨fun i => (abs_le.mp (hxL i)).1, fun i => (abs_le.mp (hxL i)).2⟩
    have hz : Exploding.podo s0 K x = 0 := le_antisymm (not_lt.mp hle) hnn
    exact hz
  -- Origin bound on the finite domain, at the same time `K`.
  have hd0 : 0 < d := by omega
  have hh : (0 : ℤ) ≤ 2 * (d : ℤ) - 2 := by omega
  have hG := Exploding.squareOrigin_odometer_le_green hd0 (2 * (d : ℤ) - 2) hh N K D hO hsupp
  have hpile : Exploding.squareOrigin_pile (d := d) (2 * (d : ℤ) - 2) N = s0 := rfl
  rw [hpile] at hG
  have hcast : ((2 * (d : ℤ) - 2 : ℤ) : ℝ) = 2 * (d : ℝ) - 2 := by push_cast; ring
  rw [hcast] at hG
  have hdiagD := hdiagB L D hDbox
  have hrowD := hrow L D hDbox 0
  have hh_real : (0 : ℝ) ≤ 2 * (d : ℝ) - 2 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have h1 : (N : ℝ) * LatticeProb.Graph.killedGreenReal (LatticeProb.lattice d) (D : Set (Site d)) 0 0
      ≤ (N : ℝ) * (B * (if d = 2 then Real.log ((L : ℝ) + 2) else 1)) :=
    mul_le_mul_of_nonneg_left hdiagD (Nat.cast_nonneg N)
  have h2 : (2 * (d : ℝ) - 2) * ∑ y ∈ D,
      LatticeProb.Graph.killedGreenReal (LatticeProb.lattice d) (D : Set (Site d)) 0 y
      ≤ (2 * (d : ℝ) - 2) * (E * ((L : ℝ) + 1) ^ 2) :=
    mul_le_mul_of_nonneg_left hrowD hh_real
  have hfin : ((Exploding.podo s0 K 0 : ℤ) : ℝ) ≤
      (N : ℝ) * (B * (if d = 2 then Real.log ((L : ℝ) + 2) else 1)) +
        (2 * (d : ℝ) - 2) * (E * ((L : ℝ) + 1) ^ 2) := by
    linarith [hG, h1, h2]
  have e : (N : ℝ) * B * (if d = 2 then Real.log ((L : ℝ) + 2) else 1) +
      (2 * (d : ℝ) - 2) * E * ((L : ℝ) + 1) ^ 2 =
      (N : ℝ) * (B * (if d = 2 then Real.log ((L : ℝ) + 2) else 1)) +
        (2 * (d : ℝ) - 2) * (E * ((L : ℝ) + 1) ^ 2) := by ring
  refine ⟨K, r, hKt, hcubeK, hlow, ?_⟩
  rw [e]
  exact hfin

end Exploding
