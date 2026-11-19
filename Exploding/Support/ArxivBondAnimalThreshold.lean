import Exploding.Support.ArxivBondAnimalGeometric

/-!
# High-density threshold for the connected-set tail

Bernoulli's inequality bounds the probability that a unit cube is bad in terms
of the bond-defect probability. This gives the smallness condition for the
geometric connected-set estimate at every sufficiently high density.
-/

open LatticeProb MeasureTheory

namespace Exploding

/-- For any fixed counting constant, the geometric-tail condition holds at all
bond densities sufficiently close to one. -/
theorem exists_bond_animal_density_threshold (d K : ℕ) :
    ∃ q0 : ℝ, 0 ≤ q0 ∧ q0 < 1 ∧ ∀ q : ℝ, q0 ≤ q → q ≤ 1 →
      ((K : ENNReal) * 2) ^ (2 * 3 ^ d) * (1 - xap6_delta d q) ≤ 1 / 2 := by
  let M : ℕ := (xap_cubeBonds (0 : Site d)).card
  let C : ℝ := ((K : ℝ) * 2) ^ (2 * 3 ^ d)
  have hC : 0 ≤ C := by positivity
  let D : ℝ := 2 * (C + 1) * ((M : ℝ) + 1)
  have hD : 0 < D := by dsimp [D]; positivity
  have hDone : 1 ≤ D := by dsimp [D]; nlinarith [show (0 : ℝ) ≤ (M : ℝ) by positivity]
  let q0 : ℝ := 1 - 1 / D
  have hq0 : 0 ≤ q0 := by
    dsimp [q0]
    have : (1 : ℝ) / D ≤ 1 := (div_le_one₀ hD).2 hDone
    linarith
  have hq01 : q0 < 1 := by dsimp [q0]; have := one_div_pos.mpr hD; linarith
  refine ⟨q0, hq0, hq01, ?_⟩
  intro q hq hq1
  have hqnonneg : 0 ≤ q := hq0.trans hq
  have hbad : 1 - q ^ M ≤ (M : ℝ) * (1 - q) := by
    have hb := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ q by linarith) M
    nlinarith
  have hnear : 1 - q ≤ 1 / D := by dsimp [q0] at hq; linarith
  have hright : C * (M : ℝ) / D ≤ 1 / 2 := by
    rw [div_le_iff₀ hD]
    dsimp [D]
    nlinarith [mul_nonneg hC (Nat.cast_nonneg M)]
  have hreal : C * (1 - q ^ M) ≤ 1 / 2 := by
    calc
      C * (1 - q ^ M) ≤ C * ((M : ℝ) * (1 - q)) :=
        mul_le_mul_of_nonneg_left hbad hC
      _ ≤ C * ((M : ℝ) * (1 / D)) := by
        gcongr
      _ = C * (M : ℝ) / D := by ring
      _ ≤ 1 / 2 := hright
  have hCcast : ENNReal.ofReal C = ((K : ENNReal) * 2) ^ (2 * 3 ^ d) := by
    dsimp [C]
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity)]
    norm_num
  have hbadcast : ENNReal.ofReal (1 - q ^ M) = 1 - xap6_delta d q := by
    rw [ENNReal.ofReal_sub 1 (pow_nonneg hqnonneg M), ENNReal.ofReal_pow hqnonneg]
    simp only [ENNReal.ofReal_one, xap6_delta, M]
  calc
    ((K : ENNReal) * 2) ^ (2 * 3 ^ d) * (1 - xap6_delta d q) =
        ENNReal.ofReal (C * (1 - q ^ M)) := by
      rw [ENNReal.ofReal_mul hC, hCcast, hbadcast]
    _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hreal
    _ = 1 / 2 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      simp

/-- At high bond density, a large connected set with good sites confined to a
finite exceptional set has a geometric size tail. -/
theorem bond_connected_bad_cubes_geometric_at_high_density (d : ℕ) :
    ∃ q0 : ℝ, 0 ≤ q0 ∧ q0 < 1 ∧ ∀ q : ℝ, q0 ≤ q → q ≤ 1 →
      ∀ (p : Site d) (P : Finset (Site d)) (t : ℕ),
        1 ≤ t → P.card ≤ 3 ^ d * t →
        bondPercolation d q
          {ω | ∃ S : Set (Site d), xmh_SConn S ∧ p ∈ S ∧
            ((2 * 3 ^ d * t : ℕ) : ℕ∞) ≤ S.encard ∧
            ∀ x ∈ S, x ∉ P → ¬ xap_Good ω x} ≤ (1 / 2 : ENNReal) ^ t := by
  obtain ⟨K, hK⟩ := bond_connected_bad_cubes_prob_le_geometric d
  obtain ⟨q0, hq0, hq01, hsmall⟩ := exists_bond_animal_density_threshold d K
  refine ⟨q0, hq0, hq01, fun q hq hq1 p P t ht hP => ?_⟩
  exact hK p P t ht hP (hq0.trans hq) hq1 (hsmall q hq hq1)

end Exploding
