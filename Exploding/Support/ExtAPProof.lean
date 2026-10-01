/-
The high-density percolation input for the chemical-distance bound of Antal and
Pisztora: the good sites (whose whole unit cube is open) form a finitely
dependent field, the probability of a good cube is a power of the density, and a
path of star-adjacent good sites is an open path.
-/
import Exploding.Support.ExtAPDefs
import Exploding.Support.RNProofGraph

open Exploding LatticeProb MeasureTheory ProbabilityTheory

open scoped Classical

namespace Exploding

variable {d : ℕ}

/-! ### The cube and its bonds as finsets -/

/-- The cube of sup-norm radius one about `z`, as a finset. -/
noncomputable def xap_cubeFinset (z : Site d) : Finset (Site d) :=
  (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(1 : ℤ)) 1)).image (fun x => x + z)

theorem xap_mem_cubeFinset (z w : Site d) : w ∈ xap_cubeFinset z ↔ w ∈ xap_cube z := by
  simp only [xap_cubeFinset, Finset.mem_image, Fintype.mem_piFinset, Finset.mem_Icc, xap_cube,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    simp only [Pi.add_apply]
    have h1 : x i + z i - z i = x i := by ring
    rw [h1]
    exact abs_le.mpr (hx i)
  · intro h
    refine ⟨w - z, fun i => ?_, by ext i; simp⟩
    exact abs_le.mp (h i)

theorem xap_card_cubeFinset (z : Site d) : (xap_cubeFinset z).card = 3 ^ d := by
  rw [xap_cubeFinset, Finset.card_image_of_injective]
  · rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h3 : (Finset.Icc (-(1 : ℤ)) 1).card = 3 := by decide
    rw [h3]
  · intro x y h
    simpa using congrArg (fun w => w - z) h

/-- The bonds with both endpoints in the cube about `z`. -/
noncomputable def xap_cubeBonds (z : Site d) : Finset (Site d × Fin d) :=
  (((xap_cubeFinset z).product (Finset.univ : Finset (Fin d))).filter
    (fun e : Site d × Fin d => e.1 + unit e.2 ∈ xap_cube z))

theorem xap_mem_cubeBonds (z : Site d) (e : Site d × Fin d) :
    e ∈ xap_cubeBonds z ↔ e.1 ∈ xap_cube z ∧ e.1 + unit e.2 ∈ xap_cube z := by
  simp [xap_cubeBonds, xap_mem_cubeFinset]
/-! ### Good sites -/

theorem xap_good_iff (ω : Site d × Fin d → Bool) (z : Site d) :
    xap_Good ω z ↔ ∀ e ∈ xap_cubeBonds z, ω e = true := by
  constructor
  · intro h e he
    rw [xap_mem_cubeBonds] at he
    exact h e.1 e.2 he.1 he.2
  · intro h x i hx hi
    exact h (x, i) (by rw [xap_mem_cubeBonds]; exact ⟨hx, hi⟩)

theorem xap_good_measurable (z : Site d) :
    MeasurableSet {ω : Site d × Fin d → Bool | xap_Good ω z} := by
  rw [show {ω : Site d × Fin d → Bool | xap_Good ω z}
      = ⋂ e ∈ xap_cubeBonds z, {ω | ω e = true} by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact xap_good_iff ω z]
  exact MeasurableSet.biInter (xap_cubeBonds z).countable_toSet fun e _ => by
    have : {ω : Site d × Fin d → Bool | ω e = true} = (fun ω => ω e) ⁻¹' ({true} : Set Bool) :=
      rfl
    rw [this]
    exact (measurable_pi_apply e) (measurableSet_singleton true)

/-! ### The density of good sites -/

theorem xap_bitLaw_true (q : ℝ) : bitLaw q {true} = ENNReal.ofReal q := by
  unfold bitLaw
  simp [Measure.dirac_apply']

/-- The probability that every bond of a finite set is open is `q` to the number of bonds. -/
theorem xap_open_prob {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (S : Finset (Site d × Fin d)) :
    bondPercolation d q {ω | ∀ e ∈ S, ω e = true} = ENNReal.ofReal q ^ S.card := by
  haveI : IsProbabilityMeasure (bitLaw q) := ⟨by
    unfold bitLaw
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add h0 (by linarith)]
    norm_num⟩
  have hset : {ω : Site d × Fin d → Bool | ∀ b ∈ S, ω b = true}
      = Set.pi (↑S : Set (Site d × Fin d)) (fun _ => ({true} : Set Bool)) := by
    ext ω; simp
  unfold bondPercolation
  rw [hset, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  simp [xap_bitLaw_true]

/-- The probability of a good cube is `q` to the number of bonds in the cube. -/
theorem xap_good_prob {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (z : Site d) :
    bondPercolation d q {ω | xap_Good ω z} = ENNReal.ofReal q ^ (xap_cubeBonds z).card := by
  rw [show {ω : Site d × Fin d → Bool | xap_Good ω z}
      = {ω | ∀ e ∈ xap_cubeBonds z, ω e = true} by
    ext ω; exact xap_good_iff ω z]
  exact xap_open_prob h0 h1 _

/-! ### A path of good sites is an open path -/

/-- Two star-adjacent good sites span a common open edge. -/
theorem xap_open_reach_of_star {ω : Site d × Fin d → Bool} {a b : Site d}
    (ha : xap_Good ω a) (hab : xap_Star a b) :
    Relation.ReflTransGen (openBondGraph ω).Adj a b :=
  xap_reach_open (xap_cube_reach' ha (xap_mem_cube_self a) (xap_star_mem_cube hab))

/-- A star-chain of good sites gives an open path between its endpoints. -/
theorem xap_reachable_of_goodChain {ω : Site d × Fin d → Bool} {a b : Site d}
    (h : Relation.ReflTransGen
      (fun x y => xap_Star x y ∧ xap_Good ω x ∧ xap_Good ω y) a b) :
    (openBondGraph ω).Reachable a b := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
      exact ih.trans (xap_open_reach_of_star hbc.2.1 hbc.1)

end Exploding
