/-
The far Lipschitz bound of Proposition 3.1 (`eq:lastwave_lipschitz`) as a standalone
theorem.  The bound for the last-wave arrival times `T̂` (`lwcl_lastArrival_lip`) is transferred to
the penultimate-cluster arrival times `T̃` through Lemma 3.7:
`T̂ ≤ T̃ ≤ T̂ + (log n)^γ`.  Only the second bound of `eq:lastwave_lipschitz` is needed in the
symmetric form `|T̃(x) - T̃(x')| ≤ C |x - x'| + (log n)^γ`, since `T̂(x') ≤ T̂(x) + ...` and
`T̂(x) ≤ T̂(x') + ...` are the same statement with the roles of `x` and `x'` exchanged.
-/
import Exploding.Support.LWCLipD

namespace Exploding

open LatticeProb MeasureTheory Filter

/-- **The far Lipschitz bound** (the `hlip` conjunct of `Exploding.Frozen.convergence_of_the_last_wave`).
Almost surely, for all large `n` and all `x, x'` of the box `[-n,n]^d`,
`|T̃(x) - T̃(x')| ≤ C |x - x'| + (log n)^γ`. -/
theorem lwcl_far_lipschitz (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∀ᵐ η ∂(toyLaw d p), ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ∀ x x' : Site d, x ∈ cent d n → x' ∈ cent d n →
        |((clusterArrival η (0 : Site d) x).toNat : ℝ) -
          ((clusterArrival η (0 : Site d) x').toNat : ℝ)|
            ≤ C * (mnorm (x - x') : ℝ) + Real.log n ^ γ := by
  obtain ⟨γ1, C, hγ1, hC, hlip⟩ := lwcl_lastArrival_lip d hd p hp hp1 hLSSB hHole hChem
  obtain ⟨γ2, hγ2, hclose⟩ := Exploding.Frozen.last_penultimate_close d hd p hp hp1.le hLSSB hHole hChem
  have hd1 : 1 ≤ d := by omega
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp (lwc_cluster_lipschitz_1_1 γ1 γ2)
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp
    (lwc_cluster_lipschitz_1_5 d hd1 (max γ1 γ2 + 1) (by positivity))
  filter_upwards [hlip, hclose] with η hl hc
  obtain ⟨n0l, hn0l⟩ := hl
  obtain ⟨n0c, hn0c⟩ := hc
  refine ⟨C, max γ1 γ2 + 1 + 1, hC, by positivity,
    max (max n0l n0c) (max N1 N2), fun n hn x x' hx hx' => ?_⟩
  have hnl : n0l ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnc : n0c ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hdn : n ≤ d * n := Nat.le_mul_of_pos_left n (by omega)
  have hcast : (((d * n : ℕ)) : ℝ) = (d : ℝ) * (n : ℝ) := by push_cast; ring
  have hxM : mnorm x ≤ ((d * n : ℕ) : ℤ) := by
    push_cast; exact lwc_cluster_lipschitz_1_6 d n x hx
  have hx'M : mnorm x' ≤ ((d * n : ℕ) : ℤ) := by
    push_cast; exact lwc_cluster_lipschitz_1_6 d n x' hx'
  obtain ⟨a, a', hax, hax', hab⟩ := hn0l (d * n) (by omega) x x' hxM hx'M
  obtain ⟨a3, a4, ha3, ha4, hab'⟩ := hn0l (d * n) (by omega) x' x hx'M hxM
  obtain ⟨hle1, a1, b1, ha1, hb1, hbb1⟩ := hn0c (d * n) (by omega) x hxM
  obtain ⟨hle2, a2, b2, ha2, hb2, hbb2⟩ := hn0c (d * n) (by omega) x' hx'M
  have huniq : ∀ u v : ℕ, (u : ℕ∞) = (v : ℕ∞) → u = v := fun u v h => by exact_mod_cast h
  have hA : a = a1 := huniq _ _ (hax.symm.trans ha1)
  have hA' : a' = a2 := huniq _ _ (hax'.symm.trans ha2)
  have hA3 : a3 = a2 := huniq _ _ (ha3.symm.trans ha2)
  have hA4 : a4 = a1 := huniq _ _ (ha4.symm.trans ha1)
  have hAR : (a : ℝ) = (a1 : ℝ) := by exact_mod_cast hA
  have hA'R : (a' : ℝ) = (a2 : ℝ) := by exact_mod_cast hA'
  have hA3R : (a3 : ℝ) = (a2 : ℝ) := by exact_mod_cast hA3
  have hA4R : (a4 : ℝ) = (a1 : ℝ) := by exact_mod_cast hA4
  rw [ha1, hb1] at hle1
  rw [ha2, hb2] at hle2
  have hle1R : (a1 : ℝ) ≤ (b1 : ℝ) := by exact_mod_cast (by exact_mod_cast hle1 : a1 ≤ b1)
  have hle2R : (a2 : ℝ) ≤ (b2 : ℝ) := by exact_mod_cast (by exact_mod_cast hle2 : a2 ≤ b2)
  have hsym : mnorm (x' - x) = mnorm (x - x') := pub_mnorm_sub_comm x' x
  rw [hsym] at hab'
  have hlog1 := hN1 (d * n) (by omega)
  have hlog2 := hN2 n hn2
  have hlog3 : Real.log ((d : ℝ) * (n : ℝ)) ^ (max γ1 γ2 + 1) ≤
      Real.log n ^ (max γ1 γ2 + 1 + 1) := hlog2
  rw [hcast] at hlog1 hab hab' hbb1 hbb2
  rw [hb1, hb2, ENat.toNat_coe, ENat.toNat_coe]
  rw [abs_sub_le_iff]
  constructor <;> linarith

end Exploding
