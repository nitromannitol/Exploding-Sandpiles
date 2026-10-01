/-
Proposition 5.1 of the paper (generalized last wave): the local bound from the origin
(`eq:generalized_lipschitz`) from the probabilistic claim `glws_Renorm` alone.  The deterministic
Section-3 estimates are proved (`glws_loc0_of_cl`); no deterministic claim remains.
-/
import Exploding.Support.GLWSec3AB

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

/-- A background carrying the cluster `glws_Clu`, with `0 ≤ η ≤ 2d - 1` and path-filling, carries the
bundled data `glws_Cl` (the chemical-distance upper bound only is kept). -/
theorem glws_Cl_of_Clu (hd : 2 ≤ d) (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (c C : ℝ) (hC : 0 < C)
    (γp : ℝ) (hγp : 0 < γp) (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (hpf : glws_PF d γp η) (h : glws_Clu d k c C η) :
    ∃ Cinf : Set (Site d), glws_Cl d η k Cinf γp C := by
  obtain ⟨Cinf, hinf, hgood, hconn, hole, n0c, hchem⟩ := h
  refine ⟨Cinf, ⟨hd, hlow, hhigh, hk, hinf, hgood, hconn, hole, ⟨n0c, ?_⟩, hγp, hC.le, hpf⟩⟩
  intro n hn x hx y hy hxn hxy
  obtain ⟨m, hm, _, hm2⟩ := hchem n hn x hx y hy hxn hxy
  exact ⟨m, hm, hm2⟩

/-- **The paper's local bound from the origin** (`eq:generalized_lipschitz`) from the probabilistic
claim: no deterministic hypothesis remains. -/
theorem glws_origin_of_renorm (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (P : Measure (Site d → ℤ)) (hR : glws_Renorm d P) : glws_Origin d ηmin P := by
  intro hP hsupp h1 h3 h4 hLSS hLSSB hHole hChem
  obtain ⟨k, hk, c, C, hc, hC, hclu⟩ := hR hd hP h1 h4 hLSS hLSSB hHole hChem
  obtain ⟨γp, hγp, hpf⟩ := h3
  obtain ⟨γ, C', hγ, hC', hloc⟩ := glws_loc0_of_cl hd k γp C hγp
  refine ⟨γ, C', hγ, hC', ?_⟩
  filter_upwards [hclu, hpf, hsupp] with η hη1 hη2 hη3
  have hlow : ∀ x, 0 ≤ η x := fun x => le_trans hηmin (hη3 x).1
  have hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1 := fun x => (hη3 x).2
  obtain ⟨Cinf, S⟩ := glws_Cl_of_Clu hd k hk c C hC γp hγp η hlow hhigh hη2 hη1
  exact hloc η Cinf S

end Exploding
