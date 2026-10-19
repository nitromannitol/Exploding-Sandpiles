/-
Proposition 5.1 of the paper (generalized last wave): the two open claims behind the local bound
and the closeness of the arrival times, isolated as a probabilistic claim (the infinite cluster
of strongly box-crossing tiles) and a deterministic claim (the Section-3 estimates run on the
event of that cluster and of Hypothesis 3), and their assembly into `glws_Origin` and
`glws_Close`.

The finiteness of the last wave at every site is proved here from the cluster
(`glws_finite_exploding`), so the deterministic claim carries only the quantitative bounds.
-/
import Exploding.Support.GLWSec3H
import Exploding.Support.GLWSec3I

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

/-- The body of Hypothesis 3 (path-filling) at a fixed background and exponent. -/
def glws_PF (d : ℕ) (γ : ℝ) (η : Site d → ℤ) : Prop :=
  ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
    ∀ (m : ℕ) (z : ℕ → Site d),
      Real.log n ^ γ ≤ (m : ℝ) →
      (∀ i, i < m → z i ∈ cent d n) →
      (∀ i j, i < m → j < m → z i = z j → i = j) →
      (∀ i, i + 1 < m → (lattice d).Adj (z i) (z (i + 1))) →
      ∀ t : ℕ, m ^ d ≤ t → ∀ x ∈ br (z '' {i : ℕ | i < m}),
        1 ≤ fodo (z '' {i : ℕ | i < m}) η (Set.indicator (z '' {i : ℕ | i < m}) 1) t x

/-- The infinite cluster of strongly box-crossing tiles of side lengths `k`, with the properties
of Proposition 2.2: an infinite connected set `C_∞` of strongly box-crossing tiles (indexed by
macroscopic sites), such that for `n` large the components of `C_∞ᶜ` meeting `[-n,n]^d` have
volume below `(log n)^{5/2}`, and the chemical distance in `C_∞` between points at distance at
least `(log n)^2` is between `c` and `C` times their `ℓ¹` distance. -/
def glws_Clu (d : ℕ) (k : Fin d → ℕ) (c C : ℝ) (η : Site d → ℤ) : Prop :=
  ∃ Cinf : Set (Site d), Cinf.Infinite ∧ (∀ j ∈ Cinf, StronglyBoxCrossed η k j) ∧
    (∀ x ∈ Cinf, ∀ y ∈ Cinf, y ∈ componentIn Cinf x) ∧
    (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf →
      (componentIn Cinfᶜ x).Finite ∧
        ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2)) ∧
    (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ Cinf, ∀ y ∈ Cinf,
      mnorm x ≤ (n : ℤ) → Real.log n ^ (2 : ℕ) ≤ (mnorm (x - y) : ℝ) →
        ∃ m : ℕ, chemDist Cinf x y = (m : ℕ∞) ∧
          c * (mnorm (x - y) : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ C * (mnorm (x - y) : ℝ))

/-- **The probabilistic claim** (the generalization of Proposition 2.2, paper
`exploding.tex:1198-1203`).  Under Hypotheses 1 and 4 the field of strongly box-crossing tiles
is `m`-dependent with marginals close to one; by the Liggett-Schonmann-Stacey domination the good
edges dominate a supercritical bond percolation (the dependence graph has bounded degree), and the
argument before Proposition 2.2 (Mathieu's bound on the holes, Antal and Pisztora's chemical
distance bound) gives the cluster on an event of probability one. -/
def glws_Renorm (d : ℕ) (P : Measure (Site d → ℤ)) : Prop :=
  2 ≤ d → IsProbabilityMeasure P → FiniteRangeOfDependence d P → StronglyBoxCrossingHyp d P →
  Exploding.External.LiggettSchonmannStacey →
  Exploding.External.LiggettSchonmannStaceyBoundedDegree →
  Exploding.External.MathieuHoleVolume →
  Exploding.External.AntalPisztoraChemicalDistance →
  ∃ k : Fin d → ℕ, (∀ i, 0 < k i) ∧ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ᵐ η ∂P, glws_Clu d k c C η

/-- **The deterministic claim** (paper `exploding.tex:1217-1230`, "the rest of the argument follows
the proof in Section 3 with the boxes of `C_∞` in place of the good cubes", and the proof of
`eq:generalized_lipschitz`).  On a background with `0 ≤ η ≤ 2d - 1` satisfying path-filling and
carrying the cluster, the first bound `T̃(x) ≤ C |x| + (log n)^γ`, the second bound
`T̃(x') ≤ T̃(x) + C |x - x'| + (log n)^γ` and the closeness `T̃(x) ≤ T̂(x) + (log n)^{γ'}` hold, all
arrival times measured from the origin, for `n` large.  The constants depend on the data of the
cluster and on the path-filling exponent only. -/
def glws_Det (d : ℕ) : Prop :=
  2 ≤ d → ∀ k : Fin d → ℕ, (∀ i, 0 < k i) → ∀ c C : ℝ, 0 < c → 0 < C → ∀ γp : ℝ, 0 < γp →
    ∃ γ C' γ' : ℝ, 0 < γ ∧ 0 < C' ∧ 0 < γ' ∧ ∀ η : Site d → ℤ, (∀ x, 0 ≤ η x) →
      (∀ x, η x ≤ 2 * (d : ℤ) - 1) → glws_PF d γp η → glws_Clu d k c C η →
      (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ cent d n, ∃ a : ℕ,
        clusterArrival η (0 : Site d) x = (a : ℕ∞) ∧
          (a : ℝ) ≤ C' * (mnorm x : ℝ) + Real.log n ^ γ ∧
          ∀ x' ∈ cent d n, ∃ b : ℕ, clusterArrival η (0 : Site d) x' = (b : ℕ∞) ∧
            (b : ℝ) ≤ (a : ℝ) + C' * (mnorm (x - x') : ℝ) + Real.log n ^ γ) ∧
      (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
        lastArrival η (0 : Site d) x ≤ clusterArrival η (0 : Site d) x ∧
          ∃ a b : ℕ, lastArrival η (0 : Site d) x = (a : ℕ∞) ∧
            clusterArrival η (0 : Site d) x = (b : ℕ∞) ∧ (b : ℝ) ≤ (a : ℝ) + Real.log n ^ γ')

/-- The paper's local bound follows from the cluster and the deterministic claim. -/
theorem glws_origin_of (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (P : Measure (Site d → ℤ)) (hR : glws_Renorm d P) (hD : glws_Det d) :
    glws_Origin d ηmin P := by
  intro hP hsupp h1 h3 h4 hLSS hLSSB hHole hChem
  obtain ⟨k, hk, c, C, hc, hC, hclu⟩ := hR hd hP h1 h4 hLSS hLSSB hHole hChem
  obtain ⟨γp, hγp, hpf⟩ := h3
  obtain ⟨γ, C', γ', hγ, hC', _, hdet⟩ := hD hd k hk c C hc hC γp hγp
  refine ⟨γ, C', hγ, hC', ?_⟩
  filter_upwards [hclu, hpf, hsupp] with η hη1 hη2 hη3
  have hlow : ∀ x, 0 ≤ η x := fun x => le_trans hηmin (hη3 x).1
  have hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1 := fun x => (hη3 x).2
  obtain ⟨hfirst, _⟩ := hdet η hlow hhigh hη2 hη1
  obtain ⟨Cinf, hinf, hgood, hconn, _, _⟩ := hη1
  exact ⟨fun y => glws_finite_exploding hd η hlow hhigh k hk Cinf hinf hgood hconn y, hfirst⟩

/-- The closeness of the arrival times follows from the cluster and the deterministic claim. -/
theorem glws_close_of (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (P : Measure (Site d → ℤ)) (hR : glws_Renorm d P) (hD : glws_Det d) :
    glws_Close d ηmin P := by
  intro hP hsupp h1 h3 h4 hLSS hLSSB hHole hChem
  obtain ⟨k, hk, c, C, hc, hC, hclu⟩ := hR hd hP h1 h4 hLSS hLSSB hHole hChem
  obtain ⟨γp, hγp, hpf⟩ := h3
  obtain ⟨γ, C', γ', hγ, hC', hγ', hdet⟩ := hD hd k hk c C hc hC γp hγp
  refine ⟨γ', hγ', ?_⟩
  filter_upwards [hclu, hpf, hsupp] with η hη1 hη2 hη3
  have hlow : ∀ x, 0 ≤ η x := fun x => le_trans hηmin (hη3 x).1
  have hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1 := fun x => (hη3 x).2
  exact (hdet η hlow hhigh hη2 hη1).2

/-- **Proposition 5.1 from the probabilistic claim and the deterministic claim.**  No Kingman
proposition is assumed: the subadditive ergodic step is `king_lipKingman`. -/
theorem glws_conclusion_of (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (L : AddSubgroup (Site d)) (hL : L.index ≠ 0) (P : Measure (Site d → ℤ))
    (hP : IsProbabilityMeasure P) (hsupp : ∀ᵐ η ∂P, InOmega d ηmin η)
    (hstat : StationaryOn d L P)
    (h1 : FiniteRangeOfDependence d P) (h3 : PathFillingHyp d P)
    (h4 : StronglyBoxCrossingHyp d P)
    (hLSS : Exploding.External.LiggettSchonmannStacey)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance)
    (hR : glws_Renorm d P) (hD : glws_Det d) :
    glw_Conclusion d P :=
  glws_conclusion d hd ηmin hηmin L hL P hP hsupp hstat h1 h3 h4 hLSS hLSSB hHole hChem
    (glws_origin_of d hd ηmin hηmin P hR hD) (glws_close_of d hd ηmin hηmin P hR hD)

/-- **The uniform-origin form of the deterministic bound** (the second bound of
`glw2_LipschitzLocal`).  It asks for the penultimate-cluster arrival time `T̃(x, x')` of the last wave
started at an arbitrary `x ∈ [-n,n]^d`, with a threshold `n0` that is uniform in `x`.  This is
strictly stronger than the paper's bound `eq:generalized_lipschitz`, which is measured from the
origin only (`glws_Det`); it needs, in addition, that from every `x` in the box the last wave
reaches the cluster within a power of `log n`, which the paper does not prove.  It is stated for
`glws_lipschitzLocal` only and is not used by the assembly of Proposition 5.1. -/
def glws_DetStrong (d : ℕ) : Prop :=
  2 ≤ d → ∀ k : Fin d → ℕ, (∀ i, 0 < k i) → ∀ c C : ℝ, 0 < c → 0 < C → ∀ γp : ℝ, 0 < γp →
    ∃ γ C' : ℝ, 0 < γ ∧ 0 < C' ∧ ∀ η : Site d → ℤ, (∀ x, 0 ≤ η x) →
      (∀ x, η x ≤ 2 * (d : ℤ) - 1) → glws_PF d γp η → glws_Clu d k c C η →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ cent d n, ∃ a : ℕ,
        clusterArrival η (0 : Site d) x = (a : ℕ∞) ∧
          ∀ x' ∈ cent d n, ∃ c : ℕ, clusterArrival η x x' = (c : ℕ∞) ∧
            (c : ℝ) ≤ C' * (mnorm (x - x') : ℝ) + Real.log n ^ γ

/-- **The local Lipschitz bound `glw2_LipschitzLocal`** from the probabilistic claim and the
uniform-origin deterministic bound; the finiteness of the last wave at every site is proved from the
cluster. -/
theorem glws_lipschitzLocal (d : ℕ) (hd : 2 ≤ d) (ηmin : ℤ) (hηmin : 0 ≤ ηmin)
    (P : Measure (Site d → ℤ)) (hR : glws_Renorm d P) (hS : glws_DetStrong d) :
    glw2_LipschitzLocal d ηmin P := by
  intro hP hsupp h1 h3 h4 hLSS hLSSB hHole hChem
  obtain ⟨k, hk, c, C, hc, hC, hclu⟩ := hR hd hP h1 h4 hLSS hLSSB hHole hChem
  obtain ⟨γp, hγp, hpf⟩ := h3
  obtain ⟨γ, C', hγ, hC', hdet⟩ := hS hd k hk c C hc hC γp hγp
  refine ⟨γ, C', hγ, hC', ?_⟩
  filter_upwards [hclu, hpf, hsupp] with η hη1 hη2 hη3
  have hlow : ∀ x, 0 ≤ η x := fun x => le_trans hηmin (hη3 x).1
  have hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1 := fun x => (hη3 x).2
  have hstr := hdet η hlow hhigh hη2 hη1
  obtain ⟨Cinf, hinf, hgood, hconn, _, _⟩ := hη1
  exact ⟨fun y => glws_finite_exploding hd η hlow hhigh k hk Cinf hinf hgood hconn y, hstr⟩

end Exploding
