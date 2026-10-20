/-
Proposition 2.2 of the paper: an infinite connected set of good cubes on the
macroscopic lattice, with small holes and a linear chemical distance.
-/
import Exploding.Support.Vocab
import Exploding.External.LiggettSchonmannStaceyBoundedDegree
import Exploding.External.MathieuHoles
import Exploding.External.AntalPisztora
import Exploding.Support.ArxivGoodCubeBondBoxCutoff
import Exploding.Support.AllHighGoodCubes
import Exploding.Support.ArxivAllGoodRenormGeometry
import Exploding.Support.ArxivMaximalGoodChemical

open Exploding LatticeProb MeasureTheory

-- The cited Mathieu binder stays in the statement as the paper gives it; the strict-support
-- argument proves the actual-cluster hole clause internally via `xmf_proved`.
set_option linter.unusedVariables false in
/-- **Proposition 2.2** (`paper/corrected-arxiv/exploding-corrected-arxiv.tex:354-369`, label `prop:renormalization_properties`).

"For fixed `k` large enough, there are constants `c, C` so that the following
hold on an event of probability 1.
 (1) There is a unique infinite maximal component `C_∞` of good cubes on the
     macroscopic lattice `{Q_k(i)}`.
 (2) There is `n_0` so that for `n ≥ n_0`, any connected component of `C_∞^c`
     that intersects `[-n,n]^d` has volume smaller than `(log n)^{5/2}`.
 (3) There is `n_0` so that for `n ≥ n_0`, for any `x, y ∈ C_∞` with `|x| ≤ n`
     and `|x-y| ≥ (log n)^2`, `c |x-y| ≤ d(x,y) ≤ C |x-y|`, where `d` is the
     chemical (graph) distance on `C_∞`."

`c` and `C` are fixed before `η`, as the paper fixes them before passing to the
probability-one event.  "Volume" is cardinality, and the finiteness of the
component is asserted alongside the bound so that no infinite set is read
through `Set.ncard = 0`.  The chemical distance is taken in `ℕ∞`, so the upper
bound also says that `x` and `y` are joined inside `C_∞`.

The percolation results the paper cites for this proposition enter as explicit
hypotheses: `hLSSB` (Liggett, Schonmann and Stacey, Corollary 1.4), `hHole`
(Mathieu, Lemma 5.2) and `hChem` (Antal and Pisztora, Theorem 1.1). -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.renormalization_properties (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᵐ η ∂(toyLaw d p),
        ∃ Cinf : Set (Site d), IsInfiniteConnectedGoodSet η k Cinf ∧
          (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ (cent d n : Set (Site d)),
            x ∉ Cinf →
              (componentIn Cinfᶜ x).Finite ∧
                ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2)) ∧
          (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x ∈ Cinf, ∀ y ∈ Cinf,
            mnorm x ≤ (n : ℤ) → Real.log n ^ (2 : ℕ) ≤ (mnorm (x - y) : ℝ) →
              ∃ m : ℕ, chemDist Cinf x y = (m : ℕ∞) ∧
                c * (mnorm (x - y) : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ C * (mnorm (x - y) : ℝ)) ∧
          (∃ z ∈ goodSites η k, Cinf = componentIn (goodSites η k) z) ∧
          (∀ z ∈ goodSites η k, (componentIn (goodSites η k) z).Infinite →
            componentIn (goodSites η k) z = Cinf)
-- FROZEN-STATEMENT-END
:= by
  rcases lt_or_eq_of_le hp1 with hpLt | hpEq
  · obtain ⟨k0, hk01, hk0⟩ :=
      arxiv_good_cube_bond_box_cutoff hLSSB hChem d hd p hp hpLt
    refine ⟨k0, fun k hk => ?_⟩
    obtain ⟨C, B, hC, hB, hae⟩ := hk0 k hk
    obtain ⟨A, hA, htransfer⟩ :=
      arxiv_maximal_good_component_chemical_transfer hd B C hB hC
    have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
    refine ⟨1, A, by norm_num, hApos, ?_⟩
    filter_upwards [hae] with η hη
    obtain ⟨ζ, i, hS, hholes, hcutoff, hchem⟩ := hη
    let I : Set (Site d) := {y | (openBondGraph ζ).Reachable i y}
    have hiI : i ∈ I := by
      change (openBondGraph ζ).Reachable i i
      exact ⟨SimpleGraph.Walk.nil⟩
    obtain ⟨Cstar, hCstar, hCstarGood, _, _, hunique, hCstarHoles, _⟩ :=
      arxivUniqueMaximalGoodCluster η k hS hholes i hiI
    have hchemK : RnChemClause d A (componentIn (goodSites η k) i) :=
      htransfer η k I i hS hiI hholes hchem hcutoff
    have hchemCstar : RnChemClause d A Cstar := by
      rw [hCstar]
      exact hchemK
    refine ⟨Cstar, hCstarGood, hCstarHoles, hchemCstar, ?_, ?_⟩
    · refine ⟨i, ?_, hCstar⟩
      exact hS.2.1 hiI
    · intro z hz hzinfinite
      have huniq := hunique (componentIn (goodSites η k) z) hzinfinite
        ⟨z, hz, rfl⟩
      exact huniq
  · have hpEqOne : p = 1 := by linarith
    subst p
    refine ⟨1, fun k hk => ?_⟩
    refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    filter_upwards [good_sites_all_scales_p1 d hd] with η hgood
    have hsites := hgood k hk
    obtain ⟨hCgood, hholes, hchem, hcomponent⟩ :=
      arxiv_all_good_renorm_geometry d hd η k hsites (0 : Site d)
    refine ⟨Set.univ, hCgood, hholes, hchem, ?_, ?_⟩
    · refine ⟨0, ?_, hcomponent.symm⟩
      rw [hsites]
      exact Set.mem_univ _
    · intro z hz _
      exact (arxiv_all_good_renorm_geometry d hd η k hsites z).2.2.2
