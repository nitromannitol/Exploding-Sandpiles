/-
Proposition 2.2 of the paper: an infinite connected set of good cubes on the
macroscopic lattice, with small holes and a linear chemical distance.
-/
import Exploding.Support.Vocab
import Exploding.External.LiggettSchonmannStaceyBoundedDegree
import Exploding.External.MathieuHoles
import Exploding.External.AntalPisztora
import Exploding.Support.RNProofGood
import Exploding.Support.RNProofPeierls

open Exploding LatticeProb MeasureTheory

/-- **Proposition 2.2** (`exploding.tex:482-497`, label
`prop:renormalization_properties`).

"For fixed `k` large enough, there are constants `c, C` so that the following
hold on an event of probability 1.
 (1) There is an infinite connected set `C_∞` of good cubes on the macroscopic
     lattice `{Q_k(i)}`.
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
theorem Exploding.Frozen.renormalization_properties (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
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
                c * (mnorm (x - y) : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ C * (mnorm (x - y) : ℝ))
-- FROZEN-STATEMENT-END
:= by
  have hPE : ∃ qP : ℝ, 0 ≤ qP ∧ qP < 1 ∧ ∀ q : ℝ, qP ≤ q → q ≤ 1 → bondTheta d q ≠ 0 :=
    ⟨255 / 256, by norm_num, by norm_num, fun _ hq0 hq1 => pe_theta_ne_zero hd hq0 hq1⟩
  exact rn_renormalization hLSSB hHole hChem d hd p hp hp1 hPE
