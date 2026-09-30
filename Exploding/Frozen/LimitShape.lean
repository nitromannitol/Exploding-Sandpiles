/-
Theorem 1.2 of the paper: the support of the exploding sandpile, rescaled by
time, converges in measure to a convex domain.
-/
import Exploding.Support.Vocab
import Exploding.Support.LSProofAux
import Exploding.External.LiggettSchonmannStaceyBoundedDegree
import Exploding.External.MathieuHoles
import Exploding.External.AntalPisztora
import Exploding.External.Schonmann

open Exploding LatticeProb MeasureTheory Filter

/-- **Theorem 1.2** (`exploding.tex:246-254`, label `theorem:limit_shape`).

"Let `η` be as in (1.2).  There exists a convex domain `B(p) ⊂ ℝ^d` so that on
an event of probability 1, `|{v̄_t > 0} △ B(p)| → 0`, where
`v̄_t(x) := v_t([t x])`."

`v_t` is the parallel toppling odometer of `η + M_η δ₀`; `[·]` is the nearest
lattice point `Exploding.nearestSite`; `|·|` is Lebesgue measure on `ℝ^d`; `△`
is the symmetric difference.  A *domain* is a nonempty open connected set, and
a nonempty open convex set is connected, so convexity, openness and
nonemptiness are the clauses carried.  `B(p)` is deterministic: it is bound
before `η`.

The results the paper cites for Proposition 2.2 (`hLSSB`, `hHole`, `hChem`) and
Schonmann's bound behind Theorem 1.4 (`hSch`) enter as explicit hypotheses. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.limit_shape (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance)
    (hSch : Exploding.External.SchonmannBootstrap) :
    ∃ B : Set (Fin d → ℝ),
      Convex ℝ B ∧ IsOpen B ∧ B.Nonempty ∧
      ∀ᵐ η ∂(toyLaw d p),
        Tendsto
          (fun t : ℕ =>
            volume (symmDiff
              {y : Fin d → ℝ | 0 < podo (explodingPile η) t (nearestSite ((t : ℝ) • y))} B))
          atTop (nhds 0)
-- FROZEN-STATEMENT-END
:= Exploding.LSProof.ls_assemble d hd p hp hp1
    (Exploding.LSProof.ls_flp_from_explosive hSch) hLSSB hHole hChem
