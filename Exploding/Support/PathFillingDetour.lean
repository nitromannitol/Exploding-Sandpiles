/-
The paper-facing form of the long detour.  The construction and its logarithmic threshold are
the generic lattice statement `LatticeProb.exists_long_lattice_path_avoiding_site`; this file
reads its conclusions through the box `cent` and the bounding rectangle `br` of the paper.
-/
import Exploding.Support.Vocab
import LatticeProb.Lattice.Detour

namespace Exploding

open LatticeProb

/-- For `2 ≤ d`, a site `x`, and a real exponent `γ`, there are an ambient box size `n ≥ n0`
and a length `m` with `(log n)^γ ≤ m`, and a map `z` whose first `m` points lie in `cent d n`,
are pairwise distinct, form a nearest-neighbour path, have bounding rectangle containing `x`,
and avoid `x`. -/
theorem exists_path_avoiding_site {d : ℕ} (hd : 2 ≤ d) (x : Site d) (γ : ℝ) (_hγ : 0 < γ)
    (n0 : ℕ) :
    ∃ (n m : ℕ) (z : ℕ → Site d), n0 ≤ n ∧
      Real.log (n : ℝ) ^ γ ≤ (m : ℝ) ∧
      (∀ i, i < m → z i ∈ cent d n) ∧
      (∀ i j, i < m → j < m → z i = z j → i = j) ∧
      (∀ i, i + 1 < m → (lattice d).Adj (z i) (z (i + 1))) ∧
      x ∈ br (z '' {i : ℕ | i < m}) ∧ x ∉ z '' {i : ℕ | i < m} := by
  obtain ⟨n, m, z, hn, hlog, hcent, hinj, hadj, hrect, havoid⟩ :=
    LatticeProb.exists_long_lattice_path_avoiding_site hd x γ n0
  refine ⟨n, m, z, hn, hlog, ?_, hinj, hadj, ?_, ?_⟩
  · intro i hi
    exact hcent i hi
  · show ∀ j, (∃ y ∈ z '' {i : ℕ | i < m}, y j ≤ x j) ∧
      (∃ y ∈ z '' {i : ℕ | i < m}, x j ≤ y j)
    intro j
    obtain ⟨⟨i, hi, hle⟩, ⟨i', hi', hge⟩⟩ := hrect j
    exact ⟨⟨z i, ⟨i, hi, rfl⟩, hle⟩, ⟨z i', ⟨i', hi', rfl⟩, hge⟩⟩
  · rintro ⟨i, hi, heq⟩
    exact havoid i hi heq

end Exploding
