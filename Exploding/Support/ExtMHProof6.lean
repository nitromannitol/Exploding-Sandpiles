/-
The deterministic core of the hole-volume assembly: a finite component `B` of the
complement of an infinite connected set `C` whose volume exceeds the threshold has a
`*`-connected inner boundary of at least the prescribed size, because the neighbours of
`B` outside `B` all lie in `C` and the boundary is `*`-connected in every dimension.
-/
import Exploding.Support.ExtMHProof5
import Exploding.Support.Vocab

namespace Exploding

open LatticeProb Relation

variable {d : ℕ}

/-- The volume threshold of Mathieu's Lemma 5.2. -/
noncomputable def xmh3_V (n : ℕ) : ℝ := Real.log n ^ ((5 : ℝ) / 2)

/-- **Deterministic boundary witness.**  If a finite connected `B` disjoint from a
connected `C` is closed under adjacency outside `C`, has volume at least `xmh3_V n`, and
every such `B` of that volume has inner boundary of cardinality at least `m n` (the
isoperimetric input), then the sites of `B` adjacent to `C` form a `*`-connected set of
cardinality at least `m n`. -/
theorem xmh3_boundary_witness {C B : Set (Site d)} (m : ℕ → ℕ)
    (hIso : ∀ (n : ℕ) (B : Set (Site d)), B.Finite → B.Nonempty →
      (∀ u ∈ B, ∀ v ∈ B, ReflTransGen (fun a b => a ∈ B ∧ b ∈ B ∧ (lattice d).Adj a b) u v) →
      xmh3_V n ≤ (B.ncard : ℝ) → m n ≤ (innerBoundary B).ncard)
    (hCconn : ∀ u ∈ C, ∀ v ∈ C,
      ReflTransGen (fun a b => a ∈ C ∧ b ∈ C ∧ (lattice d).Adj a b) u v)
    (hBconn : ∀ u ∈ B, ∀ v ∈ B,
      ReflTransGen (fun a b => a ∈ B ∧ b ∈ B ∧ (lattice d).Adj a b) u v)
    (hdisj : ∀ z, z ∈ C → z ∈ B → False)
    (hclose : ∀ b ∈ B, ∀ z, (lattice d).Adj b z → z ∉ C → z ∈ B)
    (hBfin : B.Finite) (hBne : B.Nonempty) (n : ℕ) (hBvol : xmh3_V n ≤ (B.ncard : ℝ)) :
    xmh_SConn {z | z ∈ B ∧ ∃ c ∈ C, (lattice d).Adj c z} ∧
      m n ≤ ({z | z ∈ B ∧ ∃ c ∈ C, (lattice d).Adj c z} : Set (Site d)).ncard := by
  have hDeq : {z | z ∈ B ∧ ∃ c ∈ C, (lattice d).Adj c z} = innerBoundary B := by
    ext z
    constructor
    · rintro ⟨hzB, c, hcC, hcz⟩
      exact ⟨hzB, c, fun hcB => hdisj c hcC hcB, hcz.symm⟩
    · rintro ⟨hzB, y, hyB, hzy⟩
      refine ⟨hzB, y, ?_, hzy.symm⟩
      by_contra hyC
      exact hyB (hclose z hzB y hzy hyC)
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    exact xmh3_boundaryStar d C B hCconn hBconn hdisj hclose x y hx hy
  · rw [hDeq]
    exact hIso n B hBfin hBne hBconn hBvol

end Exploding
