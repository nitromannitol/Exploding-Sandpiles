import Exploding.Support.ExtMHProof13

/-!
# Infinite inner boundaries from two infinite sides

A finite inner boundary is contained in a box, and its exterior neighbors are contained in an
enlargement of that box. Connectivity outside the enlarged box rules out infinite sets on both
sides of the boundary.
-/

namespace Exploding

open LatticeProb Relation

/-- A set with infinite complement and itself has infinite inner boundary in dimension at least
two. -/
theorem arxiv_innerBoundary_infinite_of_infinite_compl
    {d : ℕ} (hd : 2 ≤ d) {B : Set (Site d)}
    (hB : B.Infinite) (hBc : Bᶜ.Infinite) :
    (innerBoundary B).Infinite := by
  classical
  by_contra hfin
  have hdfin : (innerBoundary B).Finite := Set.not_infinite.mp hfin
  let F : Set (Site d) := {y | y ∉ B ∧ ∃ b ∈ B, (lattice d).Adj b y}
  have hFsub : F ⊆ {y : Site d | ∃ b ∈ innerBoundary B, (lattice d).Adj b y} := by
    rintro y ⟨hyB, b, hbB, hby⟩
    exact ⟨b, ⟨hbB, y, hyB, hby⟩, hby⟩
  obtain ⟨N, hN⟩ := xmh9_finite_subset_cent _ hdfin
  have hunit : ∀ (k : Fin d) (i : Fin d), |(unit k : Site d) i| ≤ 1 := by
    intro k i
    by_cases h : i = k
    · subst h; simp [unit, Pi.single_eq_same]
    · simp [unit, Pi.single_eq_of_ne h]
  have hFcent : F ⊆ cent d (N + 1) := by
    refine hFsub.trans ?_
    rintro y ⟨b, hbd, hby⟩
    intro i
    have hbi : |b i| ≤ (N : ℤ) := hN hbd i
    have hy : |y i| ≤ |b i| + 1 := by
      rcases hby with ⟨k, hk | hk⟩
      · have hyi : y i = b i + unit k i := by rw [hk, Pi.add_apply]
        rw [hyi]
        exact (abs_add_le _ _).trans (by linarith [hunit k i])
      · have hyi : y i = b i - unit k i := by rw [hk, Pi.add_apply]; ring
        rw [hyi, sub_eq_add_neg]
        exact (abs_add_le _ _).trans (by rw [abs_neg]; linarith [hunit k i])
    push_cast
    linarith
  have hclosed : ∀ s ∈ B, ∀ t ∉ cent d (N + 1), (lattice d).Adj s t → t ∈ B := by
    intro s hs t ht hst
    by_contra htB
    exact ht (hFcent ⟨htB, s, hs, hst⟩)
  obtain ⟨b, hbB, hbnot⟩ : ∃ b ∈ B, b ∉ cent d (N + 1) := by
    obtain ⟨b, hb⟩ := (hB.sdiff (xmh9_cent_finite (d := d) (N + 1))).nonempty
    exact ⟨b, hb.1, hb.2⟩
  obtain ⟨c, hcBc, hcnot⟩ : ∃ c ∈ Bᶜ, c ∉ cent d (N + 1) := by
    obtain ⟨c, hc⟩ := (hBc.sdiff (xmh9_cent_finite (d := d) (N + 1))).nonempty
    exact ⟨c, hc.1, hc.2⟩
  have hpath := xmh9_conn_compl_cent hd (N + 1) b hbnot c hcnot
  have hcB : c ∈ B := xmh9_closed_rtg hclosed hbB hpath
  exact hcBc hcB

end Exploding
