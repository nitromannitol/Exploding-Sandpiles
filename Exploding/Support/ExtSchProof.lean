/-
A deterministic seed for the bootstrap-percolation bound: on the two-dimensional
cube, a fully occupied diagonal fills the whole cube.  A site off the diagonal
topples once its two neighbours toward the diagonal have toppled, so the
occupied diagonal spreads to the whole cube.
-/
import Exploding.Support.ExtSchProb

namespace Exploding

open LatticeProb

/-- **Diagonal seed in two dimensions.**  If every diagonal site of `Q_n^2`
carries `2d` chips, then every site of the cube topples with threshold `d = 2`. -/
theorem xsch_sp_diag_two (n : ℕ) (η : Site 2 → ℤ)
    (hdiag : ∀ x ∈ cube 2 n, x 0 = x 1 → η x = 2 * (2 : ℤ)) :
    xsch_Sp (Finset.univ : Finset (Fin 2)) (cube 2 n) η := by
  have key1 : ∀ k : ℕ, ∀ x : Site 2, x ∈ cube 2 n → x 0 - x 1 = (k : ℤ) →
      xsch_Top (Finset.univ : Finset (Fin 2)) (cube 2 n) η x := by
    intro k
    induction k with
    | zero =>
      intro x hx h
      exact xsch_Top.occ hx (hdiag x hx (by omega))
    | succ k ih =>
      intro x hx h
      have h0 : 1 ≤ x 0 := (hx 0).1
      have h1 : 1 ≤ x 1 := (hx 1).1
      have h0n : x 0 ≤ (n : ℤ) := (hx 0).2
      have h1n : x 1 ≤ (n : ℤ) := (hx 1).2
      have hx0ge2 : 2 ≤ x 0 := by omega
      have hy0 : (x + xsch_dir ((0 : Fin 2), false)) 0 = x 0 - 1 := by simp [xsch_dir, unit, sub_eq_add_neg]
      have hy1 : (x + xsch_dir ((0 : Fin 2), false)) 1 = x 1 := by simp [xsch_dir, unit]
      have hz0 : (x + xsch_dir ((1 : Fin 2), true)) 0 = x 0 := by simp [xsch_dir, unit]
      have hz1 : (x + xsch_dir ((1 : Fin 2), true)) 1 = x 1 + 1 := by simp [xsch_dir, unit]
      have hy : x + xsch_dir ((0 : Fin 2), false) ∈ cube 2 n := by
        simp only [cube, Set.mem_setOf_eq, Fin.forall_fin_two]
        exact ⟨⟨by rw [hy0]; omega, by rw [hy0]; omega⟩,
          ⟨by rw [hy1]; exact h1, by rw [hy1]; exact h1n⟩⟩
      have hz : x + xsch_dir ((1 : Fin 2), true) ∈ cube 2 n := by
        simp only [cube, Set.mem_setOf_eq, Fin.forall_fin_two]
        exact ⟨⟨by rw [hz0]; exact h0, by rw [hz0]; exact h0n⟩,
          ⟨by rw [hz1]; omega, by rw [hz1]; omega⟩⟩
      have hdy : (x + xsch_dir ((0 : Fin 2), false)) 0
          - (x + xsch_dir ((0 : Fin 2), false)) 1 = (k : ℤ) := by
        rw [hy0, hy1]; omega
      have hdz : (x + xsch_dir ((1 : Fin 2), true)) 0
          - (x + xsch_dir ((1 : Fin 2), true)) 1 = (k : ℤ) := by
        rw [hz0, hz1]; omega
      refine xsch_Top.nbr {((0 : Fin 2), false), ((1 : Fin 2), true)} hx ?_ ?_ ?_
      · intro s hs
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs
        rcases hs with rfl | rfl <;> simp
      · simp
      · intro s hs
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs
        rcases hs with rfl | rfl
        · simpa using ih _ hy hdy
        · simpa using ih _ hz hdz
  have key2 : ∀ k : ℕ, ∀ x : Site 2, x ∈ cube 2 n → x 1 - x 0 = (k : ℤ) →
      xsch_Top (Finset.univ : Finset (Fin 2)) (cube 2 n) η x := by
    intro k
    induction k with
    | zero =>
      intro x hx h
      exact xsch_Top.occ hx (hdiag x hx (by omega))
    | succ k ih =>
      intro x hx h
      have h0 : 1 ≤ x 0 := (hx 0).1
      have h1 : 1 ≤ x 1 := (hx 1).1
      have h0n : x 0 ≤ (n : ℤ) := (hx 0).2
      have h1n : x 1 ≤ (n : ℤ) := (hx 1).2
      have hx1ge2 : 2 ≤ x 1 := by omega
      have hy0 : (x + xsch_dir ((0 : Fin 2), true)) 0 = x 0 + 1 := by simp [xsch_dir, unit]
      have hy1 : (x + xsch_dir ((0 : Fin 2), true)) 1 = x 1 := by simp [xsch_dir, unit]
      have hz0 : (x + xsch_dir ((1 : Fin 2), false)) 0 = x 0 := by simp [xsch_dir, unit]
      have hz1 : (x + xsch_dir ((1 : Fin 2), false)) 1 = x 1 - 1 := by simp [xsch_dir, unit, sub_eq_add_neg]
      have hy : x + xsch_dir ((0 : Fin 2), true) ∈ cube 2 n := by
        simp only [cube, Set.mem_setOf_eq, Fin.forall_fin_two]
        exact ⟨⟨by rw [hy0]; omega, by rw [hy0]; omega⟩,
          ⟨by rw [hy1]; exact h1, by rw [hy1]; exact h1n⟩⟩
      have hz : x + xsch_dir ((1 : Fin 2), false) ∈ cube 2 n := by
        simp only [cube, Set.mem_setOf_eq, Fin.forall_fin_two]
        exact ⟨⟨by rw [hz0]; exact h0, by rw [hz0]; exact h0n⟩,
          ⟨by rw [hz1]; omega, by rw [hz1]; omega⟩⟩
      have hdy : (x + xsch_dir ((0 : Fin 2), true)) 1
          - (x + xsch_dir ((0 : Fin 2), true)) 0 = (k : ℤ) := by
        rw [hy0, hy1]; omega
      have hdz : (x + xsch_dir ((1 : Fin 2), false)) 1
          - (x + xsch_dir ((1 : Fin 2), false)) 0 = (k : ℤ) := by
        rw [hz0, hz1]; omega
      refine xsch_Top.nbr {((0 : Fin 2), true), ((1 : Fin 2), false)} hx ?_ ?_ ?_
      · intro s hs
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs
        rcases hs with rfl | rfl <;> simp
      · simp
      · intro s hs
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs
        rcases hs with rfl | rfl
        · simpa using ih _ hy hdy
        · simpa using ih _ hz hdz
  intro x hx
  rcases le_total (x 0) (x 1) with hle | hle
  · exact key2 ((x 1 - x 0).toNat) x hx (by omega)
  · exact key1 ((x 0 - x 1).toNat) x hx (by omega)

end Exploding
