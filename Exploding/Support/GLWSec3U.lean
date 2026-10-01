/-
Proposition 5.1 of the paper (generalized last wave): the last wave lights a tile of `C_∞`.

A wave that does not stabilize has unbounded support, so it contains a site far from its centre,
joined to the centre by a path of distinct lit sites; the part of the path up to its first exit
from a box is a long lit path, and a long lit path lights a tile of `C_∞` near it
(`glws_path_to_tile`).
-/
import Exploding.Support.GLWSec3T
import Exploding.Support.ASProof4

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

/-- **A wave that does not stabilize has unbounded support.** -/
theorem glws_unbounded_of_not_stab (hd : 2 ≤ d) (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (N : ℕ) (zc : Site d)
    (hns : ¬ WaveStabilizable η N zc) (R : ℕ) :
    ∃ (t : ℕ) (y' : Site d), 0 < wave η N zc t y' ∧ ∃ l : Fin d, (R : ℤ) ≤ |y' l - zc l| := by
  classical
  by_contra hcon
  push Not at hcon
  apply hns
  have hd0 : (0 : ℤ) < 2 * (d : ℤ) := by
    have : (2 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    linarith
  set B : Set (Site d) := {y | ∀ l : Fin d, |y l - zc l| < (R : ℤ)} with hB
  have hBfin : B.Finite := by
    refine as_coord_bdd_finite zc (R : ℝ) B ?_
    intro y hy l
    have := hy l
    exact_mod_cast this.le
  have hstab : ∀ y : Site d, ∃ Ty : ℕ, ∀ t : ℕ, Ty ≤ t → wave η N zc t y = wave η N zc Ty y := by
    intro y
    by_cases hy : y ∈ B
    · exact as4_mono_bdd_eventually_constant (fun t => wave η N zc t y)
        (fun s t hst => wave_mono_time η hlow hd0 N zc hst y)
        ⟨(N : ℤ), fun t => wave_le_n η hhigh hd0 N zc t y⟩
    · have hzero : ∀ t : ℕ, wave η N zc t y = 0 := by
        intro t
        have h1 := wave_nonneg η hlow N zc t y
        by_contra hne
        have hpos : 0 < wave η N zc t y := lt_of_le_of_ne h1 (Ne.symm hne)
        apply hy
        intro l
        have := hcon t y hpos l
        exact this
      exact ⟨0, fun t _ => by rw [hzero t, hzero 0]⟩
  choose Ty hTy using hstab
  refine ⟨hBfin.toFinset.sup Ty, fun t ht => ?_⟩
  funext y
  by_cases hy : y ∈ B
  · have h1 : Ty y ≤ t := le_trans (Finset.le_sup (f := Ty) (hBfin.mem_toFinset.mpr hy)) ht
    have h2 : Ty y ≤ hBfin.toFinset.sup Ty := Finset.le_sup (f := Ty) (hBfin.mem_toFinset.mpr hy)
    rw [hTy y t h1, hTy y _ h2]
  · have hzero : ∀ s : ℕ, wave η N zc s y = 0 := by
      intro s
      have h1 := wave_nonneg η hlow N zc s y
      by_contra hne
      have hpos : 0 < wave η N zc s y := lt_of_le_of_ne h1 (Ne.symm hne)
      apply hy
      intro l
      exact hcon s y hpos l
    rw [hzero t, hzero _]

/-- **The exit path.**  If the `N`-wave is positive at a site at `ℓ^∞`-distance at least `D` from its
centre, there is a path of distinct lit sites from the centre, of at least `D` steps, staying within
distance `D` of the centre. -/
theorem glws_exit_path (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (hd0 : (0 : ℤ) < 2 * (d : ℤ)) (N : ℕ) (zc : Site d)
    (t : ℕ) (y' : Site d) (D : ℕ) (hD1 : 1 ≤ D) (hy' : 0 < wave η N zc t y')
    (hdev : ∃ l : Fin d, (D : ℤ) ≤ |y' l - zc l|) :
    ∃ (p : ℕ) (z : ℕ → Site d), z 0 = zc ∧ D ≤ p ∧ (∀ i, i ≤ p → 0 < wave η N zc t (z i)) ∧
      (∀ i j, i ≤ p → j ≤ p → z i = z j → i = j) ∧
      (∀ i, i < p → (lattice d).Adj (z i) (z (i + 1))) ∧
      ∀ i, i ≤ p → ∀ m, |z i m - zc m| ≤ (D : ℤ) := by
  classical
  obtain ⟨l, hl⟩ := hdev
  obtain ⟨m, z, hz0, hzm, hadj, hinj, hposz⟩ := glws_path_extract η hlow hhigh hd0 N zc t y' hy'
  have hex : ∃ q : ℕ, ∃ l' : Fin d, (D : ℤ) ≤ |z q l' - zc l'| := ⟨m, l, by rw [hzm]; exact hl⟩
  set p : ℕ := Nat.find hex with hp
  have hp1 : ∃ l' : Fin d, (D : ℤ) ≤ |z p l' - zc l'| := Nat.find_spec hex
  have hpmin : ∀ q, q < p → ∀ l' : Fin d, |z q l' - zc l'| < (D : ℤ) := by
    intro q hq l'
    have := Nat.find_min hex hq
    push Not at this
    exact this l'
  have hpm : p ≤ m := Nat.find_min' hex ⟨l, by rw [hzm]; exact hl⟩
  have hp0 : p ≠ 0 := by
    intro h0
    obtain ⟨l', hl'⟩ := hp1
    rw [h0, hz0] at hl'
    simp at hl'
    omega
  obtain ⟨p', hp'⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  have hdev : ∀ q, q ≤ p → ∀ l' : Fin d, |z q l' - zc l'| ≤ (D : ℤ) := by
    intro q hq l'
    rcases Nat.lt_or_ge q p with hlt | hge
    · exact (hpmin q hlt l').le
    · have hqp : q = p := le_antisymm hq hge
      subst hqp
      have h1 := hpmin p' (by omega) l'
      have h2 := glws_adj_coord (hadj p' (by omega)) l'
      have h3 : |z (p' + 1) l' - zc l'| ≤ |z (p' + 1) l' - z p' l'| + |z p' l' - zc l'| := by
        have := abs_add_le (z (p' + 1) l' - z p' l') (z p' l' - zc l')
        simpa using this
      rw [hp']
      linarith
  obtain ⟨l₁, hl₁⟩ := hp1
  have hdev1 : |z p l₁ - zc l₁| = (D : ℤ) := le_antisymm (hdev p le_rfl l₁) hl₁
  have hpD : D ≤ p := by
    have h1 := glws_path_coord z hadj l₁ p hpm
    rw [hz0] at h1
    have : (D : ℤ) ≤ (p : ℤ) := by rw [← hdev1]; exact h1
    exact_mod_cast this
  exact ⟨p, z, hz0, hpD, fun i hi => hposz i (by omega),
    fun i j hi hj h => hinj i j (by omega) (by omega) h,
    fun i hi => hadj i (by omega), fun i hi m => hdev i hi m⟩

end Exploding
