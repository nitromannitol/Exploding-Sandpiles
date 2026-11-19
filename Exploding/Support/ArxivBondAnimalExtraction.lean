import Exploding.Support.ArxivBondMarkedAnimals

/-!
# Finite marked animals from connected sets

A connected set whose good sites lie in a finite set contains a finite connected
animal with many marked bad cubes. This converts the marked-animal count into a
probability bound for connected sets, whether finite or infinite.
-/

open LatticeProb MeasureTheory

namespace Exploding

variable {d : ℕ}

/-- Extract a rooted animal with `k` bad cubes from a sufficiently large connected
set whose good sites lie in `P`. -/
theorem exists_marked_animal_of_connected {ω : Site d × Fin d → Bool}
    {S : Set (Site d)} {p : Site d} (hconn : xmh_SConn S) (hp : p ∈ S)
    (P : Finset (Site d)) {m k : ℕ} (hm : 1 ≤ m)
    (hsize : P.card + k ≤ m) (hS : (m : ℕ∞) ≤ S.encard)
    (hbad : ∀ x ∈ S, x ∉ P → ¬ xap_Good ω x) :
    ∃ F B : Finset (Site d), p ∈ F ∧ F.card = m ∧
      xmh_SConn (F : Set (Site d)) ∧ B ⊆ F ∧ B.card = k ∧
      ∀ x ∈ B, ¬ xap_Good ω x := by
  classical
  obtain ⟨F, hpF, hFS, hFm, hFconn⟩ := xmh_grow hconn hp m hm hS
  have hcard : k ≤ (F \ P).card := by
    have h := Finset.card_le_card_sdiff_add_card (s := F) (t := P)
    omega
  obtain ⟨B, hB, hBk⟩ := Finset.exists_subset_card_eq hcard
  refine ⟨F, B, hpF, hFm, hFconn, ?_, hBk, ?_⟩
  · exact hB.trans Finset.sdiff_subset
  · intro x hx
    have hx' := Finset.mem_sdiff.mp (hB hx)
    exact hbad x (hFS hx'.1) hx'.2

/-- The marked-animal estimate bounds the event that a connected set with at
most `P.card` good sites has size at least `m`. -/
theorem bond_connected_bad_cubes_prob_le (d : ℕ) :
    ∃ K : ℕ, ∀ (p : Site d) (P : Finset (Site d)) (m k : ℕ),
      1 ≤ m → P.card + k ≤ m → ∀ {q : ℝ}, 0 ≤ q → q ≤ 1 →
      bondPercolation d q
        {ω | ∃ S : Set (Site d), xmh_SConn S ∧ p ∈ S ∧ (m : ℕ∞) ≤ S.encard ∧
          ∀ x ∈ S, x ∉ P → ¬ xap_Good ω x} ≤
        ((K : ENNReal) ^ m * (2 : ENNReal) ^ m) *
          (1 - xap6_delta d q) ^ (k / 3 ^ d) := by
  obtain ⟨K, hK⟩ := arxiv_bond_marked_star_animal_prob_le d
  refine ⟨K, fun p P m k hm hsize q hq0 hq1 => ?_⟩
  refine (measure_mono ?_).trans (hK p m k hq0 hq1)
  rintro ω ⟨S, hconn, hp, hS, hbad⟩
  exact exists_marked_animal_of_connected hconn hp P hm hsize hS hbad

end Exploding
