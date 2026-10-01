/-
The isoperimetric input for the hole-volume assembly: the inner boundary of a finite
set is at least its edge boundary divided by `2d`, and (Loomis–Whitney plus line
counting) the edge boundary grows like the `(d-1)/d` power of the volume.  Together
these give the lower bound on the inner boundary used in `xmh3_boundary_witness`.
-/
import Exploding.Support.ExtMHProof6
import Exploding.Support.ExtMHProof3

namespace Exploding

open LatticeProb MeasureTheory Filter
open scoped BigOperators

variable {d : ℕ}

/-- The number of lattice edges joining `z` to a site outside `B`. -/
def xmh4_degOut (B : Finset (Site d)) (z : Site d) : ℕ :=
  ((Finset.univ : Finset (Fin d)).filter (fun i => z + unit i ∉ B)).card
    + ((Finset.univ : Finset (Fin d)).filter (fun i => z - unit i ∉ B)).card

/-- The edge boundary of `B`: the number of lattice edges with exactly one endpoint in `B`. -/
def xmh4_edgeBoundary (B : Finset (Site d)) : ℕ := ∑ z ∈ B, xmh4_degOut B z

theorem xmh4_degOut_le (B : Finset (Site d)) (z : Site d) : xmh4_degOut B z ≤ 2 * d := by
  unfold xmh4_degOut
  have h1 : ((Finset.univ : Finset (Fin d)).filter (fun i => z + unit i ∉ B)).card ≤ d := by
    simpa using Finset.card_filter_le (Finset.univ : Finset (Fin d))
      (fun i => z + unit i ∉ B)
  have h2 : ((Finset.univ : Finset (Fin d)).filter (fun i => z - unit i ∉ B)).card ≤ d := by
    simpa using Finset.card_filter_le (Finset.univ : Finset (Fin d))
      (fun i => z - unit i ∉ B)
  omega

/-- The inner boundary of `B` consists exactly of the sites of `B` with a neighbour outside. -/
theorem xmh4_inner_eq_filter (B : Finset (Site d)) :
    innerBoundary (B : Set (Site d))
      = ((B.filter (fun z => 0 < xmh4_degOut B z)) : Set (Site d)) := by
  ext z
  constructor
  · rintro ⟨hzB, y, hyB, hyz⟩
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨hzB, ?_⟩
    obtain ⟨i, hi | hi⟩ := hyz
    · unfold xmh4_degOut
      have hpos : 0 < ((Finset.univ : Finset (Fin d)).filter
          (fun i => z + unit i ∉ B)).card := by
        rw [Finset.card_pos]
        refine ⟨i, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← hi]
        exact fun h => hyB (Finset.mem_coe.mpr h)
      omega
    · unfold xmh4_degOut
      have hz : z - unit i = y := by rw [hi]; abel
      have hpos : 0 < ((Finset.univ : Finset (Fin d)).filter
          (fun i => z - unit i ∉ B)).card := by
        rw [Finset.card_pos]
        refine ⟨i, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hz]
        exact fun h => hyB (Finset.mem_coe.mpr h)
      omega
  · rw [Finset.mem_coe, Finset.mem_filter]
    rintro ⟨hzB, hpos⟩
    refine ⟨hzB, ?_⟩
    unfold xmh4_degOut at hpos
    rcases Nat.eq_zero_or_pos ((Finset.univ : Finset (Fin d)).filter
        (fun i => z + unit i ∉ B)).card with ha | ha
    · have hb : 0 < ((Finset.univ : Finset (Fin d)).filter
          (fun i => z - unit i ∉ B)).card := by omega
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hb
      rw [Finset.mem_filter] at hi
      exact ⟨z - unit i, hi.2, ⟨i, Or.inr (by abel)⟩⟩
    · obtain ⟨i, hi⟩ := Finset.card_pos.mp ha
      rw [Finset.mem_filter] at hi
      exact ⟨z + unit i, hi.2, ⟨i, Or.inl rfl⟩⟩

/-- The edge boundary is at most `2d` times the inner boundary. -/
theorem xmh4_edgeBoundary_le_inner (B : Finset (Site d)) :
    xmh4_edgeBoundary B ≤ (innerBoundary (B : Set (Site d))).ncard * (2 * d) := by
  have hzero : ∀ z ∈ B, z ∉ B.filter (fun z => 0 < xmh4_degOut B z) → xmh4_degOut B z = 0 := by
    intro z hz hzf
    by_contra h
    exact hzf (Finset.mem_filter.mpr ⟨hz, Nat.pos_of_ne_zero h⟩)
  have hsum : xmh4_edgeBoundary B
      = ∑ z ∈ B.filter (fun z => 0 < xmh4_degOut B z), xmh4_degOut B z := by
    unfold xmh4_edgeBoundary
    exact (Finset.sum_subset (Finset.filter_subset _ _) hzero).symm
  rw [hsum, xmh4_inner_eq_filter B, Set.ncard_coe_finset]
  calc ∑ z ∈ B.filter (fun z => 0 < xmh4_degOut B z), xmh4_degOut B z
      ≤ ∑ _z ∈ B.filter (fun z => 0 < xmh4_degOut B z), 2 * d :=
        Finset.sum_le_sum fun z _ => xmh4_degOut_le B z
    _ = (B.filter (fun z => 0 < xmh4_degOut B z)).card * (2 * d) := by
        rw [Finset.sum_const, smul_eq_mul]

/-- **The edge-isoperimetric inequality on `ℤ^d`** (Loomis–Whitney together with line
counting): the edge boundary of a nonempty finite set grows at least as the `(d-1)/d`
power of the volume.  Stated as a hypothesis of the assembly. -/
def xmh4_edgeIso (d : ℕ) : Prop :=
  ∀ B : Finset (Site d), B.Nonempty →
    2 * (B.card : ℝ) ^ (((d : ℝ) - 1) / d) ≤ (xmh4_edgeBoundary B : ℝ)

/-- The inner boundary is at least a constant times the `(d-1)/d` power of the volume. -/
theorem xmh4_innerBoundary_iso {d : ℕ} (hd : 2 ≤ d) (h : xmh4_edgeIso d)
    (B : Finset (Site d)) (hB : B.Nonempty) :
    (B.card : ℝ) ^ (((d : ℝ) - 1) / d) / d
      ≤ (innerBoundary (B : Set (Site d))).ncard := by
  have hb := h B hB
  have hbnd : (xmh4_edgeBoundary B : ℝ)
      ≤ (innerBoundary (B : Set (Site d))).ncard * (2 * d) := by
    exact_mod_cast xmh4_edgeBoundary_le_inner B
  have hd0 : (0 : ℝ) < d := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    exact this
  have h2d : (0 : ℝ) < 2 * d := by positivity
  have hmain : 2 * (B.card : ℝ) ^ (((d : ℝ) - 1) / d) / (2 * d)
      ≤ (innerBoundary (B : Set (Site d))).ncard := by
    calc 2 * (B.card : ℝ) ^ (((d : ℝ) - 1) / d) / (2 * d)
        ≤ (xmh4_edgeBoundary B : ℝ) / (2 * d) :=
          div_le_div_of_nonneg_right hb h2d.le
      _ ≤ (innerBoundary (B : Set (Site d))).ncard := (div_le_iff₀ h2d).mpr hbnd
  have heq : 2 * (B.card : ℝ) ^ (((d : ℝ) - 1) / d) / (2 * d)
      = (B.card : ℝ) ^ (((d : ℝ) - 1) / d) / d :=
    mul_div_mul_left _ _ (by norm_num)
  rw [← heq]
  exact hmain

end Exploding
