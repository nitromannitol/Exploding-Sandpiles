/-
Compactness of the cylinder content.  On `ι → Bool` the measurable cylinders are
clopen, so a decreasing sequence of them with empty intersection is eventually
empty.  This is the continuity-at-empty step that makes the projective family
content sigma-subadditive, and hence gives the projective limit measure through
Carathéodory's extension theorem.
-/
import Exploding.Support.ExtLSSProofDom

open MeasureTheory Set Filter
open scoped Topology

namespace Exploding

/-- A decreasing sequence of measurable cylinders in `ι → Bool` with empty intersection is
eventually empty. -/
theorem xlss_antitone_cylinder_eventually_empty {ι : Type*} (A : ℕ → Set (ι → Bool))
    (hA : ∀ n, A n ∈ measurableCylinders (fun _ : ι => Bool)) (hanti : Antitone A)
    (hinter : (⋂ n, A n) = ∅) : ∃ N, A N = ∅ := by
  by_contra h
  push Not at h
  have hne : ∀ n, (A n).Nonempty := h
  have hclosed : ∀ n, IsClosed (A n) := by
    intro n
    obtain ⟨I, S, _, hEq⟩ := (mem_measurableCylinders (A n)).mp (hA n)
    rw [hEq]
    exact IsClosed.cylinder I (isClosed_discrete S)
  have htd : ∀ n, A (n + 1) ⊆ A n := fun n => hanti (Nat.le_succ n)
  have hcomp : IsCompact (A 0) := (hclosed 0).isCompact
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    A htd hne hcomp hclosed
  rw [hinter] at hx
  exact hx

/-- The projective family content is continuous at the empty set, by compactness. -/
theorem xlss_projectiveFamilyContent_tendsto_zero {ι : Type*}
    (P : ∀ J : Finset ι, Measure (J → Bool)) (hP : IsProjectiveMeasureFamily (α := fun _ : ι => Bool) P)
    [∀ J, IsFiniteMeasure (P J)] :
    ∀ ⦃s : ℕ → Set (ι → Bool)⦄,
      (∀ n, s n ∈ measurableCylinders (fun _ : ι => Bool)) → Antitone s →
      (⋂ n, s n) = ∅ → Tendsto (fun n => projectiveFamilyContent (α := fun _ : ι => Bool) hP (s n)) atTop (𝓝 0) := by
  intro s hs hanti hinter
  obtain ⟨N, hN⟩ := xlss_antitone_cylinder_eventually_empty s hs hanti hinter
  refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
  have hsub : s n ⊆ s N := hanti hn
  rw [hN] at hsub
  rw [Set.subset_empty_iff.mp hsub, projectiveFamilyContent_eq, projectiveFamilyFun_empty hP]

/-- The projective family content on `ι → Bool` is σ-subadditive. -/
theorem xlss_projectiveFamilyContent_isSigmaSubadditive {ι : Type*}
    (P : ∀ J : Finset ι, Measure (J → Bool)) (hP : IsProjectiveMeasureFamily (α := fun _ : ι => Bool) P)
    [∀ J, IsFiniteMeasure (P J)] :
    (projectiveFamilyContent (α := fun _ : ι => Bool) hP).IsSigmaSubadditive := by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
    (C := measurableCylinders (fun _ : ι => Bool)) isSetRing_measurableCylinders
    (m := projectiveFamilyContent (α := fun _ : ι => Bool) hP) fun f hf hf_Union hf' => ?_
  exact addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
    (projectiveFamilyContent (α := fun _ : ι => Bool) hP) (fun s _ => projectiveFamilyContent_ne_top hP)
    (fun s hs hanti hinter => xlss_projectiveFamilyContent_tendsto_zero P hP hs hanti hinter)
    hf hf_Union hf'

end Exploding
