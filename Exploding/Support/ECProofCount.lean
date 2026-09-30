/-
The combinatorics of the Peierls estimate of Proposition 7.1: `*`-paths of the square
lattice are few, and a finite set of lattice points contains a proportional subset of
pairwise far-apart points.
-/
import Exploding.Support.ECProofStar

namespace Exploding

/-- Two planar points are more than `K` apart in some coordinate. -/
def ec_far (K : ℕ) (s t : ℤ × ℤ) : Prop := (K : ℤ) < |s.1 - t.1| ∨ (K : ℤ) < |s.2 - t.2|

theorem ec_far_symm {K : ℕ} {s t : ℤ × ℤ} (h : ec_far K s t) : ec_far K t s := by
  unfold ec_far at *
  rwa [abs_sub_comm t.1, abs_sub_comm t.2]

theorem ec_far_irrefl (K : ℕ) (s : ℤ × ℤ) : ¬ ec_far K s s := by
  unfold ec_far
  simp

/-- **A far-apart subset of proportional size.** -/
theorem ec_greedy (K : ℕ) : ∀ S : Finset (ℤ × ℤ), ∃ T ⊆ S,
    (∀ s ∈ T, ∀ t ∈ T, s ≠ t → ec_far K s t) ∧ S.card ≤ (2 * K + 1) ^ 2 * T.card := by
  classical
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hS : S = ∅
    · subst hS
      exact ⟨∅, by simp, by simp, by simp⟩
    · obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.2 hS
      set S' : Finset (ℤ × ℤ) := S.filter (fun t => ec_far K s t) with hS'
      have hS'sub : S' ⊂ S := by
        refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, ?_⟩
        intro h
        have : s ∈ S' := by rw [h]; exact hs
        exact ec_far_irrefl K s (Finset.mem_filter.1 this).2
      obtain ⟨T', hT'S, hT'far, hT'card⟩ := ih S' hS'sub
      have hsT' : s ∉ T' := by
        intro h
        exact ec_far_irrefl K s (Finset.mem_filter.1 (hT'S h)).2
      refine ⟨insert s T', ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hs
        · exact (Finset.mem_filter.1 (hT'S hx)).1
      · intro a ha b hb hab
        rcases Finset.mem_insert.1 ha with ha' | ha' <;> rcases Finset.mem_insert.1 hb with hb' | hb'
        · exact absurd (ha'.trans hb'.symm) hab
        · rw [ha']; exact (Finset.mem_filter.1 (hT'S hb')).2
        · rw [hb']; exact ec_far_symm (Finset.mem_filter.1 (hT'S ha')).2
        · exact hT'far a ha' b hb' hab
      · have hN : (S.filter (fun t => ¬ ec_far K s t)).card ≤ (2 * K + 1) ^ 2 := by
          have hsub : S.filter (fun t => ¬ ec_far K s t) ⊆
              (Finset.Icc (s.1 - K) (s.1 + K)) ×ˢ (Finset.Icc (s.2 - K) (s.2 + K)) := by
            intro t ht
            have h := (Finset.mem_filter.1 ht).2
            unfold ec_far at h
            push Not at h
            simp only [abs_le] at h
            simp only [Finset.mem_product, Finset.mem_Icc]
            omega
          refine (Finset.card_le_card hsub).trans ?_
          rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
          have : (s.1 + K + 1 - (s.1 - K)).toNat = 2 * K + 1 := by omega
          have h2 : (s.2 + K + 1 - (s.2 - K)).toNat = 2 * K + 1 := by omega
          rw [this, h2]; exact le_of_eq (by ring)
        have hsplit : S.card = S'.card + (S.filter (fun t => ¬ ec_far K s t)).card := by
          rw [hS']
          exact (Finset.card_filter_add_card_filter_not (s := S) (fun t => ec_far K s t)).symm
        rw [Finset.card_insert_of_notMem hsT', hsplit]
        calc S'.card + (S.filter (fun t => ¬ ec_far K s t)).card
            ≤ (2 * K + 1) ^ 2 * T'.card + (2 * K + 1) ^ 2 := add_le_add hT'card hN
          _ = (2 * K + 1) ^ 2 * (T'.card + 1) := by ring

/-! ### Counting `*`-paths -/

/-- The eight king moves. -/
def ec_kingOffsets : Finset (ℤ × ℤ) :=
  {(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (1, -1), (-1, 1), (-1, -1)}

/-- The lists of `m + 1` points starting at `p`, each a king move from the previous one. -/
def ec_paths : ℕ → ℤ × ℤ → Finset (List (ℤ × ℤ))
  | 0, p => {[p]}
  | m + 1, p => (ec_kingOffsets.image (fun o => p + o)).biUnion
      (fun q => (ec_paths m q).image (List.cons p))

theorem ec_paths_card : ∀ (m : ℕ) (p : ℤ × ℤ), (ec_paths m p).card ≤ 8 ^ m := by
  classical
  intro m
  induction m with
  | zero => intro p; simp [ec_paths]
  | succ m ih =>
    intro p
    rw [ec_paths]
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ q ∈ ec_kingOffsets.image (fun o => p + o), ((ec_paths m q).image (List.cons p)).card
        ≤ ∑ q ∈ ec_kingOffsets.image (fun o => p + o), 8 ^ m :=
          Finset.sum_le_sum (fun q _ => Finset.card_image_le.trans (ih q))
      _ = (ec_kingOffsets.image (fun o => p + o)).card * 8 ^ m := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 8 * 8 ^ m := by
          refine Nat.mul_le_mul_right _ ?_
          refine Finset.card_image_le.trans ?_
          decide
      _ = 8 ^ (m + 1) := by ring

theorem ec_mem_paths : ∀ (m : ℕ) (p : ℤ × ℤ) (l : List (ℤ × ℤ)), l.length = m + 1 →
    l.head? = some p → List.IsChain ec_adj8 l → l ∈ ec_paths m p := by
  classical
  intro m
  induction m with
  | zero =>
    intro p l hl hh _
    match l, hl, hh with
    | [a], _, hh => simp at hh; simp [ec_paths, hh]
  | succ m ih =>
    intro p l hl hh hc
    match l, hl, hh, hc with
    | a :: b :: rest, hl, hh, hc =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      rw [List.isChain_cons_cons] at hc
      obtain ⟨hab, hc'⟩ := hc
      rw [ec_paths, Finset.mem_biUnion]
      refine ⟨b, ?_, ?_⟩
      · rw [Finset.mem_image]
        refine ⟨b - a, ?_, by abel⟩
        obtain ⟨hne, h1, h2⟩ := hab
        simp only [abs_le] at h1 h2
        simp only [ec_kingOffsets, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff,
          Prod.fst_sub, Prod.snd_sub]
        have hne' : ¬ (a.1 = b.1 ∧ a.2 = b.2) := fun h => hne (Prod.ext h.1 h.2)
        omega
      · rw [Finset.mem_image]
        refine ⟨b :: rest, ih b _ (by simpa using hl) rfl hc', rfl⟩

theorem ec_paths_length : ∀ (m : ℕ) (p : ℤ × ℤ) (l : List (ℤ × ℤ)),
    l ∈ ec_paths m p → l.length = m + 1 := by
  classical
  intro m
  induction m with
  | zero => intro p l hl; simp [ec_paths] at hl; simp [hl]
  | succ m ih =>
    intro p l hl
    rw [ec_paths, Finset.mem_biUnion] at hl
    obtain ⟨q, _, hq⟩ := hl
    rw [Finset.mem_image] at hq
    obtain ⟨l', hl', rfl⟩ := hq
    simp [ih q l' hl']

end Exploding
