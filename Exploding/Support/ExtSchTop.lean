/-
The toppling closure of threshold bootstrap percolation along a set of directions,
and its elementary properties: monotonicity in the frozen set, dependence on the
background only inside the frozen set, the growth of a toppled region by one
adjacent layer, and the comparison with the parallel odometer `spanOdo`.

For a set of directions `J`, a site of `B` topples when its background value is `2d`,
or when at least `|J|` of its `2|J|` neighbours along the directions of `J` have
toppled.  For `J` the set of all `d` directions this is bootstrap percolation with
threshold `d` on `ℤ^d`.  For `J = J'.insert i` the toppling of a site next to a
toppled region in direction `i` is the `J'`-dynamics.
-/
import Exploding.Support.Vocab

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The displacement of a step `(i, b)`: `+e_i` if `b`, `-e_i` otherwise. -/
def xsch_dir (s : Fin d × Bool) : Site d := if s.2 then unit s.1 else -unit s.1

/-- The toppling closure inside the frozen set `B` along the directions `J`: a site of `B`
topples when its background is `2d`, or when `|J|` of its neighbours along `J` have
toppled. -/
inductive xsch_Top (J : Finset (Fin d)) (B : Set (Site d)) (η : Site d → ℤ) : Site d → Prop
  | occ {x : Site d} : x ∈ B → η x = 2 * (d : ℤ) → xsch_Top J B η x
  | nbr {x : Site d} (S : Finset (Fin d × Bool)) : x ∈ B → (∀ s ∈ S, s.1 ∈ J) →
      J.card ≤ S.card → (∀ s ∈ S, xsch_Top J B η (x + xsch_dir s)) → xsch_Top J B η x

/-- `R` is internally spanned along `J`: every site of `R` topples inside `R`. -/
def xsch_Sp (J : Finset (Fin d)) (R : Set (Site d)) (η : Site d → ℤ) : Prop :=
  ∀ x ∈ R, xsch_Top J R η x

theorem xsch_Top.mem {J : Finset (Fin d)} {B : Set (Site d)} {η : Site d → ℤ} {x : Site d}
    (h : xsch_Top J B η x) : x ∈ B := by
  cases h with
  | occ hx _ => exact hx
  | nbr S hx _ _ _ => exact hx

/-- Toppling is monotone in the frozen set. -/
theorem xsch_Top_mono {J : Finset (Fin d)} {B B' : Set (Site d)} (hB : B ⊆ B')
    {η : Site d → ℤ} {x : Site d} (h : xsch_Top J B η x) : xsch_Top J B' η x := by
  induction h with
  | occ hx h2 => exact xsch_Top.occ (hB hx) h2
  | nbr S hx hSJ hcard _ ih => exact xsch_Top.nbr S (hB hx) hSJ hcard ih

/-- Toppling inside `B` only reads the background on `B`. -/
theorem xsch_Top_congr {J : Finset (Fin d)} {B : Set (Site d)} {η η' : Site d → ℤ}
    (hη : ∀ y ∈ B, η y = η' y) {x : Site d} (h : xsch_Top J B η x) : xsch_Top J B η' x := by
  induction h with
  | occ hx h2 => exact xsch_Top.occ hx (by rw [← hη _ hx]; exact h2)
  | nbr S hx hSJ hcard _ ih => exact xsch_Top.nbr S hx hSJ hcard ih

theorem xsch_Sp_congr {J : Finset (Fin d)} {R : Set (Site d)} {η η' : Site d → ℤ}
    (hη : ∀ y ∈ R, η y = η' y) (h : xsch_Sp J R η) : xsch_Sp J R η' :=
  fun x hx => xsch_Top_congr hη (h x hx)

/-- A spanned set is toppled inside any larger frozen set. -/
theorem xsch_Sp_mono {J : Finset (Fin d)} {R B : Set (Site d)} (hRB : R ⊆ B)
    {η : Site d → ℤ} (h : xsch_Sp J R η) {x : Site d} (hx : x ∈ R) : xsch_Top J B η x :=
  xsch_Top_mono hRB (h x hx)

/-- A fully occupied set is spanned. -/
theorem xsch_Sp_of_occ {J : Finset (Fin d)} {R : Set (Site d)} {η : Site d → ℤ}
    (h : ∀ x ∈ R, η x = 2 * (d : ℤ)) : xsch_Sp J R η :=
  fun x hx => xsch_Top.occ hx (h x hx)

/-- With no directions every site of the frozen set topples. -/
theorem xsch_Sp_empty (R : Set (Site d)) (η : Site d → ℤ) : xsch_Sp (∅ : Finset (Fin d)) R η :=
  fun _ hx => xsch_Top.nbr ∅ hx (by simp) (by simp) (by simp)

/-- **Growth by one layer.**  If `T` is toppled inside `B`, and every site of the layer `L ⊆ B`
has a neighbour in `T` in direction `i ∈ J`, and `L` is spanned along `J.erase i`, then `L` is
toppled inside `B` along `J`. -/
theorem xsch_grow {J : Finset (Fin d)} {i : Fin d} (hi : i ∈ J) (b : Bool)
    {B T L : Set (Site d)} {η : Site d → ℤ}
    (hLB : L ⊆ B) (hT : ∀ x ∈ T, xsch_Top J B η x)
    (hnb : ∀ y ∈ L, y + xsch_dir (i, b) ∈ T)
    {y : Site d} (hy : xsch_Top (J.erase i) L η y) : xsch_Top J B η y := by
  induction hy with
  | occ hx h2 => exact xsch_Top.occ (hLB hx) h2
  | @nbr x S hx hSJ hcard _ ih =>
    have hnot : (i, b) ∉ S := by
      intro hmem
      have := hSJ _ hmem
      simp at this
    refine xsch_Top.nbr (insert (i, b) S) (hLB hx) ?_ ?_ ?_
    · intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact hi
      · exact Finset.mem_of_mem_erase (hSJ s hs)
    · rw [Finset.card_insert_of_notMem hnot]
      have := Finset.card_erase_add_one hi
      omega
    · intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact hT _ (hnb x hx)
      · exact ih s hs

theorem xsch_Sp_grow {J : Finset (Fin d)} {i : Fin d} (hi : i ∈ J) (b : Bool)
    {B T L : Set (Site d)} {η : Site d → ℤ}
    (hLB : L ⊆ B) (hT : ∀ x ∈ T, xsch_Top J B η x)
    (hnb : ∀ y ∈ L, y + xsch_dir (i, b) ∈ T)
    (hL : xsch_Sp (J.erase i) L η) : ∀ y ∈ L, xsch_Top J B η y :=
  fun _ hy => xsch_grow hi b hLB hT hnb (hL _ hy)

/-! ### Comparison with the parallel odometer -/

theorem xsch_nbrSumZ_eq (u : Site d → ℤ) (x : Site d) :
    nbrSumZ u x = ∑ s : Fin d × Bool, u (x + xsch_dir s) := by
  simp [nbrSumZ, Fintype.sum_prod_type, xsch_dir, sub_eq_add_neg,
    Finset.sum_add_distrib]

theorem xsch_spanOdo_off (n : ℕ) (η : Site d → ℤ) (t : ℕ) {x : Site d} (hx : x ∉ cube d n) :
    spanOdo n η t x = 0 := by
  cases t with
  | zero => rfl
  | succ t => simp only [spanOdo, if_pos hx]

theorem xsch_spanOdo_zero_one (n : ℕ) (η : Site d → ℤ) (t : ℕ) (x : Site d) :
    spanOdo n η t x = 0 ∨ spanOdo n η t x = 1 := by
  induction t generalizing x with
  | zero => left; rfl
  | succ t ih =>
    by_cases h1 : x ∈ cube d n
    · simp only [spanOdo, h1, not_true_eq_false, if_false]
      by_cases h2 : spanOdo n η t x = 1
      · rw [if_pos h2]; right; rfl
      · rw [if_neg h2]
        rcases ih x with h | h
        · rw [h]
          by_cases h3 : 2 * (d : ℤ) ≤ η x + lap (spanOdo n η t) x
          · right; rw [if_pos h3]; norm_num
          · left; rw [if_neg h3]; norm_num
        · exact absurd h h2
    · left; exact xsch_spanOdo_off n η _ h1

theorem xsch_spanOdo_mono_step (n : ℕ) (η : Site d → ℤ) (t : ℕ) (x : Site d)
    (h : spanOdo n η t x = 1) : spanOdo n η (t + 1) x = 1 := by
  by_cases hx : x ∈ cube d n
  · simp only [spanOdo, hx, not_true_eq_false, if_false, h, if_true]
  · exfalso
    rw [xsch_spanOdo_off n η t hx] at h
    exact zero_ne_one h

theorem xsch_spanOdo_mono (n : ℕ) (η : Site d → ℤ) {t t' : ℕ} (htt : t ≤ t') (x : Site d)
    (h : spanOdo n η t x = 1) : spanOdo n η t' x = 1 := by
  induction htt with
  | refl => exact h
  | step _ ih => exact xsch_spanOdo_mono_step n η _ x ih

/-- Toppling in the closure sense implies toppling by the parallel odometer, when the
background is at least `d` everywhere. -/
theorem xsch_exists_time (n : ℕ) (η : Site d → ℤ) (hη : ∀ x, (d : ℤ) ≤ η x) {x : Site d}
    (h : xsch_Top Finset.univ (cube d n) η x) : ∃ t : ℕ, spanOdo n η t x = 1 := by
  classical
  induction h with
  | @occ x hx h2 =>
    refine ⟨1, ?_⟩
    simp only [spanOdo]
    have hl : lap (fun _ : Site d => (0 : ℤ)) x = 0 := by simp [lap, nbrSumZ]
    simp [hx, h2, hl]
  | @nbr x S hx hSJ hcard _ ih =>
    choose! tt htt using ih
    set T := S.sup tt with hT
    have hT' : ∀ s ∈ S, spanOdo n η T (x + xsch_dir s) = 1 := fun s hs =>
      xsch_spanOdo_mono n η (Finset.le_sup (f := tt) hs) _ (htt s hs)
    refine ⟨T + 1, ?_⟩
    simp only [spanOdo]
    rw [if_neg (not_not.mpr hx)]
    by_cases h1 : spanOdo n η T x = 1
    · simp [h1]
    · rw [if_neg h1]
      have h0 : spanOdo n η T x = 0 := by
        rcases xsch_spanOdo_zero_one n η T x with h | h
        · exact h
        · exact absurd h h1
      have hlap : lap (spanOdo n η T) x = ∑ s : Fin d × Bool, spanOdo n η T (x + xsch_dir s) := by
        rw [lap, xsch_nbrSumZ_eq, h0]; ring
      have hsum : (S.card : ℤ) ≤ ∑ s : Fin d × Bool, spanOdo n η T (x + xsch_dir s) := by
        calc (S.card : ℤ) = ∑ s ∈ S, spanOdo n η T (x + xsch_dir s) := by
              rw [Finset.sum_congr rfl hT', Finset.sum_const]; simp
          _ ≤ ∑ s : Fin d × Bool, spanOdo n η T (x + xsch_dir s) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
              intro s _ _
              rcases xsch_spanOdo_zero_one n η T (x + xsch_dir s) with h | h <;> simp [h]
      have hcard' : (d : ℤ) ≤ (S.card : ℤ) := by
        have : (Finset.univ : Finset (Fin d)).card = d := by simp
        have h2 : (d : ℕ) ≤ S.card := by simpa using hcard
        exact_mod_cast h2
      have hge : 2 * (d : ℤ) ≤ η x + lap (spanOdo n η T) x := by
        have := hη x
        rw [hlap]
        omega
      rw [if_pos hge, h0]
      norm_num

/-- If every site of the cube topples in the closure sense, the cube is internally spanned,
for backgrounds that are at least `d` everywhere. -/
theorem xsch_internallySpanned (n : ℕ) (η : Site d → ℤ) (hη : ∀ x, (d : ℤ) ≤ η x)
    (h : xsch_Sp Finset.univ (cube d n) η) : InternallySpanned η n :=
  fun x hx => xsch_exists_time n η hη (h x hx)

end Exploding
