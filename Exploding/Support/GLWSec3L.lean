/-
Proposition 5.1 of the paper (generalized last wave): a long row of macroscopic sites meets `C_∞`,
and a rectangle with a long side contains a line of a tile of `C_∞`.
-/
import Exploding.Support.GLWSec3K

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

/-! ### A row of macroscopic sites meets `C_∞` -/

theorem glws_component_step {S : Set (Site d)} {x y y' : Site d} (hy : y ∈ componentIn S x)
    (hy' : y' ∈ S) (hadj : (lattice d).Adj y y') : y' ∈ componentIn S x := by
  obtain ⟨hx, hyS, hreach⟩ := hy
  refine ⟨hx, hy', hreach.trans ?_⟩
  exact SimpleGraph.Adj.reachable (by simpa [SimpleGraph.induce_adj] using hadj)

theorem glws_row_adj (μ : Site d) (l : Fin d) (t : ℕ) :
    (lattice d).Adj (μ + (t : ℤ) • unit l) (μ + ((t + 1 : ℕ) : ℤ) • unit l) := by
  refine ⟨l, Or.inl ?_⟩
  push_cast
  rw [add_smul, one_smul]
  abel

theorem glws_row_injective (μ : Site d) (l : Fin d) :
    Function.Injective (fun t : ℕ => μ + (t : ℤ) • unit l) := by
  intro t t' h
  have := congrFun h l
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, glws_unit_apply, if_true, mul_one,
    add_right_inj] at this
  exact_mod_cast this

/-- **A row of more than `(log n)^{5/2}` consecutive macroscopic sites meets `C_∞`**: otherwise
it lies in one component of the complement, which is smaller. -/
theorem glws_row_hole (Cinf : Set (Site d)) (n : ℕ)
    (hole : ∀ x ∈ (cent d n : Set (Site d)), x ∉ Cinf → (componentIn Cinfᶜ x).Finite ∧
      ((componentIn Cinfᶜ x).ncard : ℝ) < Real.log n ^ ((5 : ℝ) / 2))
    (l : Fin d) (μ : Site d) (r : ℕ) (hr : Real.log n ^ ((5 : ℝ) / 2) ≤ r)
    (hrow : ∀ t : ℕ, t ≤ r → μ + (t : ℤ) • unit l ∈ cent d n) :
    ∃ t : ℕ, t ≤ r ∧ μ + (t : ℤ) • unit l ∈ Cinf := by
  by_contra hcon
  push Not at hcon
  have hμ : μ ∈ (cent d n : Set (Site d)) := by simpa using hrow 0 (Nat.zero_le r)
  have hμC : μ ∉ Cinf := by simpa using hcon 0 (Nat.zero_le r)
  obtain ⟨hfin, hcard⟩ := hole μ hμ hμC
  have hcomp : ∀ t : ℕ, t ≤ r → μ + (t : ℤ) • unit l ∈ componentIn Cinfᶜ μ := by
    intro t
    induction t with
    | zero =>
      intro _
      have : μ + ((0 : ℕ) : ℤ) • unit l = μ := by simp
      rw [this]
      exact ⟨hμC, hμC, SimpleGraph.Reachable.refl _⟩
    | succ t ih =>
      intro ht
      exact glws_component_step (ih (by omega)) (hcon (t + 1) ht) (glws_row_adj μ l t)
  set F : Finset (Site d) := (Finset.range (r + 1)).image (fun t : ℕ => μ + (t : ℤ) • unit l)
    with hF
  have hFcard : F.card = r + 1 := by
    rw [hF, Finset.card_image_of_injective _ (glws_row_injective μ l)]
    simp
  have hFsub : (F : Set (Site d)) ⊆ componentIn Cinfᶜ μ := by
    intro y hy
    simp only [hF, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    exact hcomp t (by omega)
  have hle : F.card ≤ (componentIn Cinfᶜ μ).ncard := by
    have := Set.ncard_le_ncard hFsub hfin
    rwa [Set.ncard_coe_finset] at this
  have h1 : ((r + 1 : ℕ) : ℝ) ≤ ((componentIn Cinfᶜ μ).ncard : ℝ) := by
    rw [← hFcard]; exact_mod_cast hle
  push_cast at h1
  linarith

/-! ### A rectangle with a long side contains a line of a tile -/

theorem glws_floor_div (a : ℤ) (k : ℕ) (hk : 0 < k) :
    (k : ℤ) * (a / (k : ℤ)) ≤ a ∧ a < (k : ℤ) * (a / (k : ℤ)) + k := by
  have hk0 : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  have h1 := Int.emod_add_mul_ediv a (k : ℤ)
  have h2 := Int.emod_nonneg a (ne_of_gt hk0)
  have h3 := Int.emod_lt_of_pos a hk0
  constructor <;> nlinarith

/-- The macroscopic row attached to a rectangle `∏ [lo_m, hi_m]` whose `l`-side is long: for each
position `t ≤ r` of the row the tile has its `l`-extent inside the rectangle and a line across it,
through the point `lo` in the other coordinates, lies in the rectangle.  The row stays in the box
of radius `n + 1` when the rectangle lies in the box of radius `n`. -/
theorem glws_row_geom (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (l : Fin d) (lo hi : Site d)
    (hbox : ∀ m, lo m ≤ hi m) (n : ℕ) (hlo : ∀ m, |lo m| ≤ n) (hhi : ∀ m, |hi m| ≤ n) (r : ℕ)
    (hlen : (k l : ℤ) * ((r : ℤ) + 2) ≤ hi l - lo l + 1) :
    ∃ μ : Site d, (∀ t : ℕ, t ≤ r → μ + (t : ℤ) • unit l ∈ cent d (n + 1)) ∧
      ∀ t : ℕ, t ≤ r → ∃ z : Site d,
        z ∈ closureN (rboxShift k (μ + (t : ℤ) • unit l)) ∧
        (∀ w ∈ rline k (μ + (t : ℤ) • unit l) l z, ∀ m, lo m ≤ w m ∧ w m ≤ hi m) ∧
        ∀ y ∈ rboxShift k (μ + (t : ℤ) • unit l), (lo l ≤ y l ∧ y l ≤ hi l) ∧
          ∀ m, m ≠ l → lo m - (k m : ℤ) + 1 ≤ y m ∧ y m ≤ lo m + (k m : ℤ) - 1 := by
  set μ : Site d := fun m => if m = l then (lo l - 1 + (k l : ℤ) - 1) / (k l : ℤ)
    else (lo m - 1) / (k m : ℤ) with hμ
  have hk1 : ∀ m, (1 : ℤ) ≤ (k m : ℤ) := fun m => by exact_mod_cast hk m
  have hμl : μ l = (lo l - 1 + (k l : ℤ) - 1) / (k l : ℤ) := by simp [hμ]
  have hμm : ∀ m, m ≠ l → μ m = (lo m - 1) / (k m : ℤ) := by
    intro m hm; simp [hμ, hm]
  obtain ⟨hf1, hf2⟩ := glws_floor_div (lo l - 1 + (k l : ℤ) - 1) (k l) (hk l)
  rw [← hμl] at hf1 hf2
  have key : ∀ t : ℕ, t ≤ r → (μ + (t : ℤ) • unit l ∈ cent d (n + 1)) ∧ ∃ z : Site d,
      z ∈ closureN (rboxShift k (μ + (t : ℤ) • unit l)) ∧
      (∀ w ∈ rline k (μ + (t : ℤ) • unit l) l z, ∀ m, lo m ≤ w m ∧ w m ≤ hi m) ∧
      ∀ y ∈ rboxShift k (μ + (t : ℤ) • unit l), (lo l ≤ y l ∧ y l ≤ hi l) ∧
        ∀ m, m ≠ l → lo m - (k m : ℤ) + 1 ≤ y m ∧ y m ≤ lo m + (k m : ℤ) - 1 := by
    intro t ht
    set j : Site d := μ + (t : ℤ) • unit l with hj
    have hjl : j l = μ l + (t : ℤ) := by simp [hj, glws_unit_apply]
    have hjm : ∀ m, m ≠ l → j m = μ m := by
      intro m hm
      simp [hj, glws_unit_apply, hm]
    have hrt : (t : ℤ) ≤ (r : ℤ) := by exact_mod_cast ht
    have hkl := hk1 l
    have hlow_l : lo l ≤ 1 + (k l : ℤ) * j l := by
      rw [hjl]
      have : (k l : ℤ) * (μ l + t) ≥ (k l : ℤ) * μ l := by nlinarith
      linarith
    have hhigh_l : (k l : ℤ) * j l + k l ≤ hi l := by
      rw [hjl]
      have : (k l : ℤ) * (μ l + t) ≤ (k l : ℤ) * μ l + (k l : ℤ) * r := by nlinarith
      nlinarith
    refine ⟨?_, fun m => if m = l then 1 + (k l : ℤ) * j l else lo m, ?_, ?_, ?_⟩
    · intro m
      by_cases hm : m = l
      · subst hm
        have h1 := hlo m
        have h2 := hhi m
        rw [abs_le] at h1 h2 ⊢
        have hjpos : (j m) ≤ (k m : ℤ) * j m ∨ (k m : ℤ) * j m ≤ j m := by
          rcases le_total 0 (j m) with h | h
          · left; nlinarith
          · right; nlinarith
        have hjm0 : (j m : ℤ) = j m := rfl
        show -((n + 1 : ℕ) : ℤ) ≤ j m ∧ j m ≤ ((n + 1 : ℕ) : ℤ)
        push_cast
        rcases hjpos with h | h <;> constructor <;> nlinarith
      · have := pclose_ediv_abs (lo m) (k m) (hk m)
        have h3 : |j m| ≤ |lo m| + 1 := by rw [hjm m hm, hμm m hm]; exact this
        have h4 := hlo m
        show |j m| ≤ ((n + 1 : ℕ) : ℤ)
        push_cast
        linarith
    · left
      intro m
      by_cases hm : m = l
      · subst hm
        simp only [if_true]
        constructor <;> linarith
      · simp only [hm, if_false]
        obtain ⟨g1, g2⟩ := glws_floor_div (lo m - 1) (k m) (hk m)
        rw [← hμm m hm] at g1 g2
        rw [hjm m hm]
        constructor <;> linarith
    · intro w hw m
      by_cases hm : m = l
      · subst hm
        have := hw.1
        constructor <;> linarith [this.1, this.2]
      · have := hw.2 m hm
        simp only [hm, if_false] at this
        rw [this]
        exact ⟨le_rfl, hbox m⟩
    · intro y hy
      refine ⟨?_, fun m hm => ?_⟩
      · have := hy l
        constructor <;> linarith [this.1, this.2]
      · have := hy m
        obtain ⟨g1, g2⟩ := glws_floor_div (lo m - 1) (k m) (hk m)
        rw [← hμm m hm] at g1 g2
        rw [hjm m hm] at this
        have hkm := hk1 m
        constructor <;> linarith [this.1, this.2]
  exact ⟨μ, fun t ht => (key t ht).1, fun t ht => (key t ht).2⟩

end Exploding
