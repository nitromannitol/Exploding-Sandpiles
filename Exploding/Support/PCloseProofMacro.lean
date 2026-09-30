/-
Macroscopic bookkeeping for the second inequality of Lemma 3.7: the macroscopic
index of a site, two far points of the infinite cluster on either side of a site,
and the concatenation of two walks issuing from a common cube.
-/
import Exploding.Support.Vocab
import Exploding.Support.SubPub
import Exploding.Support.PCloseProofGeom
import Exploding.Support.PCloseProofWalk

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The two-sided bounds on a site in terms of its macroscopic index. -/
theorem pclose_macro_bounds (k : ℕ) (hk : 1 ≤ k) (x : Site d) (l : Fin d) :
    (k : ℤ) * macroIdx k x l + 1 ≤ x l ∧ x l ≤ (k : ℤ) * macroIdx k x l + k := by
  have h := mem_cube_of_macroIdx k hk x l
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
  constructor <;> linarith [h.1, h.2]

/-- The macroscopic index is at most one larger in absolute value. -/
theorem pclose_macro_abs (k : ℕ) (hk : 1 ≤ k) (x : Site d) (l : Fin d) :
    |macroIdx k x l| ≤ |x l| + 1 := by
  obtain ⟨h1, h2⟩ := pclose_macro_bounds k hk x l
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
  set a := macroIdx k x l with ha
  rcases le_or_gt 0 a with h0 | h0
  · rw [abs_of_nonneg h0]
    have : a ≤ (k : ℤ) * a := by nlinarith
    have hx : a ≤ x l - 1 := by linarith
    have : x l ≤ |x l| := le_abs_self _
    linarith
  · rw [abs_of_neg h0]
    have h3 : (k : ℤ) * (a + 1) ≤ a + 1 := by nlinarith
    have h4 : x l ≤ a + 1 := by nlinarith
    have : -(x l) ≤ |x l| := neg_le_abs _
    linarith

/-- The Manhattan norm of the macroscopic index. -/
theorem pclose_mnorm_macro_le (k : ℕ) (hk : 1 ≤ k) (x : Site d) :
    mnorm (macroIdx k x) ≤ mnorm x + d := by
  unfold mnorm
  calc ∑ l, |macroIdx k x l| ≤ ∑ l : Fin d, (|x l| + 1) :=
        Finset.sum_le_sum fun l _ => pclose_macro_abs k hk x l
    _ = ∑ l, |x l| + d := by
        rw [Finset.sum_add_distrib]; simp

/-- If every coordinate of `M - mac` lies in `[lo, hi]`, then `M - mac` has norm at most
`d * max |lo| |hi|`; here stated for `|M l - mac l| ≤ r`. -/
theorem pclose_mnorm_le_of_coord (M mac : Site d) (r : ℤ) (h : ∀ l, |M l - mac l| ≤ r) :
    mnorm (M - mac) ≤ (d : ℤ) * r := by
  unfold mnorm
  calc ∑ l, |(M - mac) l| ≤ ∑ _l : Fin d, r := Finset.sum_le_sum fun l _ => h l
    _ = (d : ℤ) * r := by simp

/-- **Two far points of the infinite cluster.**  On each side of a macroscopic site `mac`,
the infinite cluster has a point whose coordinates all exceed those of `mac` by at least `ρ`
(resp. lie below by at least `ρ`), and by at most `ρ + Z`. -/
theorem pclose_two_ends (hd : 1 ≤ d) (Cinf : Set (Site d)) (Z n1 : ℕ)
    (hhole : ∀ y ∈ (cent d n1 : Set (Site d)), y ∉ Cinf →
      (componentIn Cinfᶜ y).Finite ∧ (componentIn Cinfᶜ y).ncard < Z)
    (mac : Site d) (ρ : ℕ) (hcent : ∀ l, |mac l| + ρ + Z ≤ (n1 : ℤ)) :
    (∃ M ∈ Cinf, ∀ l, (ρ : ℤ) ≤ M l - mac l ∧ M l - mac l ≤ ρ + Z) ∧
    (∃ M ∈ Cinf, ∀ l, -((ρ : ℤ) + Z) ≤ M l - mac l ∧ M l - mac l ≤ -(ρ : ℤ)) := by
  have e0 : Fin d := ⟨0, by omega⟩
  constructor
  · have hs : (fun l => mac l + ρ) ∈ (cent d n1 : Set (Site d)) := by
      intro l
      have := hcent l
      have h1 : |mac l + ρ| ≤ |mac l| + ρ := by
        calc |mac l + ρ| ≤ |mac l| + |(ρ : ℤ)| := abs_add_le _ _
          _ = |mac l| + ρ := by simp
      linarith [Int.natCast_nonneg Z]
    obtain ⟨r, hr, hmem⟩ := pclose_ray_hit Cinf Z n1 hhole _ hs e0
    refine ⟨_, hmem, fun l => ?_⟩
    have hcoord := coord_add_smul (fun l => mac l + ρ) (r : ℤ) e0 l
    rw [hcoord]
    have hr0 : (0 : ℤ) ≤ r := Int.natCast_nonneg r
    have hr1 : (r : ℤ) ≤ Z := by exact_mod_cast hr
    by_cases hl : l = e0
    · simp only [hl, if_true]
      constructor <;> linarith
    · simp only [hl, if_false]
      constructor <;> linarith
  · have hs : (fun l => mac l - ρ - (if l = e0 then (Z : ℤ) else 0)) ∈
        (cent d n1 : Set (Site d)) := by
      intro l
      have := hcent l
      have h1 : |mac l - ρ - (if l = e0 then (Z : ℤ) else 0)| ≤ |mac l| + ρ + Z := by
        by_cases hl : l = e0
        · subst hl
          simp only [if_true]
          rw [abs_le]
          constructor <;> cases abs_cases (mac l) <;> linarith [Int.natCast_nonneg Z, Int.natCast_nonneg ρ]
        · simp only [hl, if_false, sub_zero]
          rw [abs_le]
          constructor <;> cases abs_cases (mac l) <;> linarith [Int.natCast_nonneg Z, Int.natCast_nonneg ρ]
      linarith
    obtain ⟨r, hr, hmem⟩ := pclose_ray_hit Cinf Z n1 hhole _ hs e0
    refine ⟨_, hmem, fun l => ?_⟩
    have hcoord := coord_add_smul (fun l => mac l - ρ - (if l = e0 then (Z : ℤ) else 0))
      (r : ℤ) e0 l
    rw [hcoord]
    have hr0 : (0 : ℤ) ≤ r := Int.natCast_nonneg r
    have hr1 : (r : ℤ) ≤ Z := by exact_mod_cast hr
    by_cases hl : l = e0
    · simp only [hl, if_true]
      constructor <;> linarith
    · simp only [hl, if_false]
      constructor <;> linarith

/-- Two walks issuing from the same cube concatenate into a walk from the end of the
first to the end of the second, each of whose vertices lies on one of the two walks. -/
theorem pclose_concat_walk (m₁ m₂ : ℕ) (c₁ c₂ : ℕ → Site d)
    (h0 : c₁ 0 = c₂ 0)
    (hadj₁ : ∀ s, s < m₁ → (lattice d).Adj (c₁ s) (c₁ (s + 1)))
    (hadj₂ : ∀ s, s < m₂ → (lattice d).Adj (c₂ s) (c₂ (s + 1))) :
    ∃ c : ℕ → Site d, c 0 = c₁ m₁ ∧ c (m₁ + m₂) = c₂ m₂ ∧
      (∀ s, s < m₁ + m₂ → (lattice d).Adj (c s) (c (s + 1))) ∧
      ∀ s, s ≤ m₁ + m₂ → (∃ s', s' ≤ m₁ ∧ c s = c₁ s') ∨ (∃ s', s' ≤ m₂ ∧ c s = c₂ s') := by
  refine ⟨fun s => if s < m₁ then c₁ (m₁ - s) else c₂ (s - m₁), ?_, ?_, ?_, ?_⟩
  · by_cases hm : 0 < m₁
    · simp [hm]
    · have : m₁ = 0 := by omega
      subst this
      simp [h0]
  · have : ¬ (m₁ + m₂ < m₁) := by omega
    simp [this]
  · intro s hs
    by_cases h1 : s + 1 < m₁
    · have h2 : s < m₁ := by omega
      simp only [h1, h2, if_true]
      have := hadj₁ (m₁ - s - 1) (by omega)
      have e : m₁ - s - 1 + 1 = m₁ - s := by omega
      have e' : m₁ - (s + 1) = m₁ - s - 1 := by omega
      rw [e] at this
      rw [e']
      exact this.symm
    · by_cases h2 : s + 1 = m₁
      · have h3 : s < m₁ := by omega
        simp only [h1, h3, if_true, if_false]
        have e : m₁ - s = 1 := by omega
        have e' : s + 1 - m₁ = 0 := by omega
        rw [e, e', ← h0]
        exact (hadj₁ 0 (by omega)).symm
      · have h3 : ¬ s < m₁ := by omega
        simp only [h1, h3, if_false]
        have e : s + 1 - m₁ = (s - m₁) + 1 := by omega
        rw [e]
        exact hadj₂ (s - m₁) (by omega)
  · intro s hs
    by_cases h1 : s < m₁
    · left
      exact ⟨m₁ - s, by omega, by simp [h1]⟩
    · right
      exact ⟨s - m₁, by omega, by simp [h1]⟩

/-- A far point of the cluster, on either side of `mac`, is at macroscopic distance between
`Z` and `d (ρ + Z) + Δ` from a cube `Q` within `Δ` of `mac`, when `ρ = Δ + Z`. -/
theorem pclose_far_norm (hd : 1 ≤ d) (Q mac M : Site d) (Δ Z ρ : ℕ) (hρ : ρ = Δ + Z)
    (hΔ : mnorm (Q - mac) ≤ (Δ : ℤ))
    (hM : (∀ l, (ρ : ℤ) ≤ M l - mac l ∧ M l - mac l ≤ ρ + Z) ∨
      (∀ l, -((ρ : ℤ) + Z) ≤ M l - mac l ∧ M l - mac l ≤ -(ρ : ℤ))) :
    (Z : ℤ) ≤ mnorm (Q - M) ∧ mnorm (Q - M) ≤ (d : ℤ) * ((ρ : ℤ) + Z) + Δ := by
  have hcoord : ∀ l, |M l - mac l| ≤ (ρ : ℤ) + Z := by
    intro l
    rcases hM with h | h
    · have := h l
      rw [abs_le]; constructor <;> linarith [Int.natCast_nonneg ρ, Int.natCast_nonneg Z]
    · have := h l
      rw [abs_le]; constructor <;> linarith [Int.natCast_nonneg ρ, Int.natCast_nonneg Z]
  have hlow : ∀ l, (ρ : ℤ) ≤ |M l - mac l| := by
    intro l
    rcases hM with h | h
    · have := h l
      rw [abs_of_nonneg (by linarith [Int.natCast_nonneg ρ])]
      exact this.1
    · have := h l
      rw [abs_of_nonpos (by linarith [Int.natCast_nonneg ρ])]
      linarith [this.2]
  have hup : mnorm (M - mac) ≤ (d : ℤ) * ((ρ : ℤ) + Z) := pclose_mnorm_le_of_coord M mac _ hcoord
  have hlo : (d : ℤ) * ρ ≤ mnorm (M - mac) := by
    unfold mnorm
    calc (d : ℤ) * ρ = ∑ _l : Fin d, (ρ : ℤ) := by simp
      _ ≤ ∑ l, |(M - mac) l| := Finset.sum_le_sum fun l _ => hlow l
  have hQM : mnorm (Q - M) = mnorm (M - Q) := by
    rw [← pclose_mnorm_neg (Q - M)]; simp
  have hsplit1 : Q - M = (Q - mac) - (M - mac) := by abel
  have hsplit2 : M - mac = (M - Q) + (Q - mac) := by abel
  constructor
  · have h1 := pclose_mnorm_add_le (M - Q) (Q - mac)
    rw [← hsplit2] at h1
    have hd1 : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    have hρ0 : (0 : ℤ) ≤ ρ := Int.natCast_nonneg ρ
    have : (ρ : ℤ) ≤ (d : ℤ) * ρ := by nlinarith
    have hρZ : (ρ : ℤ) = Δ + Z := by rw [hρ]; push_cast; ring
    rw [hQM]
    linarith
  · have h1 := pclose_mnorm_sub_le (Q - mac) (M - mac)
    rw [← hsplit1] at h1
    linarith

end Exploding
