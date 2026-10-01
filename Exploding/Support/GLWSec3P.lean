/-
Proposition 5.1 of the paper (generalized last wave): the lighting of a rectangle from a lit tile
of `C_∞`, along two walks of `C_∞`.

The first walk goes from the lit tile to a point `M_f` of `C_∞` far from the target and the second
from `M_f` to a point `M_o` on the other side of the target; the sites of the tiles of the second
walk near the target contain a path of distinct sites whose bounding rectangle contains the
target.
-/
import Exploding.Support.GLWSec3O

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

/-- Two walks, the end of the first being the start of the second, concatenate. -/
theorem glws_concat_walk (L1 L2 : ℕ) (c1 c2 : ℕ → Site d) (h : c1 L1 = c2 0)
    (hadj1 : ∀ s, s < L1 → (lattice d).Adj (c1 s) (c1 (s + 1)))
    (hadj2 : ∀ s, s < L2 → (lattice d).Adj (c2 s) (c2 (s + 1))) :
    ∃ c : ℕ → Site d, (∀ s, s ≤ L1 → c s = c1 s) ∧ (∀ s, L1 ≤ s → c s = c2 (s - L1)) ∧
      ∀ s, s < L1 + L2 → (lattice d).Adj (c s) (c (s + 1)) := by
  refine ⟨fun s => if s ≤ L1 then c1 s else c2 (s - L1), ?_, ?_, ?_⟩
  · intro s hs
    simp [hs]
  · intro s hs
    by_cases h1 : s ≤ L1
    · have : s = L1 := le_antisymm h1 hs
      subst this
      simp [h]
    · simp [h1]
  · intro s hs
    by_cases h1 : s < L1
    · have h2 : s ≤ L1 := le_of_lt h1
      have h3 : s + 1 ≤ L1 := h1
      simp only [h2, h3, if_true]
      exact hadj1 s h1
    · by_cases h2 : s = L1
      · subst h2
        have h3 : ¬ (s + 1 ≤ s) := by omega
        simp only [le_refl, if_true, h3, if_false]
        have e : s + 1 - s = 0 + 1 := by omega
        rw [e, h]
        exact hadj2 0 (by omega)
      · have h2' : ¬ s ≤ L1 := by omega
        have h3 : ¬ s + 1 ≤ L1 := by omega
        simp only [h2', h3, if_false]
        have e : s + 1 - L1 = (s - L1) + 1 := by omega
        rw [e]
        exact hadj2 (s - L1) (by omega)

/-- **The core of the lighting from a lit tile.** -/
theorem glws_light_near_core (hd : 2 ≤ d) (η : Site d → ℤ) (hlow : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (k : Fin d → ℕ) (hk : ∀ i, 0 < k i)
    (Cinf : Set (Site d)) (hgood : ∀ j ∈ Cinf, StronglyBoxCrossed η k j)
    (γp : ℝ) (hpf : glws_PF d γp η) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ (N : ℕ), 1 ≤ N → ∀ (zc : Site d) (τ : ℕ) (j : Site d),
      glws_Fired η N k zc τ j → ∀ (Mf Mo : Site d) (L1 L2 : ℕ) (c1 c2 : ℕ → Site d),
      c1 0 = j → c1 L1 = Mf → (∀ s, s ≤ L1 → c1 s ∈ Cinf) →
      (∀ s, s < L1 → (lattice d).Adj (c1 s) (c1 (s + 1))) →
      c2 0 = Mf → c2 L2 = Mo → (∀ s, s ≤ L2 → c2 s ∈ Cinf) →
      (∀ s, s < L2 → (lattice d).Adj (c2 s) (c2 (s + 1))) →
      ∀ (a b : Site d), a ∈ rboxShift k Mf → b ∈ rboxShift k Mo →
      (∀ s, s ≤ L2 → ∀ y ∈ rboxShift k (c2 s), y ∈ cent d n) →
      (∃ l₀ : Fin d, Real.log n ^ γp ≤ ((|a l₀ - b l₀| : ℤ) : ℝ) + 1) →
      ∀ w : Site d, (∀ m, min (a m) (b m) ≤ w m ∧ w m ≤ max (a m) (b m)) →
        0 < wave η N zc (τ + (L1 + L2) * ∏ l, k l + ((L2 + 1) * (∑ i, k i) ^ d) ^ d) w := by
  obtain ⟨n0, hbox⟩ := glws_light_box hd η hlow hhigh k hk Cinf hgood γp hpf
  refine ⟨n0, fun n hn N hN zc τ j hfired Mf Mo L1 L2 c1 c2 hc10 hc1L hc1S hc1adj hc20 hc2L hc2S
    hc2adj a b ha hb hcent hlen w hw => ?_⟩
  obtain ⟨c, hcL1, hcL2, hcadj⟩ := glws_concat_walk L1 L2 c1 c2 (by rw [hc1L, hc20]) hc1adj hc2adj
  have hcC : ∀ s, s ≤ L1 + L2 → c s ∈ Cinf := by
    intro s hs
    by_cases h : s ≤ L1
    · rw [hcL1 s h]; exact hc1S s h
    · rw [hcL2 s (by omega)]; exact hc2S _ (by omega)
  have hc0 : c 0 = j := by rw [hcL1 0 (Nat.zero_le _), hc10]
  have hcL1' : c L1 = Mf := by rw [hcL1 L1 le_rfl, hc1L]
  have hcL' : c (L1 + L2) = Mo := by rw [hcL2 (L1 + L2) (by omega), Nat.add_sub_cancel_left, hc2L]
  have := hbox n hn N hN zc L1 (L1 + L2) (by omega) c hcC hcadj τ (by rw [hc0]; exact hfired)
    a b (by rw [hcL1']; exact ha) (by rw [hcL']; exact hb)
    (fun s h1 h2 y hy => by
      rw [hcL2 s h1] at hy
      exact hcent (s - L1) (by omega) y hy)
    hlen w hw
  rw [show L1 + L2 - L1 + 1 = L2 + 1 from by omega] at this
  exact this

end Exploding
