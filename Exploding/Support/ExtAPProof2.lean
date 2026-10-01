/-
The linear chemical-distance bound from a chain of good cubes: a star-step of
good sites lies inside one good cube, so the open walk realising it has length at
most `2 d`, and summing over a good star-chain gives an open path of length at
most `2 d` per step.
-/
import Exploding.Support.ExtAPProof

open Exploding LatticeProb MeasureTheory

namespace Exploding

variable {d : ℕ}

/-! ### The king graph of star-adjacent sites -/

/-- Two sites are neighbours when they are distinct and nearby in every coordinate. -/
def xap2_kingGraph (d : ℕ) : SimpleGraph (Site d) where
  Adj x y := xap_Star x y
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun i => by rw [abs_sub_comm]; exact h.2 i⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

theorem xap2_kingGraph_adj {x y : Site d} : (xap2_kingGraph d).Adj x y ↔ xap_Star x y :=
  Iff.rfl

/-! ### The distance inside one good cube -/

/-- Inside a good cube, changing one coordinate at a time costs one open edge per
coordinate, so the open distance from the centre to any site of the cube is at
most the number of remaining coordinates. -/
theorem xap2_edist_cube_aux {ω : Site d × Fin d → Bool} {z : Site d} (hz : xap_Good ω z) :
    ∀ (s : Finset (Fin d)) (b : Site d), b ∈ xap_cube z → (∀ i, i ∉ s → b i = z i) →
      (openBondGraph ω).edist z b ≤ (s.card : ℕ∞) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro b hb hbs
      have hbz : b = z := funext fun i => hbs i (Finset.notMem_empty i)
      rw [hbz, SimpleGraph.edist_self]
      simp
  | insert j s hj ih =>
      intro b hb hbs
      set b' : Site d := Function.update b j (z j) with hb'def
      have hb'cube : b' ∈ xap_cube z := by
        intro i
        by_cases hij : i = j
        · subst hij; simp [hb'def]
        · simp only [hb'def, Function.update_of_ne hij]; exact hb i
      have hb's : ∀ i, i ∉ s → b' i = z i := by
        intro i his
        by_cases hij : i = j
        · subst hij; simp [hb'def]
        · simp only [hb'def, Function.update_of_ne hij]
          exact hbs i (by simp [hij, his])
      have h1 : (openBondGraph ω).edist z b' ≤ (s.card : ℕ∞) := ih b' hb'cube hb's
      have hcard : ((insert j s).card : ℕ∞) = (s.card : ℕ∞) + 1 := by
        rw [Finset.card_insert_of_notMem hj]; push_cast; ring
      by_cases hbj : b j = z j
      · have hbb' : b = b' := by
          funext i
          by_cases hij : i = j
          · subst hij; simp [hb'def, hbj]
          · simp [hb'def, Function.update_of_ne hij]
        rw [hbb', hcard]
        exact h1.trans (by simp)
      · have hopen : (openBondGraph ω).Adj b' b := by
          have hj1 : |b j - z j| ≤ 1 := hb j
          have hcases : b j = z j + 1 ∨ b j = z j - 1 := by
            rcases abs_cases (b j - z j) with ⟨h, _⟩ | ⟨h, _⟩
            · left; omega
            · right; omega
          rcases hcases with hc | hc
          · have hbe : b = b' + unit j := by
              funext i
              by_cases hij : i = j
              · subst hij; simp [hb'def, hc, unit]
              · simp [hb'def, unit, hij]
            have hlat : (lattice d).Adj b' b := ⟨j, Or.inl hbe⟩
            exact xap_open_adj_of_good hz hb'cube hb hlat
          · have hbe : b' = b + unit j := by
              funext i
              by_cases hij : i = j
              · subst hij; simp [hb'def, hc, unit]
              · simp [hb'def, unit, hij]
            have hlat : (lattice d).Adj b' b := ⟨j, Or.inr hbe⟩
            exact xap_open_adj_of_good hz hb'cube hb hlat
        have hstep : (openBondGraph ω).edist b' b ≤ 1 := by
          rw [SimpleGraph.edist_eq_one_iff_adj.mpr hopen]
        calc (openBondGraph ω).edist z b
            ≤ (openBondGraph ω).edist z b' + (openBondGraph ω).edist b' b :=
              SimpleGraph.edist_triangle
          _ ≤ (s.card : ℕ∞) + 1 := add_le_add h1 hstep
          _ = ((insert j s).card : ℕ∞) := hcard.symm

/-- Any two sites of a good cube are at open distance at most `2 d`. -/
theorem xap2_edist_cube_le {ω : Site d × Fin d → Bool} {z a b : Site d} (hz : xap_Good ω z)
    (ha : a ∈ xap_cube z) (hb : b ∈ xap_cube z) :
    (openBondGraph ω).edist a b ≤ ((2 * d : ℕ) : ℕ∞) := by
  have hza := xap2_edist_cube_aux hz Finset.univ a ha
    (fun i hi => absurd (Finset.mem_univ i) hi)
  have hzb := xap2_edist_cube_aux hz Finset.univ b hb
    (fun i hi => absurd (Finset.mem_univ i) hi)
  rw [Finset.card_univ, Fintype.card_fin] at hza hzb
  calc (openBondGraph ω).edist a b
      ≤ (openBondGraph ω).edist a z + (openBondGraph ω).edist z b :=
        SimpleGraph.edist_triangle
    _ = (openBondGraph ω).edist z a + (openBondGraph ω).edist z b := by
        rw [SimpleGraph.edist_comm]
    _ ≤ (d : ℕ∞) + (d : ℕ∞) := add_le_add hza hzb
    _ = ((2 * d : ℕ) : ℕ∞) := by push_cast; ring

/-- A star-step between good sites costs at most `2 d` open edges. -/
theorem xap2_edist_star {ω : Site d × Fin d → Bool} {a b : Site d} (ha : xap_Good ω a)
    (hab : xap_Star a b) : (openBondGraph ω).edist a b ≤ ((2 * d : ℕ) : ℕ∞) :=
  xap2_edist_cube_le ha (xap_mem_cube_self a) (xap_star_mem_cube hab)

/-! ### The distance along a good star-chain -/

/-- Along a walk of good, star-adjacent sites the open distance grows by at most
`2 d` per step. -/
theorem xap2_edist_walk {ω : Site d × Fin d → Bool} {a b : Site d}
    (p : (xap2_kingGraph d).Walk a b) (hgood : ∀ z ∈ p.support, xap_Good ω z) :
    (openBondGraph ω).edist a b ≤ ((2 * d : ℕ) : ℕ∞) * (p.length : ℕ∞) := by
  revert hgood
  induction p with
  | nil => intro _; simp
  | cons h p' ih =>
      intro hgood
      have hgood' : ∀ z ∈ p'.support, xap_Good ω z := by
        intro z hz
        exact hgood z (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hz)
      have ha : xap_Good ω _ := hgood _ (SimpleGraph.Walk.start_mem_support _)
      have hstar : xap_Star _ _ := h
      have ih' := ih hgood'
      rw [SimpleGraph.Walk.length_cons]
      calc (openBondGraph ω).edist _ _
          ≤ (openBondGraph ω).edist _ _ + (openBondGraph ω).edist _ _ :=
            SimpleGraph.edist_triangle
        _ ≤ ((2 * d : ℕ) : ℕ∞) + ((2 * d : ℕ) : ℕ∞) * (p'.length : ℕ∞) :=
            add_le_add (xap2_edist_star ha hstar) ih'
        _ = ((2 * d : ℕ) : ℕ∞) * ((p'.length : ℕ∞) + 1) := by ring

/-- If a good star-chain joins a site of the cube of the origin to a site of the
cube of `y`, then the open distance from `0` to `y` is at most `2 d` times the
chain length plus the two end cubes. -/
theorem xap2_edist_le_of_goodWalk {ω : Site d × Fin d → Bool} {z₀ z₁ y : Site d}
    (p : (xap2_kingGraph d).Walk z₀ z₁) (hgood : ∀ z ∈ p.support, xap_Good ω z)
    (h0 : 0 ∈ xap_cube z₀) (hy : y ∈ xap_cube z₁) :
    (openBondGraph ω).edist 0 y ≤ ((2 * d : ℕ) : ℕ∞) * ((p.length : ℕ∞) + 2) := by
  have hz₀ : xap_Good ω z₀ := hgood z₀ (SimpleGraph.Walk.start_mem_support p)
  have hz₁ : xap_Good ω z₁ := hgood z₁ (SimpleGraph.Walk.end_mem_support p)
  have h0z₀ : (openBondGraph ω).edist 0 z₀ ≤ ((2 * d : ℕ) : ℕ∞) :=
    xap2_edist_cube_le hz₀ h0 (xap_mem_cube_self z₀)
  have hz₁y : (openBondGraph ω).edist z₁ y ≤ ((2 * d : ℕ) : ℕ∞) :=
    xap2_edist_cube_le hz₁ (xap_mem_cube_self z₁) hy
  have hwalk := xap2_edist_walk p hgood
  calc (openBondGraph ω).edist 0 y
      ≤ (openBondGraph ω).edist 0 z₀ + (openBondGraph ω).edist z₀ y :=
        SimpleGraph.edist_triangle
    _ ≤ (openBondGraph ω).edist 0 z₀
          + ((openBondGraph ω).edist z₀ z₁ + (openBondGraph ω).edist z₁ y) := by
        gcongr
        exact SimpleGraph.edist_triangle
    _ ≤ ((2 * d : ℕ) : ℕ∞)
          + (((2 * d : ℕ) : ℕ∞) * (p.length : ℕ∞) + ((2 * d : ℕ) : ℕ∞)) :=
        add_le_add h0z₀ (add_le_add hwalk hz₁y)
    _ = ((2 * d : ℕ) : ℕ∞) * ((p.length : ℕ∞) + 2) := by ring

end Exploding
