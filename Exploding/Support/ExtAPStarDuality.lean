/-
The star-duality statement of `xbc_StarDuality` is false in dimension one: closing the origin
of the interval `cent 1 n` blocks every open crossing, while the only all-closed `*`-connected
sets are contained in that one site and so have at most one point rather than the side length
`2 * n + 1`.  This file records the counterexample, the correct dimension threshold `2 ≤ d`,
and the elementary size bound for `*`-connected sets that meet both opposite faces.
-/
import Exploding.Support.ExtBCBernoulli2
import Exploding.Support.ExtMHBase

open Exploding LatticeProb MeasureTheory Relation

namespace Exploding

variable {d : ℕ}

/-! ### A discrete intermediate value lemma -/

/-- If every step of a relation changes the `i`-coordinate by at most one, then a chain from a
site of coordinate at most `k` to a site of coordinate at least `k` contains a site of
coordinate exactly `k`. -/
theorem xbd_path_hits {r : Site d → Site d → Prop} {i : Fin d} {x y : Site d} {k : ℤ}
    (hr : ∀ a b, r a b → |a i - b i| ≤ 1) (hpath : ReflTransGen r x y)
    (hx : x i ≤ k) (hy : k ≤ y i) :
    ∃ z : Site d, ReflTransGen r x z ∧ z i = k := by
  have hmain : ∀ y : Site d, ReflTransGen r x y → k ≤ y i →
      ∃ z : Site d, ReflTransGen r x z ∧ z i = k := by
    intro y hpath
    induction hpath with
    | refl => intro _; exact ⟨x, ReflTransGen.refl, by omega⟩
    | tail hpref hbc ih =>
      rename_i bmid cfinal
      intro hky
      by_cases hk : k ≤ bmid i
      · obtain ⟨z, hxz, hzk⟩ := ih hk
        exact ⟨z, hxz, hzk⟩
      · have hle := hr bmid cfinal hbc
        rw [abs_le] at hle
        exact ⟨cfinal, hpref.tail hbc, by omega⟩
  exact hmain y hpath hy

/-! ### The one-dimensional counterexample -/

/-- The configuration of `ℤ` that is closed exactly at the origin. -/
def xbd_oneConfig : Site 1 → Bool := fun z => decide (z 0 ≠ 0)

theorem xbd_oneConfig_zero : xbd_oneConfig (0 : Site 1) = false := by
  simp [xbd_oneConfig]

theorem xbd_oneConfig_eq_zero {z : Site 1} (h : xbd_oneConfig z = false) : z 0 = 0 := by
  have h' : ¬ z 0 ≠ 0 := of_decide_eq_false (by simpa [xbd_oneConfig] using h)
  simpa using h'

theorem xbd_oneConfig_ne {z : Site 1} (h : z 0 ≠ 0) : xbd_oneConfig z = true := by
  simp [xbd_oneConfig, h]

/-- Lattice neighbours change a coordinate by at most one. -/
theorem xbd_abs_sub_le_of_adj {a b : Site d} (h : (lattice d).Adj a b) (i : Fin d) :
    |a i - b i| ≤ 1 := by
  obtain ⟨j, hj | hj⟩ := h
  · subst hj
    by_cases hji : i = j
    · subst hji; simp [unit]
    · simp [unit, Pi.single_eq_of_ne hji]
  · subst hj
    by_cases hji : i = j
    · subst hji; simp [unit]
    · simp [unit, Pi.single_eq_of_ne hji]

/-- A site reached from the start of a crossing chain by a nonempty chain is open. -/
theorem xbd_rtg_target_open {n : ℕ} {ω : Site d → Bool} {x z : Site d}
    (h : ReflTransGen (fun a b => (lattice d).Adj a b ∧ a ∈ cent d n ∧ b ∈ cent d n ∧
      ω a = true ∧ ω b = true) x z) (hne : z ≠ x) : ω z = true := by
  rcases ReflTransGen.cases_tail h with h' | ⟨b, _, hb⟩
  · exact absurd h' hne
  · exact hb.2.2.2.2

/-- A chain that goes from coordinate `-1` to coordinate `1` in the open sites of the interval
cannot avoid the closed origin. -/
theorem xbd_one_no_cross (i : Fin 1) : ¬ xbc_Crosses 1 1 i xbd_oneConfig := by
  rintro ⟨x, y, hx, hy, _hxb, _hyb, hpath⟩
  have hxle : x i ≤ (0 : ℤ) := by rw [hx]; norm_num
  have hyge : (0 : ℤ) ≤ y i := by rw [hy]; norm_num
  have hr : ∀ a b : Site 1, ((lattice 1).Adj a b ∧ a ∈ cent 1 1 ∧ b ∈ cent 1 1 ∧
      xbd_oneConfig a = true ∧ xbd_oneConfig b = true) → |a i - b i| ≤ 1 :=
    fun a b hab => xbd_abs_sub_le_of_adj hab.1 i
  obtain ⟨z, hxz, hz0⟩ := xbd_path_hits (r := fun a b => (lattice 1).Adj a b ∧
      a ∈ cent 1 1 ∧ b ∈ cent 1 1 ∧ xbd_oneConfig a = true ∧ xbd_oneConfig b = true)
    (i := i) (k := 0) hr hpath hxle hyge
  have hzopen : xbd_oneConfig z = true :=
    xbd_rtg_target_open hxz (by
      intro hzx
      rw [hzx] at hz0
      exact absurd (hx.symm.trans hz0) (by norm_num))
  have hzclosed : xbd_oneConfig z = false := by
    have hz : z 0 = 0 := by
      have : (0 : Fin 1) = i := Subsingleton.elim _ _
      rw [this]
      exact hz0
    simp [xbd_oneConfig, hz]
  rw [hzclosed] at hzopen
  exact Bool.noConfusion hzopen

/-- **The one-dimensional statement is false.** -/
theorem xbd_not_starDuality_one : ¬ xbc_StarDuality 1 := by
  classical
  intro h
  have hnc := xbd_one_no_cross (0 : Fin 1)
  obtain ⟨s, hs, Γ, hΓ, hclosed⟩ := h 1 (0 : Fin 1) xbd_oneConfig hnc
  rw [xap11_starSets, Finset.mem_filter] at hΓ
  obtain ⟨_, hΓcard, _⟩ := hΓ
  have hsub : ∀ a ∈ Γ, a = (0 : Site 1) := by
    intro a ha
    have ha0 : a 0 = 0 := xbd_oneConfig_eq_zero (hclosed a ha)
    funext j
    fin_cases j
    exact ha0
  have hcard1 : Γ.card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro a ha b hb
    rw [hsub a ha, hsub b hb]
  omega

/-! ### The sharpest corrected statement -/

/-- The star duality restricted to the dimensions in which it can hold: `d ≥ 2`. -/
def xbd_StarDualityPos (d : ℕ) : Prop := 2 ≤ d → xbc_StarDuality d

/-! ### The size of a `*`-connected set meeting both faces -/

/-- Along a `*`-chain from a site `x ∈ F` of `i`-coordinate at most `k` to a site of
`i`-coordinate at least `k`, the set `F` meets the slice of coordinate `k`. -/
theorem xbd_hits_coord {F : Set (Site d)} {i : Fin d} {x : Site d} {k : ℤ}
    (hxF : x ∈ F) (hxk : x i ≤ k) :
    ∀ y : Site d, ReflTransGen (fun a b => a ∈ F ∧ b ∈ F ∧ xmh_star a b) x y →
      k ≤ y i → ∃ z ∈ F, z i = k := by
  intro y hpath
  induction hpath with
  | refl => intro _; exact ⟨x, hxF, by omega⟩
  | tail hpref hbc ih =>
    rename_i bmid cfinal
    intro hky
    by_cases hk : k ≤ bmid i
    · exact ih hk
    · have hle := hbc.2.2.2 i
      rw [abs_le] at hle
      exact ⟨cfinal, hbc.2.1, by omega⟩

/-- A `*`-connected set of sites meeting both the negative and the positive `i`-faces has at
least `2 * n + 1` points. -/
theorem xbd_card_ge_of_star_meets_faces {n : ℕ} {i : Fin d} {G : Finset (Site d)}
    (hconn : xmh_SConn (G : Set (Site d)))
    (hneg : ∃ x ∈ G, x i = -(n : ℤ)) (hpos : ∃ y ∈ G, y i = (n : ℤ)) :
    2 * n + 1 ≤ G.card := by
  classical
  obtain ⟨x, hxG, hx⟩ := hneg
  obtain ⟨y, hyG, hy⟩ := hpos
  have hpath := hconn x hxG y hyG
  let K : Finset ℤ := Finset.Icc (-(n : ℤ)) (n : ℤ)
  have hex : ∀ k : ↥K, ∃ z ∈ G, z i = (k : ℤ) := fun k => by
    have hk := Finset.mem_Icc.mp k.property
    exact xbd_hits_coord (F := (G : Set (Site d))) (i := i) (x := x) (k := (k : ℤ))
      hxG (by rw [hx]; exact hk.1) y hpath (by rw [hy]; exact hk.2)
  choose g hgG hgk using hex
  let g' : ↥K → ↥G := fun k => ⟨g k, hgG k⟩
  have hinj : Function.Injective g' := by
    intro a b hab
    have h1 := hgk a
    have h2 := hgk b
    have h3 : (g a) i = (g b) i := congrArg (fun w : ↥G => (w : Site d) i) hab
    rw [h1, h2] at h3
    exact Subtype.ext h3
  have hcard := Fintype.card_le_of_injective g' hinj
  rw [Fintype.card_coe, Fintype.card_coe] at hcard
  have hK : K.card = 2 * n + 1 := by
    simp only [K, Int.card_Icc]
    omega
  omega

end Exploding
