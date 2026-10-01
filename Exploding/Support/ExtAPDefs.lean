/-
Vocabulary for a chemical distance bound for bond percolation at high density: cubes of
sup-norm radius one, good sites (every bond of the cube is open), clusters of bad sites,
open connectivity inside a prescribed set of sites, and the boundary hypothesis for
connected sets of `ℤ^d` that the surgery around a cluster rests on.
-/
import Exploding.Support.Percolation
import Exploding.Support.ECProofDyn

namespace Exploding

open LatticeProb Relation

variable {d : ℕ}

/-! ### Cubes and good sites -/

/-- The cube of sup-norm radius one about `z`. -/
def xap_cube (z : Site d) : Set (Site d) := {x | ∀ i, |x i - z i| ≤ 1}

theorem xap_mem_cube_self (z : Site d) : z ∈ xap_cube z := fun i => by simp

/-- A site is good for a bond configuration when every bond with both endpoints in its cube
is open. -/
def xap_Good (ω : Site d × Fin d → Bool) (z : Site d) : Prop :=
  ∀ (x : Site d) (i : Fin d), x ∈ xap_cube z → x + unit i ∈ xap_cube z → ω (x, i) = true

/-- Two distinct sites whose coordinates differ by at most one. -/
def xap_Star (x y : Site d) : Prop := x ≠ y ∧ ∀ i, |x i - y i| ≤ 1

theorem xap_star_mem_cube {x y : Site d} (h : xap_Star x y) : y ∈ xap_cube x := fun i => by
  rw [abs_sub_comm]; exact h.2 i

theorem xap_lattice_mem_cube {x y : Site d} (h : (lattice d).Adj x y) : y ∈ xap_cube x := by
  obtain ⟨i, h | h⟩ := h
  · intro j
    subst h
    by_cases hj : j = i <;> simp [unit, hj]
  · intro j
    subst h
    by_cases hj : j = i <;> simp [unit, hj]

/-! ### Open bonds -/

theorem xap_open_adj_of_bond {ω : Site d × Fin d → Bool} {x : Site d} {i : Fin d}
    (h : ω (x, i) = true) : (openBondGraph ω).Adj x (x + unit i) := by
  rw [openBondGraph, SimpleGraph.fromRel_adj]
  refine ⟨fun e => unit_ne_zero i ?_, Or.inl ⟨i, rfl, h⟩⟩
  have := congrArg (· - x) e
  simpa using this.symm

theorem xap_lattice_of_open {ω : Site d × Fin d → Bool} {a b : Site d}
    (h : (openBondGraph ω).Adj a b) : (lattice d).Adj a b := by
  rw [openBondGraph, SimpleGraph.fromRel_adj] at h
  obtain ⟨_, ⟨i, hi, _⟩ | ⟨i, hi, _⟩⟩ := h
  · exact ⟨i, Or.inl hi⟩
  · exact ⟨i, Or.inr hi⟩

theorem xap_open_adj_of_good {ω : Site d × Fin d → Bool} {z a b : Site d}
    (hz : xap_Good ω z) (ha : a ∈ xap_cube z) (hb : b ∈ xap_cube z)
    (hab : (lattice d).Adj a b) : (openBondGraph ω).Adj a b := by
  obtain ⟨i, h | h⟩ := hab
  · subst h
    exact xap_open_adj_of_bond (hz a i ha hb)
  · subst h
    exact (xap_open_adj_of_bond (hz b i hb ha)).symm

/-! ### Connectivity inside a set of sites -/

theorem xap_rtg_mono {α : Type*} {r p : α → α → Prop} (hrp : ∀ a b, r a b → p a b) {a b : α}
    (h : ReflTransGen r a b) : ReflTransGen p a b := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (hrp _ _ hbc)

theorem xap_rtg_symm {α : Type*} {r : α → α → Prop} (hr : ∀ a b, r a b → r b a) {a b : α}
    (h : ReflTransGen r a b) : ReflTransGen r b a := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hbc ih => exact ReflTransGen.head (hr _ _ hbc) ih

/-- An open bond of `ω` between two sites of `S`. -/
def xap_RS (ω : Site d × Fin d → Bool) (S : Set (Site d)) (a b : Site d) : Prop :=
  a ∈ S ∧ b ∈ S ∧ (openBondGraph ω).Adj a b

/-- `p` and `q` are joined by a path of open bonds all of whose sites lie in `S`. -/
def xap_Reach (ω : Site d × Fin d → Bool) (S : Set (Site d)) (p q : Site d) : Prop :=
  p ∈ S ∧ ReflTransGen (xap_RS ω S) p q

section reach

variable {ω : Site d × Fin d → Bool} {S S' : Set (Site d)} {p q r : Site d}

theorem xap_reach_refl (h : p ∈ S) : xap_Reach ω S p p := ⟨h, ReflTransGen.refl⟩

theorem xap_reach_mem_right (h : xap_Reach ω S p q) : q ∈ S := by
  obtain ⟨hp, h⟩ := h
  rcases ReflTransGen.cases_tail h with h | ⟨b, _, hb⟩
  · rw [h]; exact hp
  · exact hb.2.1

theorem xap_reach_trans (h1 : xap_Reach ω S p q) (h2 : xap_Reach ω S q r) :
    xap_Reach ω S p r := ⟨h1.1, h1.2.trans h2.2⟩

theorem xap_reach_mono (hS : S ⊆ S') (h : xap_Reach ω S p q) : xap_Reach ω S' p q :=
  ⟨hS h.1, xap_rtg_mono (fun _ _ hab => ⟨hS hab.1, hS hab.2.1, hab.2.2⟩) h.2⟩

theorem xap_reach_step (hp : p ∈ S) (hq : q ∈ S) (h : (openBondGraph ω).Adj p q) :
    xap_Reach ω S p q := ⟨hp, ReflTransGen.single ⟨hp, hq, h⟩⟩

theorem xap_reach_symm (h : xap_Reach ω S p q) : xap_Reach ω S q p := by
  exact ⟨xap_reach_mem_right h,
    xap_rtg_symm (fun _ _ hab => ⟨hab.2.1, hab.1, hab.2.2.symm⟩) h.2⟩

theorem xap_reach_open (h : xap_Reach ω S p q) : ReflTransGen (openBondGraph ω).Adj p q :=
  xap_rtg_mono (fun _ _ hab => hab.2.2) h.2

end reach

/-! ### Good sites connect their cube -/

theorem xap_cube_reach {ω : Site d × Fin d → Bool} {z : Site d} (hz : xap_Good ω z) :
    ∀ b ∈ xap_cube z, ReflTransGen (xap_RS ω (xap_cube z)) z b := by
  classical
  have key : ∀ s : Finset (Fin d), ∀ b ∈ xap_cube z, (∀ i, i ∉ s → b i = z i) →
      ReflTransGen (xap_RS ω (xap_cube z)) z b := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro b _ hb
      have : b = z := funext fun i => hb i (Finset.notMem_empty i)
      rw [this]
    | insert j s hj ih =>
      intro b hb hbs
      set b' : Site d := Function.update b j (z j) with hb'
      have hb'cube : b' ∈ xap_cube z := by
        intro i
        by_cases hij : i = j
        · subst hij; simp [hb']
        · simp only [hb', Function.update_of_ne hij]; exact hb i
      have hb's : ∀ i, i ∉ s → b' i = z i := by
        intro i his
        by_cases hij : i = j
        · subst hij; simp [hb']
        · simp only [hb', Function.update_of_ne hij]
          exact hbs i (by simp [hij, his])
      have h1 := ih b' hb'cube hb's
      by_cases hbj : b j = z j
      · have : b' = b := by
          funext i
          by_cases hij : i = j
          · subst hij; simp [hb', hbj]
          · simp [hb', Function.update_of_ne hij]
        rw [this] at h1; exact h1
      · refine h1.tail ⟨hb'cube, hb, ?_⟩
        have hj1 : |b j - z j| ≤ 1 := hb j
        have hcases : b j = z j + 1 ∨ b j = z j - 1 := by
          rcases abs_cases (b j - z j) with ⟨h, _⟩ | ⟨h, _⟩
          · left; omega
          · right; omega
        rcases hcases with hc | hc
        · have hbe : b = b' + unit j := by
            funext i
            by_cases hij : i = j
            · subst hij; simp [hb', hc, unit]
            · simp [hb', unit, hij]
          have hlat : (lattice d).Adj b' b := ⟨j, Or.inl hbe⟩
          exact xap_open_adj_of_good hz hb'cube hb hlat
        · have hbe : b' = b + unit j := by
            funext i
            by_cases hij : i = j
            · subst hij; simp [hb', hc, unit]
            · simp [hb', unit, hij]
          have hlat : (lattice d).Adj b' b := ⟨j, Or.inr hbe⟩
          exact xap_open_adj_of_good hz hb'cube hb hlat
  intro b hb
  exact key Finset.univ b hb (fun i hi => absurd (Finset.mem_univ i) hi)

/-- Any two sites of the cube of a good site are joined by open bonds inside the cube. -/
theorem xap_cube_reach' {ω : Site d × Fin d → Bool} {z a b : Site d} (hz : xap_Good ω z)
    (ha : a ∈ xap_cube z) (hb : b ∈ xap_cube z) : xap_Reach ω (xap_cube z) a b := by
  have h1 : xap_Reach ω (xap_cube z) z a := ⟨xap_mem_cube_self z, xap_cube_reach hz a ha⟩
  have h2 : xap_Reach ω (xap_cube z) z b := ⟨xap_mem_cube_self z, xap_cube_reach hz b hb⟩
  exact xap_reach_trans (xap_reach_symm h1) h2

end Exploding
