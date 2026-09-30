/-
The outer boundary of a connected set of the square lattice is `*`-connected
(the planar duality behind the Peierls estimate of Proposition 7.1), proved by a
mod-two parity argument: the indicator of the edges between the set and one part of
its boundary is a cocycle, hence a coboundary, hence constant on connected sets.
-/
import Exploding.Support.ECProofPoincare

namespace Exploding

open Relation

/-! ### Adjacency on `ℤ × ℤ` -/

/-- Nearest-neighbour adjacency on `ℤ × ℤ`. -/
def ec_adj4 (a b : ℤ × ℤ) : Prop := |a.1 - b.1| + |a.2 - b.2| = 1

/-- King-move adjacency on `ℤ × ℤ`. -/
def ec_adj8 (a b : ℤ × ℤ) : Prop := a ≠ b ∧ |a.1 - b.1| ≤ 1 ∧ |a.2 - b.2| ≤ 1

theorem ec_adj4_symm {a b : ℤ × ℤ} (h : ec_adj4 a b) : ec_adj4 b a := by
  unfold ec_adj4 at *
  rw [abs_sub_comm b.1, abs_sub_comm b.2]; exact h

theorem ec_adj8_symm {a b : ℤ × ℤ} (h : ec_adj8 a b) : ec_adj8 b a := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.symm, ?_, ?_⟩
  · rw [abs_sub_comm]; exact h2
  · rw [abs_sub_comm]; exact h3

theorem ec_adj4_iff (a b : ℤ × ℤ) :
    ec_adj4 a b ↔ b = a + (1, 0) ∨ b = a + (-1, 0) ∨ b = a + (0, 1) ∨ b = a + (0, -1) := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only [ec_adj4, Prod.mk_add_mk, Prod.mk.injEq]
  constructor
  · intro h
    rcases abs_cases (a1 - b1) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
    rcases abs_cases (a2 - b2) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;> omega
  · intro h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;> simp

theorem ec_adj4_adj8 {a b : ℤ × ℤ} (h : ec_adj4 a b) : ec_adj8 a b := by
  rcases (ec_adj4_iff a b).1 h with h | h | h | h <;> subst h <;>
    refine ⟨?_, ?_, ?_⟩ <;> simp [Prod.ext_iff]

/-! ### The finite parity lemma on a unit square -/

/-- The status of a vertex: in `A`; in the part `D₁` of the boundary; in the rest `D₂`
of the boundary; inside `B` but off the boundary; or elsewhere. -/
inductive ECSt
  | a | d1 | d2 | bi | o
  deriving DecidableEq, Fintype

/-- Which statuses may be nearest neighbours. -/
def ECSt.okAdj : ECSt → ECSt → Bool
  | .bi, .a => false
  | .a, .bi => false
  | .o, .d1 => false
  | .d1, .o => false
  | .o, .d2 => false
  | .d2, .o => false
  | .o, .bi => false
  | .bi, .o => false
  | _, _ => true

/-- Which statuses may lie in a common unit square. -/
def ECSt.okNear : ECSt → ECSt → Bool
  | .d1, .d2 => false
  | .d2, .d1 => false
  | _, _ => true

/-- The edge indicator between `A` and `D₁`. -/
def ECSt.cross : ECSt → ECSt → ZMod 2
  | .a, .d1 => 1
  | .d1, .a => 1
  | _, _ => 0

theorem ECSt.cross_symm (s t : ECSt) : ECSt.cross s t = ECSt.cross t s := by
  cases s <;> cases t <;> rfl

theorem ec_square_parity : ∀ s0 s1 s2 s3 : ECSt,
    ECSt.okAdj s0 s1 = true → ECSt.okAdj s1 s3 = true → ECSt.okAdj s0 s2 = true →
    ECSt.okAdj s2 s3 = true → ECSt.okNear s0 s1 = true → ECSt.okNear s0 s2 = true →
    ECSt.okNear s0 s3 = true → ECSt.okNear s1 s2 = true → ECSt.okNear s1 s3 = true →
    ECSt.okNear s2 s3 = true →
    ECSt.cross s0 s1 + ECSt.cross s1 s3 = ECSt.cross s0 s2 + ECSt.cross s2 s3 := by
  decide


open Classical in
/-- The status of a vertex. -/
noncomputable def ec_st (A B D1 : Set (ℤ × ℤ)) (z : ℤ × ℤ) : ECSt :=
  if z ∈ A then .a else if z ∈ D1 then .d1 else if z ∈ B then
    (if ∃ c ∈ A, ec_adj4 c z then .d2 else .bi) else .o

section
variable {A B D1 : Set (ℤ × ℤ)} {z : ℤ × ℤ}

theorem ec_st_cases (hD1 : ∀ z ∈ D1, z ∈ B ∧ ∃ c ∈ A, ec_adj4 c z) (z : ℤ × ℤ) :
    (z ∈ A ∧ ec_st A B D1 z = .a) ∨
    (z ∉ A ∧ z ∈ B ∧ z ∈ D1 ∧ ec_st A B D1 z = .d1) ∨
    (z ∉ A ∧ z ∈ B ∧ z ∉ D1 ∧ (∃ c ∈ A, ec_adj4 c z) ∧ ec_st A B D1 z = .d2) ∨
    (z ∉ A ∧ z ∈ B ∧ ¬ (∃ c ∈ A, ec_adj4 c z) ∧ ec_st A B D1 z = .bi) ∨
    (z ∉ A ∧ z ∉ B ∧ ec_st A B D1 z = .o) := by
  classical
  unfold ec_st
  by_cases hA : z ∈ A
  · left; simp [hA]
  · by_cases hD : z ∈ D1
    · right; left; exact ⟨hA, (hD1 z hD).1, hD, by simp [hA, hD]⟩
    · by_cases hB : z ∈ B
      · by_cases hc : ∃ c ∈ A, ec_adj4 c z
        · right; right; left; exact ⟨hA, hB, hD, hc, by simp [hA, hD, hB, hc]⟩
        · right; right; right; left; exact ⟨hA, hB, hc, by simp [hA, hD, hB, hc]⟩
      · right; right; right; right; exact ⟨hA, hB, by simp [hA, hD, hB]⟩

theorem ec_st_adj (hclose : ∀ b ∈ B, ∀ z, ec_adj4 b z → z ∉ A → z ∈ B)
    (hD1 : ∀ z ∈ D1, z ∈ B ∧ ∃ c ∈ A, ec_adj4 c z) {z w : ℤ × ℤ} (h : ec_adj4 z w) :
    ECSt.okAdj (ec_st A B D1 z) (ec_st A B D1 w) = true := by
  have hs := ec_adj4_symm h
  have hI : w ∈ A → z ∈ B → ∃ c ∈ A, ec_adj4 c z := fun hw _ => ⟨w, hw, hs⟩
  have hII : z ∈ A → w ∈ B → ∃ c ∈ A, ec_adj4 c w := fun hz _ => ⟨z, hz, h⟩
  have hIII : w ∈ B → z ∉ A → z ∈ B := fun hw hz => hclose w hw z hs hz
  have hIV : z ∈ B → w ∉ A → w ∈ B := fun hz hw => hclose z hz w h hw
  rcases ec_st_cases hD1 z with ⟨hzA, hz⟩ | ⟨hzA, hzB, _, hz⟩ | ⟨hzA, hzB, _, _, hz⟩ |
      ⟨hzA, hzB, hzN, hz⟩ | ⟨hzA, hzB, hz⟩ <;>
  rcases ec_st_cases hD1 w with ⟨hwA, hw⟩ | ⟨hwA, hwB, _, hw⟩ | ⟨hwA, hwB, _, _, hw⟩ |
      ⟨hwA, hwB, hwN, hw⟩ | ⟨hwA, hwB, hw⟩ <;>
  rw [hz, hw] <;>
  first
  | rfl
  | simp_all

theorem ec_st_near (hD1 : ∀ z ∈ D1, z ∈ B ∧ ∃ c ∈ A, ec_adj4 c z)
    (hsep : ∀ x ∈ D1, ∀ y, y ∈ B → (∃ c ∈ A, ec_adj4 c y) → y ∉ D1 →
      ¬ (|x.1 - y.1| ≤ 1 ∧ |x.2 - y.2| ≤ 1))
    {z w : ℤ × ℤ} (h1 : |z.1 - w.1| ≤ 1) (h2 : |z.2 - w.2| ≤ 1) :
    ECSt.okNear (ec_st A B D1 z) (ec_st A B D1 w) = true := by
  have h1' : |w.1 - z.1| ≤ 1 := by rw [abs_sub_comm]; exact h1
  have h2' : |w.2 - z.2| ≤ 1 := by rw [abs_sub_comm]; exact h2
  have hN1 : z ∈ D1 → w ∈ B → (∃ c ∈ A, ec_adj4 c w) → w ∉ D1 → False :=
    fun hz hwB hc hwD => hsep z hz w hwB hc hwD ⟨h1, h2⟩
  have hN2 : w ∈ D1 → z ∈ B → (∃ c ∈ A, ec_adj4 c z) → z ∉ D1 → False :=
    fun hw hzB hc hzD => hsep w hw z hzB hc hzD ⟨h1', h2'⟩
  rcases ec_st_cases hD1 z with ⟨hzA, hz⟩ | ⟨hzA, hzB, hzD1, hz⟩ | ⟨hzA, hzB, hzD2, hzc, hz⟩ |
      ⟨hzA, hzB, hzN, hz⟩ | ⟨hzA, hzB, hz⟩ <;>
  rcases ec_st_cases hD1 w with ⟨hwA, hw⟩ | ⟨hwA, hwB, hwD1, hw⟩ | ⟨hwA, hwB, hwD2, hwc, hw⟩ |
      ⟨hwA, hwB, hwN, hw⟩ | ⟨hwA, hwB, hw⟩ <;>
  rw [hz, hw] <;>
  first
  | rfl
  | simp_all

theorem ec_st_of_mem (hz : z ∈ A) : ec_st A B D1 z = .a := by
  classical
  unfold ec_st; simp [hz]

theorem ec_st_ne_a (hz : z ∉ A) : ec_st A B D1 z ≠ .a := by
  classical
  unfold ec_st; simp only [hz, if_false]; split_ifs <;> simp

theorem ec_st_d1 (hzA : z ∉ A) (hzD : z ∈ D1) : ec_st A B D1 z = .d1 := by
  classical
  unfold ec_st; simp [hzA, hzD]

theorem ec_st_d2 (hzA : z ∉ A) (hzD : z ∉ D1) (hzB : z ∈ B) (hc : ∃ c ∈ A, ec_adj4 c z) :
    ec_st A B D1 z = .d2 := by
  classical
  unfold ec_st; simp [hzA, hzD, hzB, hc]

theorem ECSt.cross_eq_zero_of_ne_a {s t : ECSt} (hs : s ≠ .a) (ht : t ≠ .a) :
    ECSt.cross s t = 0 := by
  cases s <;> cases t <;> simp_all [ECSt.cross]

theorem ec_coboundary (hclose : ∀ b ∈ B, ∀ z, ec_adj4 b z → z ∉ A → z ∈ B)
    (hD1 : ∀ z ∈ D1, z ∈ B ∧ ∃ c ∈ A, ec_adj4 c z)
    (hsep : ∀ x ∈ D1, ∀ y, y ∈ B → (∃ c ∈ A, ec_adj4 c y) → y ∉ D1 →
      ¬ (|x.1 - y.1| ≤ 1 ∧ |x.2 - y.2| ≤ 1)) :
    ∃ f : ℤ × ℤ → ZMod 2, ∀ u v, ec_adj4 u v →
      f u + f v = ECSt.cross (ec_st A B D1 u) (ec_st A B D1 v) := by
  have hsq : ∀ p : ℤ × ℤ,
      ECSt.cross (ec_st A B D1 p) (ec_st A B D1 (p + (1, 0))) +
        ECSt.cross (ec_st A B D1 (p + (1, 0))) (ec_st A B D1 (p + (1, 0) + (0, 1))) =
      ECSt.cross (ec_st A B D1 p) (ec_st A B D1 (p + (0, 1))) +
        ECSt.cross (ec_st A B D1 (p + (0, 1))) (ec_st A B D1 (p + (0, 1) + (1, 0))) := by
    intro p
    have e : p + (0, 1) + (1, 0) = p + (1, 0) + (0, 1) := by
      rw [add_right_comm]
    rw [e]
    have a01 : ec_adj4 p (p + (1, 0)) := (ec_adj4_iff _ _).2 (Or.inl rfl)
    have a13 : ec_adj4 (p + (1, 0)) (p + (1, 0) + (0, 1)) := (ec_adj4_iff _ _).2 (by simp)
    have a02 : ec_adj4 p (p + (0, 1)) := (ec_adj4_iff _ _).2 (by simp)
    have a23 : ec_adj4 (p + (0, 1)) (p + (1, 0) + (0, 1)) := by
      rw [ec_adj4_iff]
      left
      rw [add_right_comm]
    have nr : ∀ u v : ℤ × ℤ, |u.1 - v.1| ≤ 1 → |u.2 - v.2| ≤ 1 →
        ECSt.okNear (ec_st A B D1 u) (ec_st A B D1 v) = true :=
      fun u v h1 h2 => ec_st_near hD1 hsep h1 h2
    refine ec_square_parity _ _ _ _ (ec_st_adj hclose hD1 a01) (ec_st_adj hclose hD1 a13)
      (ec_st_adj hclose hD1 a02) (ec_st_adj hclose hD1 a23) ?_ ?_ ?_ ?_ ?_ ?_ <;>
      refine nr _ _ ?_ ?_ <;>
      simp only [Prod.fst_add, Prod.snd_add, abs_le] <;> omega
  obtain ⟨f, hf⟩ := ec_poincare
    (fun p => ECSt.cross (ec_st A B D1 p) (ec_st A B D1 (p + (1, 0))))
    (fun p => ECSt.cross (ec_st A B D1 p) (ec_st A B D1 (p + (0, 1)))) hsq
  refine ⟨f, ?_⟩
  intro u v huv
  rcases (ec_adj4_iff u v).1 huv with h | h | h | h
  · subst h
    have := (hf u).1
    rw [this, ← add_assoc, ec_zmod2_add_self, zero_add]
  · subst h
    have := (hf (u + (-1, 0))).1
    have e : u + (-1, 0) + (1, 0) = u := by
      ext <;> simp
    rw [e] at this
    rw [this, ECSt.cross_symm, add_comm, ← add_assoc, ec_zmod2_add_self, zero_add]
  · subst h
    have := (hf u).2
    rw [this, ← add_assoc, ec_zmod2_add_self, zero_add]
  · subst h
    have := (hf (u + (0, -1))).2
    have e : u + (0, -1) + (0, 1) = u := by
      ext <;> simp
    rw [e] at this
    rw [this, ECSt.cross_symm, add_comm, ← add_assoc, ec_zmod2_add_self, zero_add]

end

/-- **The outer boundary of a connected set is `*`-connected.**  `A` and `B` are
connected sets of nearest-neighbour adjacency, disjoint, with `B` closed under
adjacency outside `A` (`B` is a component of the complement of `A`); the vertices of
`B` adjacent to `A` are joined by a chain of king moves inside that boundary. -/
theorem ec_star_conn (A B : Set (ℤ × ℤ))
    (hA : ∀ u ∈ A, ∀ v ∈ A, ReflTransGen (fun a b => a ∈ A ∧ b ∈ A ∧ ec_adj4 a b) u v)
    (hB : ∀ u ∈ B, ∀ v ∈ B, ReflTransGen (fun a b => a ∈ B ∧ b ∈ B ∧ ec_adj4 a b) u v)
    (hdisj : ∀ z, z ∈ A → z ∈ B → False)
    (hclose : ∀ b ∈ B, ∀ z, ec_adj4 b z → z ∉ A → z ∈ B)
    (x y : ℤ × ℤ) (hx : x ∈ B ∧ ∃ c ∈ A, ec_adj4 c x) (hy : y ∈ B ∧ ∃ c ∈ A, ec_adj4 c y) :
    ReflTransGen (fun a b => (a ∈ B ∧ ∃ c ∈ A, ec_adj4 c a) ∧
      (b ∈ B ∧ ∃ c ∈ A, ec_adj4 c b) ∧ ec_adj8 a b) x y := by
  classical
  by_contra hne
  set R : ℤ × ℤ → ℤ × ℤ → Prop := fun a b => (a ∈ B ∧ ∃ c ∈ A, ec_adj4 c a) ∧
      (b ∈ B ∧ ∃ c ∈ A, ec_adj4 c b) ∧ ec_adj8 a b with hR
  set D1 : Set (ℤ × ℤ) := {z | (z ∈ B ∧ ∃ c ∈ A, ec_adj4 c z) ∧ ReflTransGen R x z} with hD1def
  have hyD1 : y ∉ D1 := fun h => hne h.2
  have hxD1 : x ∈ D1 := ⟨hx, ReflTransGen.refl⟩
  have hD1 : ∀ z ∈ D1, z ∈ B ∧ ∃ c ∈ A, ec_adj4 c z := fun z hz => hz.1
  have hsep : ∀ x' ∈ D1, ∀ y', y' ∈ B → (∃ c ∈ A, ec_adj4 c y') → y' ∉ D1 →
      ¬ (|x'.1 - y'.1| ≤ 1 ∧ |x'.2 - y'.2| ≤ 1) := by
    intro x' hx' y' hy'B hy'c hy'D hnear
    apply hy'D
    refine ⟨⟨hy'B, hy'c⟩, hx'.2.tail ?_⟩
    refine ⟨hx'.1, ⟨hy'B, hy'c⟩, ?_, hnear.1, hnear.2⟩
    intro heq
    subst heq
    exact hy'D hx'
  obtain ⟨f, hf⟩ := ec_coboundary hclose hD1 hsep
  have char2 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  have hfA : ∀ u ∈ A, ∀ v ∈ A, f u = f v := by
    intro u hu v hv
    have hstep : ∀ v, ReflTransGen (fun a b => a ∈ A ∧ b ∈ A ∧ ec_adj4 a b) u v → f u = f v := by
      intro v h
      induction h with
      | refl => rfl
      | tail _ hbc ih =>
        refine ih.trans (char2 _ _ ?_)
        rw [hf _ _ hbc.2.2, ec_st_of_mem hbc.1, ec_st_of_mem hbc.2.1]
        rfl
    exact hstep v (hA u hu v hv)
  have hfB : ∀ u ∈ B, ∀ v ∈ B, f u = f v := by
    intro u hu v hv
    have hstep : ∀ v, ReflTransGen (fun a b => a ∈ B ∧ b ∈ B ∧ ec_adj4 a b) u v → f u = f v := by
      intro v h
      induction h with
      | refl => rfl
      | tail _ hbc ih =>
        refine ih.trans (char2 _ _ ?_)
        rw [hf _ _ hbc.2.2]
        exact ECSt.cross_eq_zero_of_ne_a (ec_st_ne_a fun h => hdisj _ h hbc.1)
          (ec_st_ne_a fun h => hdisj _ h hbc.2.1)
    exact hstep v (hB u hu v hv)
  obtain ⟨a1, ha1, hadj1⟩ := hx.2
  obtain ⟨a2, ha2, hadj2⟩ := hy.2
  have hxA : x ∉ A := fun h => hdisj _ h hx.1
  have hyA : y ∉ A := fun h => hdisj _ h hy.1
  have e1 : f a1 + f x = 1 := by
    rw [hf _ _ hadj1, ec_st_of_mem ha1, ec_st_d1 hxA hxD1]
    rfl
  have e2 : f a2 + f y = 0 := by
    rw [hf _ _ hadj2, ec_st_of_mem ha2, ec_st_d2 hyA hyD1 hy.1 ⟨a2, ha2, hadj2⟩]
    rfl
  have h3 := hfA a1 ha1 a2 ha2
  have h4 := hfB x hx.1 y hy.1
  rw [h3, h4, e2] at e1
  exact absurd e1 (by decide)

end Exploding
