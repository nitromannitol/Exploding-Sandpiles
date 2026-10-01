/-
The inner boundary of a connected set of `ℤ^d` is `*`-connected, in every dimension,
extending the planar parity argument of `Exploding.ec_star_conn` by means of the
general Poincaré lemma `xmh3_poincare`.  A vertex is classified by whether it lies in
`A`, in one chosen part `D₁` of the boundary, in the rest of the boundary, in `B` off
the boundary, or outside; the indicator of the `A`--`D₁` edges is shown to be a closed
one-cochain, hence a coboundary, and the coboundary turns out to be constant on `A`
and on `B`, which forces the two boundary parts to coincide.
-/
import Exploding.Support.ExtMHProof4
import Exploding.Support.ExtMHBase
import Exploding.Support.ECProofStar

namespace Exploding

open LatticeProb Relation

variable {d : ℕ}

/-- Chebyshev-adjacency: all coordinates differ by at most one.  (This is `xmh_star`
without the proviso of distinctness.) -/
def xmh3_near (a b : Site d) : Prop := ∀ i, |a i - b i| ≤ 1

theorem xmh3_unit_abs_le (i k : Fin d) : |(unit i : Site d) k| ≤ 1 := by
  by_cases h : k = i
  · subst h; simp [unit, Pi.single_eq_same]
  · simp [unit, Pi.single_eq_of_ne h]

theorem xmh3_near_refl (a : Site d) : xmh3_near a a := fun _ => by simp

theorem xmh3_near_symm {a b : Site d} (h : xmh3_near a b) : xmh3_near b a :=
  fun i => by rw [abs_sub_comm]; exact h i

theorem xmh3_near_of_adj {a b : Site d} (h : (lattice d).Adj a b) : xmh3_near a b := by
  obtain ⟨i, hi | hi⟩ := h
  · rw [hi]; intro k
    rw [abs_sub_comm]
    simpa [Pi.add_apply, add_sub_cancel_right] using xmh3_unit_abs_le i k
  · rw [hi]; intro k
    simpa [Pi.add_apply, add_sub_cancel_left] using xmh3_unit_abs_le i k

open Classical in
/-- The status of a vertex. -/
noncomputable def xmh3_st (A B D1 : Set (Site d)) (z : Site d) : ECSt :=
  if z ∈ A then .a else if z ∈ D1 then .d1 else if z ∈ B then
    (if ∃ c ∈ A, (lattice d).Adj c z then .d2 else .bi) else .o

section
variable {A B D1 : Set (Site d)} {z : Site d}

theorem xmh3_st_cases (hD1 : ∀ z ∈ D1, z ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c z)
    (z : Site d) :
    (z ∈ A ∧ xmh3_st A B D1 z = .a) ∨
    (z ∉ A ∧ z ∈ B ∧ z ∈ D1 ∧ xmh3_st A B D1 z = .d1) ∨
    (z ∉ A ∧ z ∈ B ∧ z ∉ D1 ∧ (∃ c ∈ A, (lattice d).Adj c z) ∧
      xmh3_st A B D1 z = .d2) ∨
    (z ∉ A ∧ z ∈ B ∧ ¬ (∃ c ∈ A, (lattice d).Adj c z) ∧ xmh3_st A B D1 z = .bi) ∨
    (z ∉ A ∧ z ∉ B ∧ xmh3_st A B D1 z = .o) := by
  classical
  unfold xmh3_st
  by_cases hA : z ∈ A
  · left; simp [hA]
  · by_cases hD : z ∈ D1
    · right; left; exact ⟨hA, (hD1 z hD).1, hD, by simp [hA, hD]⟩
    · by_cases hB : z ∈ B
      · by_cases hc : ∃ c ∈ A, (lattice d).Adj c z
        · right; right; left; exact ⟨hA, hB, hD, hc, by simp [hA, hD, hB, hc]⟩
        · right; right; right; left; exact ⟨hA, hB, hc, by simp [hA, hD, hB, hc]⟩
      · right; right; right; right; exact ⟨hA, hB, by simp [hA, hD, hB]⟩

theorem xmh3_st_adj (hclose : ∀ b ∈ B, ∀ z, (lattice d).Adj b z → z ∉ A → z ∈ B)
    (hD1 : ∀ z ∈ D1, z ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c z) {z w : Site d}
    (h : (lattice d).Adj z w) :
    ECSt.okAdj (xmh3_st A B D1 z) (xmh3_st A B D1 w) = true := by
  have hs : (lattice d).Adj w z := h.symm
  have hI : w ∈ A → z ∈ B → ∃ c ∈ A, (lattice d).Adj c z := fun hw _ => ⟨w, hw, hs⟩
  have hII : z ∈ A → w ∈ B → ∃ c ∈ A, (lattice d).Adj c w := fun hz _ => ⟨z, hz, h⟩
  have hIII : w ∈ B → z ∉ A → z ∈ B := fun hw hz => hclose w hw z hs hz
  have hIV : z ∈ B → w ∉ A → w ∈ B := fun hz hw => hclose z hz w h hw
  rcases xmh3_st_cases hD1 z with ⟨hzA, hz⟩ | ⟨hzA, hzB, _, hz⟩ | ⟨hzA, hzB, _, _, hz⟩ |
      ⟨hzA, hzB, hzN, hz⟩ | ⟨hzA, hzB, hz⟩ <;>
  rcases xmh3_st_cases hD1 w with ⟨hwA, hw⟩ | ⟨hwA, hwB, _, hw⟩ | ⟨hwA, hwB, _, _, hw⟩ |
      ⟨hwA, hwB, hwN, hw⟩ | ⟨hwA, hwB, hw⟩ <;>
  rw [hz, hw] <;>
  first
  | rfl
  | simp_all

theorem xmh3_st_near (hD1 : ∀ z ∈ D1, z ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c z)
    (hsep : ∀ x ∈ D1, ∀ y, y ∈ B → (∃ c ∈ A, (lattice d).Adj c y) → y ∉ D1 →
      ¬ xmh3_near x y)
    {z w : Site d} (h : xmh3_near z w) :
    ECSt.okNear (xmh3_st A B D1 z) (xmh3_st A B D1 w) = true := by
  have h' : xmh3_near w z := xmh3_near_symm h
  have hN1 : z ∈ D1 → w ∈ B → (∃ c ∈ A, (lattice d).Adj c w) → w ∉ D1 → False :=
    fun hz hwB hc hwD => hsep z hz w hwB hc hwD h
  have hN2 : w ∈ D1 → z ∈ B → (∃ c ∈ A, (lattice d).Adj c z) → z ∉ D1 → False :=
    fun hw hzB hc hzD => hsep w hw z hzB hc hzD h'
  rcases xmh3_st_cases hD1 z with ⟨hzA, hz⟩ | ⟨hzA, hzB, hzD1, hz⟩ | ⟨hzA, hzB, hzD2, hzc, hz⟩ |
      ⟨hzA, hzB, hzN, hz⟩ | ⟨hzA, hzB, hz⟩ <;>
  rcases xmh3_st_cases hD1 w with ⟨hwA, hw⟩ | ⟨hwA, hwB, hwD1, hw⟩ | ⟨hwA, hwB, hwD2, hwc, hw⟩ |
      ⟨hwA, hwB, hwN, hw⟩ | ⟨hwA, hwB, hw⟩ <;>
  rw [hz, hw] <;>
  first
  | rfl
  | simp_all

theorem xmh3_st_of_mem (hz : z ∈ A) : xmh3_st A B D1 z = .a := by
  classical
  unfold xmh3_st; simp [hz]

theorem xmh3_st_ne_a (hz : z ∉ A) : xmh3_st A B D1 z ≠ .a := by
  classical
  unfold xmh3_st; simp only [hz, if_false]; split_ifs <;> simp

theorem xmh3_st_d1 (hzA : z ∉ A) (hzD : z ∈ D1) : xmh3_st A B D1 z = .d1 := by
  classical
  unfold xmh3_st; simp [hzA, hzD]

theorem xmh3_st_d2 (hzA : z ∉ A) (hzD : z ∉ D1) (hzB : z ∈ B)
    (hc : ∃ c ∈ A, (lattice d).Adj c z) : xmh3_st A B D1 z = .d2 := by
  classical
  unfold xmh3_st; simp [hzA, hzD, hzB, hc]

end

/-! ### Chebyshev-nearness of the elementary displacements -/

theorem xmh3_unit_eq_zero_or_one (i k : Fin d) :
    (unit i : Site d) k = 0 ∨ (unit i : Site d) k = 1 := by
  by_cases h : k = i
  · right; rw [unit, h, Pi.single_eq_same]
  · left; rw [unit, Pi.single_eq_of_ne h]

theorem xmh3_unit_eq_one {i k : Fin d} (h : (unit i : Site d) k = 1) : k = i := by
  by_contra hk
  rw [unit, Pi.single_eq_of_ne hk] at h
  exact one_ne_zero h.symm

theorem xmh3_unit_sub_abs_le (i j k : Fin d) : |(unit i : Site d) k - unit j k| ≤ 1 := by
  rcases xmh3_unit_eq_zero_or_one i k with h | h <;>
    rcases xmh3_unit_eq_zero_or_one j k with h' | h' <;>
    rw [h, h'] <;> norm_num

theorem xmh3_unit_add_abs_le {i j : Fin d} (hij : i ≠ j) (k : Fin d) :
    |(unit i : Site d) k + unit j k| ≤ 1 := by
  rcases xmh3_unit_eq_zero_or_one i k with h | h <;>
    rcases xmh3_unit_eq_zero_or_one j k with h' | h'
  · rw [h, h']; norm_num
  · rw [h, h']; norm_num
  · rw [h, h']; norm_num
  · exact (hij ((xmh3_unit_eq_one h).symm.trans (xmh3_unit_eq_one h'))).elim

theorem xmh3_near_add_unit (p : Site d) (i : Fin d) : xmh3_near p (p + unit i) := by
  intro k
  rw [abs_sub_comm]
  simpa [Pi.add_apply, add_sub_cancel_right] using xmh3_unit_abs_le i k

theorem xmh3_near_add_units {i j : Fin d} (hij : i ≠ j) (p : Site d) :
    xmh3_near p (p + unit i + unit j) := by
  intro k
  rw [abs_sub_comm]
  have h : (p + unit i + unit j) k - p k = (unit i) k + (unit j) k := by
    simp only [Pi.add_apply]; ring
  rw [h]
  exact xmh3_unit_add_abs_le hij k

theorem xmh3_near_units (i j : Fin d) (p : Site d) :
    xmh3_near (p + unit i) (p + unit j) := by
  intro k
  have h : (p + unit i) k - (p + unit j) k = (unit i) k - (unit j) k := by
    simp only [Pi.add_apply]; ring
  rw [h]
  exact xmh3_unit_sub_abs_le i j k

theorem xmh3_near_add_unit_left (p : Site d) (i j : Fin d) :
    xmh3_near (p + unit i) (p + unit i + unit j) := by
  intro k
  rw [abs_sub_comm]
  have h : (p + unit i + unit j) k - (p + unit i) k = (unit j) k := by
    simp only [Pi.add_apply]; ring
  rw [h]
  exact xmh3_unit_abs_le j k

theorem xmh3_near_add_unit_right (p : Site d) (i j : Fin d) :
    xmh3_near (p + unit j) (p + unit i + unit j) := by
  intro k
  have h : (p + unit j) k - (p + unit i + unit j) k = -((unit i) k) := by
    simp only [Pi.add_apply]; ring
  rw [h, abs_neg]
  exact xmh3_unit_abs_le i k

/-! ### The boundary cocycle is a coboundary -/

section
variable {A B D1 : Set (Site d)}

theorem xmh3_coboundary (hclose : ∀ b ∈ B, ∀ z, (lattice d).Adj b z → z ∉ A → z ∈ B)
    (hD1 : ∀ z ∈ D1, z ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c z)
    (hsep : ∀ x ∈ D1, ∀ y, y ∈ B → (∃ c ∈ A, (lattice d).Adj c y) → y ∉ D1 →
      ¬ xmh3_near x y) :
    ∃ f : Site d → ZMod 2, ∀ u v, (lattice d).Adj u v →
      f u + f v = ECSt.cross (xmh3_st A B D1 u) (xmh3_st A B D1 v) := by
  have hclosed : ∀ i j, i ≠ j → ∀ p : Site d,
      ECSt.cross (xmh3_st A B D1 p) (xmh3_st A B D1 (p + unit i))
        + ECSt.cross (xmh3_st A B D1 (p + unit i)) (xmh3_st A B D1 (p + unit i + unit j))
      = ECSt.cross (xmh3_st A B D1 p) (xmh3_st A B D1 (p + unit j))
        + ECSt.cross (xmh3_st A B D1 (p + unit j)) (xmh3_st A B D1 (p + unit j + unit i)) := by
    intro i j hij p
    have h01 := xmh3_st_adj hclose hD1 (show (lattice d).Adj p (p + unit i) from ⟨i, Or.inl rfl⟩)
    have h13 := xmh3_st_adj hclose hD1
      (show (lattice d).Adj (p + unit i) (p + unit i + unit j) from ⟨j, Or.inl rfl⟩)
    have h02 := xmh3_st_adj hclose hD1 (show (lattice d).Adj p (p + unit j) from ⟨j, Or.inl rfl⟩)
    have h23 := xmh3_st_adj hclose hD1
      (show (lattice d).Adj (p + unit j) (p + unit i + unit j) from ⟨i, Or.inl (by abel)⟩)
    have n01 := xmh3_st_near hD1 hsep (xmh3_near_add_unit p i)
    have n02 := xmh3_st_near hD1 hsep (xmh3_near_add_unit p j)
    have n03 := xmh3_st_near hD1 hsep (xmh3_near_add_units hij p)
    have n12 := xmh3_st_near hD1 hsep (xmh3_near_units i j p)
    have n13 := xmh3_st_near hD1 hsep (xmh3_near_add_unit_left p i j)
    have n23 := xmh3_st_near hD1 hsep (xmh3_near_add_unit_right p i j)
    have hsq := ec_square_parity _ _ _ _ h01 h13 h02 h23 n01 n02 n03 n12 n13 n23
    rw [show (p + unit j + unit i : Site d) = p + unit i + unit j by abel]
    exact hsq
  obtain ⟨F, hF⟩ := xmh3_poincare d
    (fun i p => ECSt.cross (xmh3_st A B D1 p) (xmh3_st A B D1 (p + unit i))) hclosed
  refine ⟨F, ?_⟩
  intro u v huv
  obtain ⟨i, hi | hi⟩ := huv
  · rw [hi, hF i u, ← add_assoc, ec_zmod2_add_self, zero_add]
  · rw [hi, hF i v, add_assoc,
      add_comm (ECSt.cross (xmh3_st A B D1 v) (xmh3_st A B D1 (v + unit i))) (F v),
      ← add_assoc, ec_zmod2_add_self, zero_add, ECSt.cross_symm]

end

/-! ### The boundary is `*`-connected -/

theorem xmh3_boundaryStar (d : ℕ) : xmh_BoundaryStar d := by
  intro A B hA hB hdisj hclose x y hx hy
  classical
  by_contra hne
  set R : Site d → Site d → Prop := fun a b => (a ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c a) ∧
      (b ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c b) ∧ xmh_star a b
  set D1 : Set (Site d) := {z | (z ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c z) ∧ ReflTransGen R x z}
  have hyD1 : y ∉ D1 := fun h => hne h.2
  have hxD1 : x ∈ D1 := ⟨hx, ReflTransGen.refl⟩
  have hD1 : ∀ z ∈ D1, z ∈ B ∧ ∃ c ∈ A, (lattice d).Adj c z := fun z hz => hz.1
  have hsep : ∀ x' ∈ D1, ∀ y', y' ∈ B → (∃ c ∈ A, (lattice d).Adj c y') → y' ∉ D1 →
      ¬ xmh3_near x' y' := by
    intro x' hx' y' hy'B hy'c hy'D hnear
    apply hy'D
    refine ⟨⟨hy'B, hy'c⟩, hx'.2.tail ?_⟩
    exact ⟨hx'.1, ⟨hy'B, hy'c⟩, (fun heq => hy'D (heq ▸ hx')), hnear⟩
  obtain ⟨f, hf⟩ := xmh3_coboundary hclose hD1 hsep
  have char2 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  have hfA : ∀ u ∈ A, ∀ v ∈ A, f u = f v := by
    intro u hu v hv
    have hstep : ∀ v, ReflTransGen (fun a b => a ∈ A ∧ b ∈ A ∧ (lattice d).Adj a b) u v →
        f u = f v := by
      intro v h
      induction h with
      | refl => rfl
      | tail _ hbc ih =>
        refine ih.trans (char2 _ _ ?_)
        rw [hf _ _ hbc.2.2, xmh3_st_of_mem hbc.1, xmh3_st_of_mem hbc.2.1]
        rfl
    exact hstep v (hA u hu v hv)
  have hfB : ∀ u ∈ B, ∀ v ∈ B, f u = f v := by
    intro u hu v hv
    have hstep : ∀ v, ReflTransGen (fun a b => a ∈ B ∧ b ∈ B ∧ (lattice d).Adj a b) u v →
        f u = f v := by
      intro v h
      induction h with
      | refl => rfl
      | tail _ hbc ih =>
        refine ih.trans (char2 _ _ ?_)
        rw [hf _ _ hbc.2.2]
        exact ECSt.cross_eq_zero_of_ne_a (xmh3_st_ne_a fun h => hdisj _ h hbc.1)
          (xmh3_st_ne_a fun h => hdisj _ h hbc.2.1)
    exact hstep v (hB u hu v hv)
  obtain ⟨a1, ha1, hadj1⟩ := hx.2
  obtain ⟨a2, ha2, hadj2⟩ := hy.2
  have hxA : x ∉ A := fun h => hdisj _ h hx.1
  have hyA : y ∉ A := fun h => hdisj _ h hy.1
  have e1 : f a1 + f x = 1 := by
    rw [hf _ _ hadj1, xmh3_st_of_mem ha1, xmh3_st_d1 hxA hxD1]
    rfl
  have e2 : f a2 + f y = 0 := by
    rw [hf _ _ hadj2, xmh3_st_of_mem ha2, xmh3_st_d2 hyA hyD1 hy.1 ⟨a2, ha2, hadj2⟩]
    rfl
  have h3 := hfA a1 ha1 a2 ha2
  have h4 := hfB x hx.1 y hy.1
  rw [h3, h4, e2] at e1
  exact absurd e1 (by decide)

end Exploding
