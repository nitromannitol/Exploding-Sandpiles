/-
The box boundary-star theorem for the augmented graph: the box `cent d n` together with a
super-source adjacent to the negative face.  A minimal vertex cut of the two opposite faces
meets the negative face only in whole blocks, so its negative side can be disconnected; the
super-source restores connectedness, and the mod-two coboundary argument then shows that the
cut is `*`-connected, which yields the box-crossing star duality in dimension at least two.
-/
import Exploding.Support.ExtAPBoxPoincare
import Exploding.Support.ExtAPMinCut
import Exploding.Support.ExtAPMinCutDuality
import Exploding.Support.ExtMHProof5

namespace Exploding

open LatticeProb Relation
open scoped Classical

variable {d : ℕ}

/-! ### The status of a site in the augmented box -/

/-- A site is adjacent to the augmented set `A` when it is a lattice neighbour of `A` or
lies on the negative face (hence adjacent to the super-source). -/
def xmb_Bdry (Fneg A : Set (Site d)) (z : Site d) : Prop :=
  (∃ c ∈ A, (lattice d).Adj c z) ∨ z ∈ Fneg

/-- The status of a site of the box in the augmented graph. -/
noncomputable def xmb_st (Fneg A B D1 : Set (Site d)) (z : Site d) : ECSt :=
  if z ∈ A then .a else if z ∈ D1 then .d1 else if z ∈ B then
    (if xmb_Bdry Fneg A z then .d2 else .bi) else .o

theorem xmb_st_cases {Fneg A B D1 : Set (Site d)} {z : Site d}
    (hD1 : ∀ z ∈ D1, z ∈ B ∧ xmb_Bdry Fneg A z) :
    (z ∈ A ∧ xmb_st Fneg A B D1 z = .a) ∨
    (z ∉ A ∧ z ∈ B ∧ z ∈ D1 ∧ xmb_st Fneg A B D1 z = .d1) ∨
    (z ∉ A ∧ z ∈ B ∧ z ∉ D1 ∧ xmb_Bdry Fneg A z ∧ xmb_st Fneg A B D1 z = .d2) ∨
    (z ∉ A ∧ z ∈ B ∧ ¬ xmb_Bdry Fneg A z ∧ xmb_st Fneg A B D1 z = .bi) ∨
    (z ∉ A ∧ z ∉ B ∧ xmb_st Fneg A B D1 z = .o) := by
  classical
  unfold xmb_st
  by_cases hA : z ∈ A
  · left; simp [hA]
  · by_cases hD : z ∈ D1
    · right; left; exact ⟨hA, (hD1 z hD).1, hD, by simp [hA, hD]⟩
    · by_cases hB : z ∈ B
      · by_cases hc : xmb_Bdry Fneg A z
        · right; right; left; exact ⟨hA, hB, hD, hc, by simp [hA, hD, hB, hc]⟩
        · right; right; right; left; exact ⟨hA, hB, hc, by simp [hA, hD, hB, hc]⟩
      · right; right; right; right; exact ⟨hA, hB, by simp [hA, hD, hB]⟩

theorem xmb_st_of_mem {Fneg A B D1 : Set (Site d)} {z : Site d} (hz : z ∈ A) :
    xmb_st Fneg A B D1 z = .a := by
  classical
  unfold xmb_st; simp [hz]

theorem xmb_st_ne_a {Fneg A B D1 : Set (Site d)} {z : Site d} (hz : z ∉ A) :
    xmb_st Fneg A B D1 z ≠ .a := by
  classical
  unfold xmb_st; simp only [hz, if_false]; split_ifs <;> simp

theorem xmb_st_d1 {Fneg A B D1 : Set (Site d)} {z : Site d}
    (hzA : z ∉ A) (hzD : z ∈ D1) : xmb_st Fneg A B D1 z = .d1 := by
  classical
  unfold xmb_st; simp [hzA, hzD]

theorem xmb_st_d2 {Fneg A B D1 : Set (Site d)} {z : Site d}
    (hzA : z ∉ A) (hzD : z ∉ D1) (hzB : z ∈ B) (hc : xmb_Bdry Fneg A z) :
    xmb_st Fneg A B D1 z = .d2 := by
  classical
  unfold xmb_st; simp [hzA, hzD, hzB, hc]

/-! ### Local compatibility of the statuses -/

theorem xmb_st_adj (n : ℕ) {Fneg A B D1 : Set (Site d)}
    (hclose : ∀ b ∈ B, ∀ z, (lattice d).Adj b z → b ∈ cent d n → z ∈ cent d n →
      z ∉ A → z ∈ B)
    (hD1 : ∀ z ∈ D1, z ∈ B ∧ xmb_Bdry Fneg A z)
    {z w : Site d} (hzc : z ∈ cent d n) (hwc : w ∈ cent d n) (h : (lattice d).Adj z w) :
    ECSt.okAdj (xmb_st Fneg A B D1 z) (xmb_st Fneg A B D1 w) = true := by
  have hs : (lattice d).Adj w z := h.symm
  have hI : w ∈ A → z ∈ B → xmb_Bdry Fneg A z := fun hw _ => Or.inl ⟨w, hw, hs⟩
  have hII : z ∈ A → w ∈ B → xmb_Bdry Fneg A w := fun hz _ => Or.inl ⟨z, hz, h⟩
  have hIII : w ∈ B → z ∉ A → z ∈ B := fun hw hz => hclose w hw z hs hwc hzc hz
  have hIV : z ∈ B → w ∉ A → w ∈ B := fun hz hw => hclose z hz w h hzc hwc hw
  rcases xmb_st_cases (Fneg := Fneg) (A := A) (B := B) (D1 := D1) hD1 (z := z) with
    ⟨hzA, hz⟩ | ⟨hzA, hzB, _, hz⟩ | ⟨hzA, hzB, _, _, hz⟩ | ⟨hzA, hzB, hzN, hz⟩ |
      ⟨hzA, hzB, hz⟩ <;>
  rcases xmb_st_cases (Fneg := Fneg) (A := A) (B := B) (D1 := D1) hD1 (z := w) with
    ⟨hwA, hw⟩ | ⟨hwA, hwB, _, hw⟩ | ⟨hwA, hwB, _, _, hw⟩ | ⟨hwA, hwB, hwN, hw⟩ |
      ⟨hwA, hwB, hw⟩ <;>
  rw [hz, hw] <;>
  first
  | rfl
  | simp_all

theorem xmb_st_near {Fneg A B D1 : Set (Site d)}
    (hD1 : ∀ z ∈ D1, z ∈ B ∧ xmb_Bdry Fneg A z)
    (hsep : ∀ x ∈ D1, ∀ y, y ∈ B → xmb_Bdry Fneg A y → y ∉ D1 →
      ¬ xmh3_near x y)
    {z w : Site d} (h : xmh3_near z w) :
    ECSt.okNear (xmb_st Fneg A B D1 z) (xmb_st Fneg A B D1 w) = true := by
  have h' : xmh3_near w z := xmh3_near_symm h
  have hN1 : z ∈ D1 → w ∈ B → xmb_Bdry Fneg A w → w ∉ D1 → False :=
    fun hz hwB hc hwD => hsep z hz w hwB hc hwD h
  have hN2 : w ∈ D1 → z ∈ B → xmb_Bdry Fneg A z → z ∉ D1 → False :=
    fun hw hzB hc hzD => hsep w hw z hzB hc hzD h'
  rcases xmb_st_cases (Fneg := Fneg) (A := A) (B := B) (D1 := D1) hD1 (z := z) with
    ⟨hzA, hz⟩ | ⟨hzA, hzB, hzD1, hz⟩ | ⟨hzA, hzB, hzD2, hzc, hz⟩ |
      ⟨hzA, hzB, hzN, hz⟩ | ⟨hzA, hzB, hz⟩ <;>
  rcases xmb_st_cases (Fneg := Fneg) (A := A) (B := B) (D1 := D1) hD1 (z := w) with
    ⟨hwA, hw⟩ | ⟨hwA, hwB, hwD1, hw⟩ | ⟨hwA, hwB, hwD2, hwc, hw⟩ |
      ⟨hwA, hwB, hwN, hw⟩ | ⟨hwA, hwB, hw⟩ <;>
  rw [hz, hw] <;>
  first
  | rfl
  | simp_all

end Exploding
