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

/-! ### The negative face is connected -/

theorem xmb_adj_update_succ (z : Site d) (j : Fin d) (s : ℤ) :
    (lattice d).Adj (Function.update z j s) (Function.update z j (s + 1)) := by
  refine ⟨j, Or.inl ?_⟩
  ext k
  by_cases hk : k = j
  · subst hk; simp [unit]
  · simp [Function.update_of_ne hk, unit, Pi.single_eq_of_ne hk]

theorem xmb_face_update_mem {n : ℕ} {i : Fin d} {z : Site d} (hz : z ∈ xmc_Fneg d n i)
    {j : Fin d} (hji : j ≠ i) {s : ℤ} (hs : |s| ≤ (n : ℤ)) :
    Function.update z j s ∈ xmc_Fneg d n i := by
  refine ⟨?_, ?_⟩
  · intro k
    by_cases hk : k = j
    · subst hk; rw [Function.update_self]; exact hs
    · rw [Function.update_of_ne hk]; exact hz.1 k
  · rw [Function.update_of_ne (Ne.symm hji)]; exact hz.2

theorem xmb_face_path_up {n : ℕ} {i : Fin d} {z : Site d} (hz : z ∈ xmc_Fneg d n i)
    {j : Fin d} (hji : j ≠ i) {b : ℤ} (hb : |b| ≤ (n : ℤ)) :
    ReflTransGen (fun a b => a ∈ xmc_Fneg d n i ∧ b ∈ xmc_Fneg d n i ∧ (lattice d).Adj a b)
      z (Function.update z j b) := by
  have hzj : |z j| ≤ (n : ℤ) := hz.1 j
  have hzj_lo : -(n : ℤ) ≤ z j := (abs_le.mp hzj).1
  have hzj_hi : z j ≤ (n : ℤ) := (abs_le.mp hzj).2
  have hb_lo : -(n : ℤ) ≤ b := (abs_le.mp hb).1
  have hb_hi : b ≤ (n : ℤ) := (abs_le.mp hb).2
  rcases le_total (z j) b with hab | hba
  · have key : ∀ k : ℕ, (z j) + (k : ℤ) ≤ b →
        ReflTransGen (fun a b => a ∈ xmc_Fneg d n i ∧ b ∈ xmc_Fneg d n i ∧
          (lattice d).Adj a b) z (Function.update z j ((z j) + (k : ℤ))) := by
      intro k
      induction k with
      | zero => intro _; simpa using ReflTransGen.refl
      | succ k ih =>
        intro hk
        have hk' : (z j) + (k : ℤ) ≤ b := by omega
        have hb1 : |(z j) + (k : ℤ)| ≤ (n : ℤ) := by
          rw [abs_le]; constructor <;> omega
        have hb2 : |(z j) + (k : ℤ) + 1| ≤ (n : ℤ) := by
          rw [abs_le]; constructor <;> omega
        have hstep : (fun a b => a ∈ xmc_Fneg d n i ∧ b ∈ xmc_Fneg d n i ∧
            (lattice d).Adj a b) (Function.update z j ((z j) + (k : ℤ)))
            (Function.update z j ((z j) + ((k + 1 : ℕ) : ℤ))) := by
          rw [show (z j) + ((k + 1 : ℕ) : ℤ) = (z j) + (k : ℤ) + 1 by push_cast; ring]
          exact ⟨xmb_face_update_mem hz hji hb1, xmb_face_update_mem hz hji hb2,
            xmb_adj_update_succ z j ((z j) + (k : ℤ))⟩
        exact (ih hk').tail hstep
    have hb' : b = (z j) + ((b - z j).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (by omega)]; ring
    rw [hb']
    exact key ((b - z j).toNat) (by rw [Int.toNat_of_nonneg (by omega)]; omega)
  · have key : ∀ k : ℕ, b ≤ (z j) - (k : ℤ) →
        ReflTransGen (fun a b => a ∈ xmc_Fneg d n i ∧ b ∈ xmc_Fneg d n i ∧
          (lattice d).Adj a b) z (Function.update z j ((z j) - (k : ℤ))) := by
      intro k
      induction k with
      | zero => intro _; simpa using ReflTransGen.refl
      | succ k ih =>
        intro hk
        have hk' : b ≤ (z j) - (k : ℤ) := by omega
        have hb1 : |(z j) - (k : ℤ)| ≤ (n : ℤ) := by
          rw [abs_le]; constructor <;> omega
        have hb2 : |(z j) - (k : ℤ) - 1| ≤ (n : ℤ) := by
          rw [abs_le]; constructor <;> omega
        have hstep : (fun a b => a ∈ xmc_Fneg d n i ∧ b ∈ xmc_Fneg d n i ∧
            (lattice d).Adj a b) (Function.update z j ((z j) - (k : ℤ)))
            (Function.update z j ((z j) - ((k + 1 : ℕ) : ℤ))) := by
          rw [show (z j) - ((k + 1 : ℕ) : ℤ) = (z j) - (k : ℤ) - 1 by push_cast; ring]
          have hadj := xmb_adj_update_succ z j ((z j) - (k : ℤ) - 1)
          rw [show (z j) - (k : ℤ) - 1 + 1 = (z j) - (k : ℤ) by ring] at hadj
          exact ⟨xmb_face_update_mem hz hji hb1, xmb_face_update_mem hz hji hb2,
            hadj.symm⟩
        exact (ih hk').tail hstep
    have hb' : b = (z j) - ((z j - b).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (by omega)]; ring
    rw [hb']
    exact key ((z j - b).toNat) (by rw [Int.toNat_of_nonneg (by omega)]; omega)

theorem xmb_Fneg_connected (n : ℕ) (i : Fin d) {u v : Site d}
    (hu : u ∈ xmc_Fneg d n i) (hv : v ∈ xmc_Fneg d n i) :
    ReflTransGen (fun a b => a ∈ xmc_Fneg d n i ∧ b ∈ xmc_Fneg d n i ∧ (lattice d).Adj a b)
      u v := by
  have key : ∀ T : Finset (Fin d), i ∉ T →
      ReflTransGen (fun a b => a ∈ xmc_Fneg d n i ∧ b ∈ xmc_Fneg d n i ∧
        (lattice d).Adj a b) u (fun j => if j ∈ T then v j else u j) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      simpa only [Finset.notMem_empty, if_false] using
        (ReflTransGen.refl : ReflTransGen (fun a b => a ∈ xmc_Fneg d n i ∧
          b ∈ xmc_Fneg d n i ∧ (lattice d).Adj a b) u u)
    | insert j T' hj ih =>
      intro hiT
      have hiT' : i ∉ T' := fun h => hiT (Finset.mem_insert_of_mem h)
      have hji : j ≠ i := fun h => hiT (h ▸ Finset.mem_insert_self j T')
      have hprev := ih hiT'
      have hs'mem : (fun k => if k ∈ T' then v k else u k) ∈ xmc_Fneg d n i := by
        refine ⟨?_, ?_⟩
        · intro k
          show |(if k ∈ T' then v k else u k)| ≤ (n : ℤ)
          by_cases hk : k ∈ T'
          · rw [if_pos hk]; exact hv.1 k
          · rw [if_neg hk]; exact hu.1 k
        · show (if i ∈ T' then v i else u i) = -(n : ℤ)
          rw [if_neg hiT']
          exact hu.2
      have hfinal : (fun k => if k ∈ insert j T' then v k else u k)
          = Function.update (fun k => if k ∈ T' then v k else u k) j (v j) := by
        funext k
        by_cases hk : k = j
        · subst hk; rw [Function.update_self, if_pos (Finset.mem_insert_self k T')]
        · rw [Function.update_of_ne hk]
          by_cases hkT : k ∈ T'
          · rw [if_pos (Finset.mem_insert_of_mem hkT), if_pos hkT]
          · rw [if_neg (fun h => hkT ((Finset.mem_insert.mp h).resolve_left hk)), if_neg hkT]
      rw [hfinal]
      exact hprev.trans (xmb_face_path_up hs'mem hji (b := v j) (hv.1 j))
  have hfinal : (fun j => if j ∈ (Finset.univ.erase i) then v j
      else u j) = v := by
    funext k
    by_cases hk : k = i
    · rw [hk, if_neg (Finset.notMem_erase i Finset.univ)]
      exact hu.2.trans hv.2.symm
    · rw [if_pos (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)]
  rw [← hfinal]
  exact key (Finset.univ.erase i) (Finset.notMem_erase i Finset.univ)

/-! ### The box coboundary for the augmented status -/

theorem xmb_add_units_mem_cent {n : ℕ} {p : Site d} {i j : Fin d} (hij : i ≠ j)
    (hpi : p + unit i ∈ cent d n) (hpj : p + unit j ∈ cent d n) :
    p + unit i + unit j ∈ cent d n := by
  intro k
  by_cases hki : k = i
  · have he : (p + unit i + unit j) k = (p + unit i) i := by
      rw [hki]
      simp only [Pi.add_apply, unit]
      rw [Pi.single_eq_same, Pi.single_eq_of_ne hij, add_zero]
    rw [he]; exact hpi i
  · by_cases hkj : k = j
    · have he : (p + unit i + unit j) k = (p + unit j) j := by
        rw [hkj]
        simp only [Pi.add_apply, unit]
        rw [Pi.single_eq_of_ne (Ne.symm hij), add_zero, Pi.single_eq_same]
      rw [he]; exact hpj j
    · have he : (p + unit i + unit j) k = (p + unit i) k := by
        simp only [Pi.add_apply, unit]
        rw [Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj, add_zero]
      rw [he]; exact hpi k

theorem xmb_add_self_zmod2 (x : ZMod 2) : x + x = 0 :=
  (add_eq_zero_iff_eq_neg).mpr (CharTwo.neg_eq x).symm

theorem xmb_cross_eq_of_sts {s t : ECSt}
    (hs : s = .a ∨ s = .d1 ∨ s = .d2) (ht : t = .a ∨ t = .d1 ∨ t = .d2)
    (hno : ¬ (s = .d1 ∧ t = .d2) ∧ ¬ (s = .d2 ∧ t = .d1)) :
    ECSt.cross s t = ECSt.cross .a s + ECSt.cross .a t := by
  rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
    first
    | (exfalso; first | exact absurd ⟨rfl, rfl⟩ hno.1 | exact absurd ⟨rfl, rfl⟩ hno.2)
    | decide

theorem xmb_cross_triangle_of_sts {s t : ECSt}
    (hs : s = .a ∨ s = .d1 ∨ s = .d2) (ht : t = .a ∨ t = .d1 ∨ t = .d2)
    (hno : ¬ (s = .d1 ∧ t = .d2) ∧ ¬ (s = .d2 ∧ t = .d1)) :
    ECSt.cross .a s + ECSt.cross s t + ECSt.cross .a t = 0 := by
  rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
    first
    | (exfalso; first | exact absurd ⟨rfl, rfl⟩ hno.1 | exact absurd ⟨rfl, rfl⟩ hno.2)
    | decide

theorem xmb_coboundary (n : ℕ) {Fneg A B D1 : Set (Site d)}
    (hclose : ∀ b ∈ B, ∀ z, (lattice d).Adj b z → b ∈ cent d n → z ∈ cent d n →
      z ∉ A → z ∈ B)
    (hD1 : ∀ z ∈ D1, z ∈ B ∧ xmb_Bdry Fneg A z)
    (hsep : ∀ x ∈ D1, ∀ y, y ∈ B → xmb_Bdry Fneg A y → y ∉ D1 →
      ¬ xmh3_near x y) :
    ∃ f : Site d → ZMod 2, ∀ u v, (lattice d).Adj u v → u ∈ cent d n → v ∈ cent d n →
      f u + f v = ECSt.cross (xmb_st Fneg A B D1 u) (xmb_st Fneg A B D1 v) := by
  have hclosed : ∀ i j, i ≠ j → ∀ p : Site d, p ∈ cent d n → p + unit i ∈ cent d n →
      p + unit j ∈ cent d n →
      ECSt.cross (xmb_st Fneg A B D1 p) (xmb_st Fneg A B D1 (p + unit i))
        + ECSt.cross (xmb_st Fneg A B D1 (p + unit i))
            (xmb_st Fneg A B D1 (p + unit i + unit j))
      = ECSt.cross (xmb_st Fneg A B D1 p) (xmb_st Fneg A B D1 (p + unit j))
        + ECSt.cross (xmb_st Fneg A B D1 (p + unit j))
            (xmb_st Fneg A B D1 (p + unit j + unit i)) := by
    intro i j hij p hp hpi hpj
    have hpij : p + unit i + unit j ∈ cent d n := xmb_add_units_mem_cent hij hpi hpj
    have h01 := xmb_st_adj n hclose hD1 hp hpi (show (lattice d).Adj p (p + unit i) from ⟨i, Or.inl rfl⟩)
    have h13 := xmb_st_adj n hclose hD1 hpi hpij
      (show (lattice d).Adj (p + unit i) (p + unit i + unit j) from ⟨j, Or.inl rfl⟩)
    have h02 := xmb_st_adj n hclose hD1 hp hpj (show (lattice d).Adj p (p + unit j) from ⟨j, Or.inl rfl⟩)
    have h23 := xmb_st_adj n hclose hD1 hpj hpij
      (show (lattice d).Adj (p + unit j) (p + unit i + unit j) from ⟨i, Or.inl (by abel)⟩)
    have n01 := xmb_st_near hD1 hsep (xmh3_near_add_unit p i)
    have n02 := xmb_st_near hD1 hsep (xmh3_near_add_unit p j)
    have n03 := xmb_st_near hD1 hsep (xmh3_near_add_units hij p)
    have n12 := xmb_st_near hD1 hsep (xmh3_near_units i j p)
    have n13 := xmb_st_near hD1 hsep (xmh3_near_add_unit_left p i j)
    have n23 := xmb_st_near hD1 hsep (xmh3_near_add_unit_right p i j)
    have hsq := ec_square_parity _ _ _ _ h01 h13 h02 h23 n01 n02 n03 n12 n13 n23
    rw [show (p + unit j + unit i : Site d) = p + unit i + unit j by abel]
    exact hsq
  obtain ⟨F, hF⟩ := xmb_boxPoincare n d
    (fun i p => ECSt.cross (xmb_st Fneg A B D1 p) (xmb_st Fneg A B D1 (p + unit i))) hclosed
  refine ⟨F, ?_⟩
  intro u v huv huc hvc
  rcases huv with ⟨i, hi | hi⟩
  · subst hi
    rw [hF i u huc hvc, ← add_assoc, ec_zmod2_add_self, zero_add]
  · subst hi
    rw [hF i v hvc huc, add_assoc, add_comm (ECSt.cross (xmb_st Fneg A B D1 v)
        (xmb_st Fneg A B D1 (v + unit i))) (F v), ← add_assoc, ec_zmod2_add_self, zero_add,
      ECSt.cross_symm]

/-! ### The coboundary of the augmented graph -/

theorem xmb_st_ne_d1_of_notMem {Fneg A B D1 : Set (Site d)} {y : Site d}
    (hyD : y ∉ D1) : xmb_st Fneg A B D1 y ≠ .d1 := by
  unfold xmb_st
  simp only [hyD, if_false]
  split_ifs <;> simp

theorem xmb_st_d2_spec {Fneg A B D1 : Set (Site d)} {y : Site d}
    (hy : xmb_st Fneg A B D1 y = .d2) : y ∈ B ∧ xmb_Bdry Fneg A y ∧ y ∉ D1 := by
  unfold xmb_st at hy
  by_cases hyA : y ∈ A
  · simp [hyA] at hy
  · rw [if_neg hyA] at hy
    by_cases hyD : y ∈ D1
    · simp [hyD] at hy
    · rw [if_neg hyD] at hy
      by_cases hyB : y ∈ B
      · rw [if_pos hyB] at hy
        by_cases hbd : xmb_Bdry Fneg A y
        · simp [hbd] at hy; exact ⟨hyB, hbd, hyD⟩
        · simp [hbd] at hy
      · simp [hyB] at hy

theorem xmb_g_loc (n : ℕ) {Fneg A B D1 : Set (Site d)}
    (hsep : ∀ x ∈ D1, ∀ y, y ∈ B → xmb_Bdry Fneg A y → y ∉ D1 →
      ¬ xmh3_near x y)
    (hcover : ∀ z, z ∈ cent d n → z ∉ A → z ∈ B)
    (hFcent : Fneg ⊆ cent d n)
    {fb : Site d → ZMod 2}
    (hfb : ∀ u v, (lattice d).Adj u v → u ∈ cent d n → v ∈ cent d n →
      fb u + fb v = ECSt.cross (xmb_st Fneg A B D1 u) (xmb_st Fneg A B D1 v))
    {z w : Site d} (hz : z ∈ Fneg) (hw : w ∈ Fneg) (hzw : (lattice d).Adj z w) :
    fb z + ECSt.cross .a (xmb_st Fneg A B D1 z)
      = fb w + ECSt.cross .a (xmb_st Fneg A B D1 w) := by
  have hzc : z ∈ cent d n := hFcent hz
  have hwc : w ∈ cent d n := hFcent hw
  have hfb' := hfb z w hzw hzc hwc
  have htz : xmb_st Fneg A B D1 z = .a ∨ xmb_st Fneg A B D1 z = .d1 ∨
      xmb_st Fneg A B D1 z = .d2 := by
    by_cases hzA : z ∈ A
    · exact Or.inl (xmb_st_of_mem hzA)
    · by_cases hzD : z ∈ D1
      · exact Or.inr (Or.inl (xmb_st_d1 hzA hzD))
      · exact Or.inr (Or.inr (xmb_st_d2 hzA hzD (hcover z hzc hzA) (Or.inr hz)))
  have htw : xmb_st Fneg A B D1 w = .a ∨ xmb_st Fneg A B D1 w = .d1 ∨
      xmb_st Fneg A B D1 w = .d2 := by
    by_cases hwA : w ∈ A
    · exact Or.inl (xmb_st_of_mem hwA)
    · by_cases hwD : w ∈ D1
      · exact Or.inr (Or.inl (xmb_st_d1 hwA hwD))
      · exact Or.inr (Or.inr (xmb_st_d2 hwA hwD (hcover w hwc hwA) (Or.inr hw)))
  have hno : ¬ (xmb_st Fneg A B D1 z = .d1 ∧ xmb_st Fneg A B D1 w = .d2) ∧
      ¬ (xmb_st Fneg A B D1 z = .d2 ∧ xmb_st Fneg A B D1 w = .d1) := by
    constructor
    · rintro ⟨h1, h2⟩
      have hzD : z ∈ D1 := by_contra fun h => xmb_st_ne_d1_of_notMem h h1
      have hwB := xmb_st_d2_spec h2
      exact hsep z hzD w hwB.1 hwB.2.1 hwB.2.2 (xmh3_near_of_adj hzw)
    · rintro ⟨h1, h2⟩
      have hwD : w ∈ D1 := by_contra fun h => xmb_st_ne_d1_of_notMem h h2
      have hzB := xmb_st_d2_spec h1
      exact hsep w hwD z hzB.1 hzB.2.1 hzB.2.2 (xmh3_near_symm (xmh3_near_of_adj hzw))
  have hB : ECSt.cross (xmb_st Fneg A B D1 z) (xmb_st Fneg A B D1 w)
      = ECSt.cross .a (xmb_st Fneg A B D1 z) + ECSt.cross .a (xmb_st Fneg A B D1 w) :=
    xmb_cross_eq_of_sts htz htw hno
  have h1 : fb z + fb w
      = ECSt.cross .a (xmb_st Fneg A B D1 z) + ECSt.cross .a (xmb_st Fneg A B D1 w) :=
    hfb'.trans hB
  have hsum : (fb z + ECSt.cross .a (xmb_st Fneg A B D1 z))
      + (fb w + ECSt.cross .a (xmb_st Fneg A B D1 w)) = 0 := by
    rw [show (fb z + ECSt.cross .a (xmb_st Fneg A B D1 z))
          + (fb w + ECSt.cross .a (xmb_st Fneg A B D1 w))
        = (fb z + fb w) + (ECSt.cross .a (xmb_st Fneg A B D1 z)
          + ECSt.cross .a (xmb_st Fneg A B D1 w)) by abel, h1, xmb_add_self_zmod2]
  have h2 := (add_eq_zero_iff_eq_neg).mp hsum
  rwa [CharTwo.neg_eq] at h2

theorem xmb_coboundary_aug (n : ℕ) (i : Fin d) {Fneg A B D1 : Set (Site d)}
    (hFneg : Fneg = xmc_Fneg d n i)
    (hclose : ∀ b ∈ B, ∀ z, (lattice d).Adj b z → b ∈ cent d n → z ∈ cent d n →
      z ∉ A → z ∈ B)
    (hD1 : ∀ z ∈ D1, z ∈ B ∧ xmb_Bdry Fneg A z)
    (hsep : ∀ x ∈ D1, ∀ y, y ∈ B → xmb_Bdry Fneg A y → y ∉ D1 →
      ¬ xmh3_near x y)
    (hcover : ∀ z, z ∈ cent d n → z ∉ A → z ∈ B)
    {z0 : Site d} (hz0 : z0 ∈ xmc_Fneg d n i) :
    ∃ f : Option (Site d) → ZMod 2,
      (∀ u v, (lattice d).Adj u v → u ∈ cent d n → v ∈ cent d n →
        f (some u) + f (some v) = ECSt.cross (xmb_st Fneg A B D1 u) (xmb_st Fneg A B D1 v)) ∧
      (∀ z ∈ xmc_Fneg d n i, f none + f (some z) = ECSt.cross .a (xmb_st Fneg A B D1 z)) := by
  subst hFneg
  obtain ⟨fb, hfb⟩ := xmb_coboundary n hclose hD1 hsep
  have hgconst : ∀ z ∈ xmc_Fneg d n i,
      fb z + ECSt.cross .a (xmb_st (xmc_Fneg d n i) A B D1 z)
        = fb z0 + ECSt.cross .a (xmb_st (xmc_Fneg d n i) A B D1 z0) := by
    intro z hz
    have hpath := xmb_Fneg_connected n i hz hz0
    induction hpath with
    | refl => rfl
    | tail hpref hb ih =>
      exact (ih hb.1).trans (xmb_g_loc n hsep hcover (fun z hz => hz.1) hfb hb.1 hb.2.1 hb.2.2)
  refine ⟨fun o => o.elim (fb z0 + ECSt.cross .a (xmb_st (xmc_Fneg d n i) A B D1 z0))
    (fun z => fb z), ?_, ?_⟩
  · intro u v huv huc hvc; exact hfb u v huv huc hvc
  · intro z hz
    have hgc := hgconst z hz
    show (fb z0 + ECSt.cross .a (xmb_st (xmc_Fneg d n i) A B D1 z0)) + fb z
      = ECSt.cross .a (xmb_st (xmc_Fneg d n i) A B D1 z)
    have hsum : ((fb z0 + ECSt.cross .a (xmb_st (xmc_Fneg d n i) A B D1 z0)) + fb z)
        + ECSt.cross .a (xmb_st (xmc_Fneg d n i) A B D1 z) = 0 := by
      rw [show ((fb z0 + ECSt.cross .a (xmb_st (xmc_Fneg d n i) A B D1 z0)) + fb z)
            + ECSt.cross .a (xmb_st (xmc_Fneg d n i) A B D1 z)
          = ((fb z + ECSt.cross .a (xmb_st (xmc_Fneg d n i) A B D1 z)) + fb z)
            + ECSt.cross .a (xmb_st (xmc_Fneg d n i) A B D1 z) by rw [← hgc]]
      rw [show ((fb z + ECSt.cross .a (xmb_st (xmc_Fneg d n i) A B D1 z)) + fb z)
            + ECSt.cross .a (xmb_st (xmc_Fneg d n i) A B D1 z)
          = (fb z + fb z) + (ECSt.cross .a (xmb_st (xmc_Fneg d n i) A B D1 z)
            + ECSt.cross .a (xmb_st (xmc_Fneg d n i) A B D1 z)) by abel,
        xmb_add_self_zmod2, xmb_add_self_zmod2, zero_add]
    have h2 := (add_eq_zero_iff_eq_neg).mp hsum
    rwa [CharTwo.neg_eq] at h2

/-! ### The boundary of the augmented box is `*`-connected -/

theorem xmb_boundaryStar (n : ℕ) (i : Fin d) {A B : Set (Site d)}
    (hAcent : ∀ z ∈ A, z ∈ cent d n)
    (hB_eq : ∀ z, z ∈ B ↔ (z ∈ cent d n ∧ z ∉ A))
    (hBcon : ∀ u ∈ B, ∀ v ∈ B,
      ReflTransGen (fun a b => a ∈ B ∧ b ∈ B ∧ (lattice d).Adj a b) u v)
    (hAmeets : ∀ u ∈ A, ∃ f1 ∈ A, f1 ∈ xmc_Fneg d n i ∧
      ReflTransGen (fun a b => a ∈ A ∧ b ∈ A ∧ (lattice d).Adj a b) u f1)
    {z0 : Site d} (hz0 : z0 ∈ xmc_Fneg d n i)
    (x y : Site d)
    (hx : x ∈ B ∧ xmb_Bdry (xmc_Fneg d n i) A x)
    (hy : y ∈ B ∧ xmb_Bdry (xmc_Fneg d n i) A y) :
    ReflTransGen (fun a b => (a ∈ B ∧ xmb_Bdry (xmc_Fneg d n i) A a) ∧
      (b ∈ B ∧ xmb_Bdry (xmc_Fneg d n i) A b) ∧ xmh_star a b) x y := by
  classical
  by_contra hne
  set R : Site d → Site d → Prop := fun a b =>
    (a ∈ B ∧ xmb_Bdry (xmc_Fneg d n i) A a) ∧
    (b ∈ B ∧ xmb_Bdry (xmc_Fneg d n i) A b) ∧ xmh_star a b with hR
  set D1 : Set (Site d) := {z | (z ∈ B ∧ xmb_Bdry (xmc_Fneg d n i) A z) ∧
    ReflTransGen R x z} with hD1def
  have hyD1 : y ∉ D1 := fun h => hne h.2
  have hxD1 : x ∈ D1 := ⟨hx, ReflTransGen.refl⟩
  have hD1 : ∀ z ∈ D1, z ∈ B ∧ xmb_Bdry (xmc_Fneg d n i) A z := fun z hz => hz.1
  have hsep : ∀ x' ∈ D1, ∀ y', y' ∈ B → xmb_Bdry (xmc_Fneg d n i) A y' → y' ∉ D1 →
      ¬ xmh3_near x' y' := by
    intro x' hx' y' hy'B hy'c hy'D hnear
    apply hy'D
    refine ⟨⟨hy'B, hy'c⟩, hx'.2.tail ?_⟩
    exact ⟨hx'.1, ⟨hy'B, hy'c⟩, (fun heq => hy'D (heq ▸ hx')), hnear⟩
  have hclose : ∀ b ∈ B, ∀ z, (lattice d).Adj b z → b ∈ cent d n → z ∈ cent d n →
      z ∉ A → z ∈ B :=
    fun b _ z _ _ hzc hzA => (hB_eq z).mpr ⟨hzc, hzA⟩
  obtain ⟨f, hfbox, hfsigma⟩ := xmb_coboundary_aug n i rfl hclose hD1 hsep
    (fun z hz hzA => (hB_eq z).mpr ⟨hz, hzA⟩) hz0
  have char2 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  have hxA : x ∉ A := ((hB_eq x).mp hx.1).2
  have hyA : y ∉ A := ((hB_eq y).mp hy.1).2
  have hstx : xmb_st (xmc_Fneg d n i) A B D1 x = .d1 := xmb_st_d1 hxA hxD1
  have hsty : xmb_st (xmc_Fneg d n i) A B D1 y = .d2 :=
    xmb_st_d2 hyA hyD1 hy.1 hy.2
  have hfB : ∀ u ∈ B, ∀ v ∈ B, f (some u) = f (some v) := by
    intro u hu v hv
    have hstep : ∀ v, ReflTransGen (fun a b => a ∈ B ∧ b ∈ B ∧ (lattice d).Adj a b) u v →
        f (some u) = f (some v) := by
      intro v h
      induction h with
      | refl => rfl
      | tail _ hbc ih =>
        refine ih.trans (char2 _ _ ?_)
        rw [hfbox _ _ hbc.2.2 ((hB_eq _).mp hbc.1).1 ((hB_eq _).mp hbc.2.1).1,
          ECSt.cross_eq_zero_of_ne_a (xmb_st_ne_a ((hB_eq _).mp hbc.1).2)
            (xmb_st_ne_a ((hB_eq _).mp hbc.2.1).2)]
    exact hstep v (hBcon u hu v hv)
  have hfA_none : ∀ c ∈ A, f (some c) = f none := by
    intro c hc
    obtain ⟨f1, hf1A, hf1F, hpath⟩ := hAmeets c hc
    have hpath' : f (some c) = f (some f1) := by
      have hstepA : ∀ a b, a ∈ A → b ∈ A → (lattice d).Adj a b →
          f (some a) = f (some b) := by
        intro a b ha hb hab
        have h := hfbox a b hab (hAcent a ha) (hAcent b hb)
        rw [xmb_st_of_mem ha, xmb_st_of_mem hb] at h
        exact char2 _ _ h
      have key : ∀ w, ReflTransGen (fun a b => a ∈ A ∧ b ∈ A ∧ (lattice d).Adj a b) c w →
          f (some c) = f (some w) := by
        intro w hw
        induction hw with
        | refl => rfl
        | tail _ hbc ih => exact ih.trans (hstepA _ _ hbc.1 hbc.2.1 hbc.2.2)
      exact key f1 hpath
    have hsig := hfsigma f1 hf1F
    rw [xmb_st_of_mem hf1A] at hsig
    exact hpath'.trans (char2 _ _ hsig).symm
  have hfA : ∀ u ∈ A, ∀ v ∈ A, f (some u) = f (some v) :=
    fun u hu v hv => (hfA_none u hu).trans (hfA_none v hv).symm
  have hA_opt : ∀ u v : Option (Site d),
      (u = none ∨ ∃ c, u = some c ∧ c ∈ A) →
      (v = none ∨ ∃ c, v = some c ∧ c ∈ A) → f u = f v := by
    intro u v hu hv
    rcases hu with rfl | ⟨cu, rfl, hcu⟩ <;> rcases hv with rfl | ⟨cv, rfl, hcv⟩
    · rfl
    · exact (hfA_none cv hcv).symm
    · exact hfA_none cu hcu
    · exact hfA cu hcu cv hcv
  obtain ⟨a1, ha1, he1⟩ : ∃ a1 : Option (Site d),
      (a1 = none ∨ ∃ c, a1 = some c ∧ c ∈ A) ∧
      f a1 + f (some x) = ECSt.cross .a (xmb_st (xmc_Fneg d n i) A B D1 x) := by
    rcases hx.2 with ⟨c, hcA, hadj⟩ | hxF
    · refine ⟨some c, Or.inr ⟨c, rfl, hcA⟩, ?_⟩
      rw [hfbox c x hadj (hAcent c hcA) ((hB_eq x).mp hx.1).1, xmb_st_of_mem hcA]
    · exact ⟨none, Or.inl rfl, by rw [hfsigma x hxF]⟩
  obtain ⟨a2, ha2, he2⟩ : ∃ a2 : Option (Site d),
      (a2 = none ∨ ∃ c, a2 = some c ∧ c ∈ A) ∧
      f a2 + f (some y) = ECSt.cross .a (xmb_st (xmc_Fneg d n i) A B D1 y) := by
    rcases hy.2 with ⟨c, hcA, hadj⟩ | hyF
    · refine ⟨some c, Or.inr ⟨c, rfl, hcA⟩, ?_⟩
      rw [hfbox c y hadj (hAcent c hcA) ((hB_eq y).mp hy.1).1, xmb_st_of_mem hcA]
    · exact ⟨none, Or.inl rfl, by rw [hfsigma y hyF]⟩
  have he1' : f a1 + f (some x) = 1 := by rw [he1, hstx]; rfl
  have he2' : f a2 + f (some y) = 0 := by rw [he2, hsty]; rfl
  have h3 : f a1 = f a2 := hA_opt a1 a2 ha1 ha2
  have h4 : f (some x) = f (some y) := hfB x hx.1 y hy.1
  rw [h3, h4, he2'] at he1'
  exact absurd he1' (by decide)

end Exploding
