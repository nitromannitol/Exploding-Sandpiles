/-
The dynamics of Proposition 7.1 in the plane of tiles: if every constant-`n` pile
stabilizes, the completely toppled tiles of the plane form a finite set containing the
origin tile, and every tile next to it fails to be box-crossing.
-/
import Exploding.Support.ECProofDyn
import Exploding.Support.ECProofTop

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The embedding of the plane `ℤ × ℤ` into the first two coordinates of `ℤ^d`. -/
def ec_emb (d : ℕ) (z : ℤ × ℤ) : Site d :=
  fun i => if i.val = 0 then z.1 else if i.val = 1 then z.2 else 0

theorem ec_emb_add (z w : ℤ × ℤ) : ec_emb d (z + w) = ec_emb d z + ec_emb d w := by
  funext i
  simp only [ec_emb, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  split_ifs <;> ring

theorem ec_emb_neg (z : ℤ × ℤ) : ec_emb d (-z) = -ec_emb d z := by
  funext i
  simp only [ec_emb, Prod.fst_neg, Prod.snd_neg, Pi.neg_apply]
  split_ifs <;> ring

theorem ec_emb_zero : ec_emb d (0, 0) = 0 := by
  funext i
  simp only [ec_emb]
  split_ifs <;> rfl

theorem ec_emb_e0 (hd : 2 ≤ d) : ec_emb d (1, 0) = unit ⟨0, by omega⟩ := by
  funext i
  rw [ec_unit_apply]
  simp only [ec_emb, Fin.ext_iff]
  split_ifs <;> simp_all

theorem ec_emb_e1 (hd : 2 ≤ d) : ec_emb d (0, 1) = unit ⟨1, by omega⟩ := by
  funext i
  rw [ec_unit_apply]
  simp only [ec_emb, Fin.ext_iff]
  split_ifs <;> simp_all

/-- Adjacent planar tiles are adjacent in the lattice of tiles of `ℤ^d`. -/
theorem ec_emb_adj (hd : 2 ≤ d) {a z : ℤ × ℤ} (h : ec_adj4 a z) :
    ∃ i : Fin d, ec_emb d z = ec_emb d a + unit i ∨ ec_emb d z = ec_emb d a - unit i := by
  rcases (ec_adj4_iff a z).1 h with h | h | h | h
  · refine ⟨⟨0, by omega⟩, Or.inl ?_⟩
    rw [h, ec_emb_add, ec_emb_e0 hd]
  · refine ⟨⟨0, by omega⟩, Or.inr ?_⟩
    have : (-1, 0) = -((1 : ℤ), (0 : ℤ)) := by ext <;> simp
    rw [h, ec_emb_add, this, ec_emb_neg, ec_emb_e0 hd]
    abel
  · refine ⟨⟨1, by omega⟩, Or.inl ?_⟩
    rw [h, ec_emb_add, ec_emb_e1 hd]
  · refine ⟨⟨1, by omega⟩, Or.inr ?_⟩
    have : (0, -1) = -((0 : ℤ), (1 : ℤ)) := by ext <;> simp
    rw [h, ec_emb_add, this, ec_emb_neg, ec_emb_e1 hd]
    abel

theorem ec_corner_mem (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (j : Site d) :
    (fun i : Fin d => 1 + (k i : ℤ) * j i) ∈ rboxShift k j := by
  intro i
  have := hk i
  constructor
  · exact le_rfl
  · have h1 : (1 : ℤ) ≤ (k i : ℤ) := by exact_mod_cast this
    linarith

theorem ec_corner_inj (hd : 2 ≤ d) (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) :
    Function.Injective (fun z : ℤ × ℤ => (fun i : Fin d => 1 + (k i : ℤ) * ec_emb d z i : Site d)) := by
  intro z z' h
  have h0 := congrFun h ⟨0, by omega⟩
  have h1 := congrFun h ⟨1, by omega⟩
  simp only [ec_emb] at h0 h1
  simp at h0 h1
  have hk0 : k ⟨0, by omega⟩ ≠ 0 := by have := hk ⟨0, by omega⟩; omega
  have hk1 : k ⟨1, by omega⟩ ≠ 0 := by have := hk ⟨1, by omega⟩; omega
  ext
  · exact h0.resolve_right hk0
  · exact h1.resolve_right hk1

theorem ec_abs_le_mnorm (x : Site d) (i : Fin d) : |x i| ≤ mnorm x :=
  Finset.single_le_sum (f := fun j : Fin d => |x j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/-- **The completely toppled tiles.**  If every constant pile at the origin stabilizes,
then the tiles of the plane that topple completely form a finite set containing the
origin tile, and no box-crossing tile lies next to it. -/
theorem ec_full_tiles (hd : 2 ≤ d) (η : Site d → ℤ) (hη : ∀ x, 0 ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 1)
    (k : Fin d → ℕ) (hk : ∀ i, 0 < k i) (hrob : Robust η) :
    ∃ F : Set (ℤ × ℤ), F.Finite ∧ ((0 : ℤ), (0 : ℤ)) ∈ F ∧
      ∀ z : ℤ × ℤ, z ∉ F → (∃ a ∈ F, ec_adj4 a z) → ¬ BoxCrossed η k (ec_emb d z) := by
  set ρ : ℕ := ∑ i, k i with hρ
  set n : ℕ := (2 * d) ^ (ρ + 2) with hn
  have hn1 : 1 ≤ n := Nat.one_le_pow _ _ (by omega)
  set s0 : Site d → ℤ := fun x => η x + (n : ℤ) * dirac (0 : Site d) x with hs0
  obtain ⟨T, hT⟩ := ec_stable_of_stabilizable s0 (hrob n hn1)
  set v : Site d → ℤ := podo s0 T with hv
  have hv0 : ∀ x, 0 ≤ v x := ec_podo_nonneg s0 T
  have hfar : ∀ x, (T : ℤ) < mnorm x → v x = 0 :=
    ec_podo_zero_of_far s0 (fun x hx => by
      simp only [hs0, dirac_of_ne hx, mul_zero, add_zero]; exact (hη x).2) T
  refine ⟨{z | ∀ x ∈ rboxShift k (ec_emb d z), 1 ≤ v x}, ?_, ?_, ?_⟩
  · -- finiteness
    have hbox : {x : Site d | v x ≠ 0}.Finite := by
      refine (Set.Finite.pi (t := fun _ : Fin d => Set.Icc (-(T : ℤ)) (T : ℤ))
        (fun _ => Set.finite_Icc _ _)).subset ?_
      intro x hx
      have hm : mnorm x ≤ (T : ℤ) := by
        by_contra hlt
        exact hx (hfar x (not_le.1 hlt))
      intro i _
      have := ec_abs_le_mnorm x i
      rw [Set.mem_Icc]
      constructor <;> linarith [abs_le.1 (this.trans hm)]
    refine (hbox.preimage (ec_corner_inj hd k hk).injOn).subset ?_
    intro z hz
    have := hz _ (ec_corner_mem k hk (ec_emb d z))
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    omega
  · -- the origin tile
    intro x hx
    rw [ec_emb_zero] at hx
    refine ec_ball_fill (by omega) η (fun x => (hη x).1) n v hv0 hT ρ le_rfl x ?_
    have hb : ∀ i, 1 ≤ x i ∧ x i ≤ (k i : ℤ) := by
      intro i
      have := hx i
      simpa using this
    calc mnorm x = ∑ i, |x i| := rfl
      _ ≤ ∑ i, (k i : ℤ) := Finset.sum_le_sum (fun i _ => by
          have := hb i
          rw [abs_of_nonneg (by omega)]; exact this.2)
      _ = (ρ : ℤ) := by rw [hρ]; push_cast; rfl
  · intro z hz hnb hcross
    obtain ⟨a, ha, hadj⟩ := hnb
    apply hz
    obtain ⟨i, hi⟩ := ec_emb_adj hd hadj
    exact ec_tile_step η n v hv0 hT k hk (ec_emb d a) (ec_emb d z) i hi ha hcross

end Exploding
