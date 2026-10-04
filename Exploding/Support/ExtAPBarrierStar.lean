/-
The boundary of a connected set inside a box, closed under adjacency outside a connected
set within the box, need not be `*`-connected.  Two fingers of the connected set can reach
the wall of the box and be joined outside it, while the connected set wraps around the tips
of the fingers; then the sites adjacent to the connected set fall into two pieces more than
one king move apart.  This file records the explicit counterexample.
-/
import Exploding.Support.ExtMHBase
import Exploding.Support.Vocab

namespace Exploding

open LatticeProb Relation

variable {d : ℕ}

/-- The site of `ℤ²` with the two prescribed coordinates. -/
def xbs_pt (a b : ℤ) : Site 2 := ![a, b]

@[simp] theorem xbs_pt_zero (a b : ℤ) : xbs_pt a b 0 = a := rfl

@[simp] theorem xbs_pt_one (a b : ℤ) : xbs_pt a b 1 = b := rfl

/-! ### Elementary adjacency facts -/

theorem xbs_adj_add_unit (z : Site d) (i : Fin d) : (lattice d).Adj z (z + unit i) :=
  ⟨i, Or.inl rfl⟩

theorem xbs_adj_sub_unit (z : Site d) (i : Fin d) : (lattice d).Adj z (z - unit i) :=
  ⟨i, Or.inr (by simp)⟩

theorem xbs_abs_sub_le_of_adj {a b : Site d} (h : (lattice d).Adj a b) (i : Fin d) :
    |a i - b i| ≤ 1 := by
  obtain ⟨j, hj | hj⟩ := h
  · subst hj
    rw [abs_sub_comm]
    by_cases hji : i = j
    · subst hji; simp [unit]
    · simp [unit, Pi.single_eq_of_ne hji]
  · subst hj
    by_cases hji : i = j
    · subst hji; simp [unit]
    · simp [unit, Pi.single_eq_of_ne hji]

theorem xbs_natAbs_add_one_lt {a : ℤ} (ha : a < 0) : (a + 1).natAbs < a.natAbs := by
  have h1 : ((a + 1).natAbs : ℤ) = -(a + 1) := Int.ofNat_natAbs_of_nonpos (by omega)
  have h2 : (a.natAbs : ℤ) = -a := Int.ofNat_natAbs_of_nonpos (le_of_lt ha)
  omega

theorem xbs_natAbs_sub_one_lt {a : ℤ} (ha : 0 < a) : (a - 1).natAbs < a.natAbs := by
  have h1 : ((a - 1).natAbs : ℤ) = a - 1 := Int.natAbs_of_nonneg (by omega)
  have h2 : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg (le_of_lt ha)
  omega

/-! ### Connectivity from a decreasing parent map -/

theorem xbs_connected_of_parent {S : Set (Site d)} {root : Site d} {r : Site d → ℕ}
    (hpar : ∀ z ∈ S, z ≠ root → ∃ p ∈ S, (lattice d).Adj z p ∧ r p < r z) :
    ∀ u ∈ S, ∀ v ∈ S,
      ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ (lattice d).Adj a b) u v := by
  have hsymm : ∀ a b, (a ∈ S ∧ b ∈ S ∧ (lattice d).Adj a b) →
      (b ∈ S ∧ a ∈ S ∧ (lattice d).Adj b a) :=
    fun a b h => ⟨h.2.1, h.1, h.2.2.symm⟩
  have hto : ∀ n, ∀ z ∈ S, r z = n →
      ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ (lattice d).Adj a b) z root := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro z hz hrz
      by_cases hzr : z = root
      · subst hzr; exact ReflTransGen.refl
      · obtain ⟨p, hpS, hAdj, hlt⟩ := hpar z hz hzr
        exact (ReflTransGen.single ⟨hz, hpS, hAdj⟩).trans
          (ih (r p) (by omega) p hpS rfl)
  intro u hu v hv
  exact (hto (r u) u hu rfl).trans (xmh_rtg_symm hsymm (hto (r v) v hv rfl))

/-! ### The counterexample -/

/-- `A`: two vertical fingers at `x₀ = ±2` spanning `x₁ ∈ [-4, 0]`, joined by the horizontal
bar `x₁ = -4`. -/
def xbs_A : Set (Site 2) :=
  {z | (z 0 = -2 ∧ -4 ≤ z 1 ∧ z 1 ≤ 0) ∨ (z 0 = 2 ∧ -4 ≤ z 1 ∧ z 1 ≤ 0) ∨
       (z 1 = -4 ∧ -2 ≤ z 0 ∧ z 0 ≤ 2)}

/-- `B`, the box `cent 2 2` with `A` removed. -/
def xbs_B : Set (Site 2) := {z | z ∈ cent 2 2 ∧ z ∉ xbs_A}

/-- The rank used for connectivity of `A`, measuring the distance from its middle. -/
def xbs_Ar (z : Site 2) : ℕ := (z 1 + 4).natAbs * 10 + (z 0).natAbs

/-- The parent map for `A`: along the bar move towards `x₀ = 0`, on the fingers move down. -/
def xbs_Apar (z : Site 2) : Site 2 :=
  if z 1 = -4 then
    (if z 0 ≤ 0 then z + unit (0 : Fin 2) else z - unit (0 : Fin 2))
  else z - unit (1 : Fin 2)

theorem xbs_A_par (z : Site 2) (hz : z ∈ xbs_A) (hzr : z ≠ xbs_pt 0 (-4)) :
    ∃ p ∈ xbs_A, (lattice 2).Adj z p ∧ xbs_Ar p < xbs_Ar z := by
  have hz1lo : -4 ≤ z 1 := by
    rcases hz with ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨h, _, _⟩ <;> omega
  have hz1hi : z 1 ≤ 0 := by
    rcases hz with ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨h, _, _⟩ <;> omega
  by_cases hz1 : z 1 = -4
  · have hz0lo : -2 ≤ z 0 := by
      rcases hz with ⟨h, _, _⟩ | ⟨h, _, _⟩ | ⟨_, h, _⟩ <;> omega
    have hz0hi : z 0 ≤ 2 := by
      rcases hz with ⟨h, _, _⟩ | ⟨h, _, _⟩ | ⟨_, _, h⟩ <;> omega
    have hz0ne : z 0 ≠ 0 := by
      intro h0
      apply hzr
      ext i
      fin_cases i
      · simpa [xbs_pt] using h0
      · simpa [xbs_pt] using hz1
    by_cases hle : z 0 ≤ 0
    · have hp : xbs_Apar z = z + unit (0 : Fin 2) := by
        rw [xbs_Apar, if_pos hz1, if_pos hle]
      refine ⟨xbs_Apar z, ?_, ?_, ?_⟩
      · rw [hp]
        refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
        · simp [unit, hz1]
        · simp [unit]; omega
        · simp [unit]; omega
      · rw [hp]; exact xbs_adj_add_unit z 0
      · rw [hp]
        have hdec : (z 0 + 1).natAbs < (z 0).natAbs := xbs_natAbs_add_one_lt (by omega)
        simp only [xbs_Ar]
        simp [unit]
        omega
    · have hgt : 0 < z 0 := by omega
      have hp : xbs_Apar z = z - unit (0 : Fin 2) := by
        rw [xbs_Apar, if_pos hz1, if_neg hle]
      refine ⟨xbs_Apar z, ?_, ?_, ?_⟩
      · rw [hp]
        refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
        · simp [unit, hz1]
        · simp [unit]; omega
        · simp [unit]; omega
      · rw [hp]; exact xbs_adj_sub_unit z 0
      · rw [hp]
        have hdec : (z 0 - 1).natAbs < (z 0).natAbs := xbs_natAbs_sub_one_lt hgt
        simp only [xbs_Ar]
        simp [unit]
        omega
  · have hz0 : z 0 = -2 ∨ z 0 = 2 := by
      rcases hz with ⟨h, _, _⟩ | ⟨h, _, _⟩ | ⟨h, _, _⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hz1
    have hz1ge : -3 ≤ z 1 := by omega
    have hp : xbs_Apar z = z - unit (1 : Fin 2) := by
      rw [xbs_Apar, if_neg hz1]
    refine ⟨xbs_Apar z, ?_, ?_, ?_⟩
    · rw [hp]
      rcases hz0 with h | h
      · refine Or.inl ⟨?_, ?_, ?_⟩
        · simp [unit, h]
        · simp [unit]; omega
        · simp [unit]; omega
      · refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
        · simp [unit, h]
        · simp [unit]; omega
        · simp [unit]; omega
    · rw [hp]; exact xbs_adj_sub_unit z 1
    · rw [hp]
      have hdec : ((z 1 - 1 + 4).natAbs : ℤ) < ((z 1 + 4).natAbs : ℤ) := by
        have h1 : ((z 1 - 1 + 4).natAbs : ℤ) = z 1 - 1 + 4 :=
          Int.natAbs_of_nonneg (by omega)
        have h2 : ((z 1 + 4).natAbs : ℤ) = z 1 + 4 := Int.natAbs_of_nonneg (by omega)
        omega
      simp only [xbs_Ar]
      simp [unit]
      omega

theorem xbs_A_connected :
    ∀ u ∈ xbs_A, ∀ v ∈ xbs_A,
      ReflTransGen (fun a b => a ∈ xbs_A ∧ b ∈ xbs_A ∧ (lattice 2).Adj a b) u v :=
  xbs_connected_of_parent (S := xbs_A) (root := xbs_pt 0 (-4)) (r := xbs_Ar) xbs_A_par

/-- The rank used for connectivity of `B`, measuring the distance from the top middle. -/
def xbs_Br (z : Site 2) : ℕ := (2 - z 1).natAbs * 10 + (z 0).natAbs

/-- The parent map for `B`: move up, and on the top row move towards `x₀ = 0`. -/
def xbs_Bpar (z : Site 2) : Site 2 :=
  if z 1 < 2 then z + unit (1 : Fin 2)
  else if z 0 < 0 then z + unit (0 : Fin 2)
  else if 0 < z 0 then z - unit (0 : Fin 2) else z

theorem xbs_B_par (z : Site 2) (hz : z ∈ xbs_B) (hzr : z ≠ xbs_pt 0 2) :
    ∃ p ∈ xbs_B, (lattice 2).Adj z p ∧ xbs_Br p < xbs_Br z := by
  obtain ⟨hzcent, hzA⟩ := hz
  have hz0 : |z 0| ≤ 2 := hzcent 0
  have hz1 : |z 1| ≤ 2 := hzcent 1
  have hz0lo : -2 ≤ z 0 := (abs_le.mp hz0).1
  have hz0hi : z 0 ≤ 2 := (abs_le.mp hz0).2
  have hz1lo : -2 ≤ z 1 := (abs_le.mp hz1).1
  have hz1hi : z 1 ≤ 2 := (abs_le.mp hz1).2
  by_cases hz1lt : z 1 < 2
  · have hp : xbs_Bpar z = z + unit (1 : Fin 2) := by
      rw [xbs_Bpar, if_pos hz1lt]
    have hp1 : (z + unit (1 : Fin 2)) 1 = z 1 + 1 := by simp [unit]
    have hp0 : (z + unit (1 : Fin 2)) 0 = z 0 := by simp [unit]
    refine ⟨xbs_Bpar z, ?_, ?_, ?_⟩
    · rw [hp]
      refine ⟨?_, ?_⟩
      · change ∀ i, |(z + unit (1 : Fin 2)) i| ≤ (2 : ℤ)
        rw [Fin.forall_fin_two]
        constructor
        · simpa [hp0] using hz0
        · rw [hp1, abs_le]; constructor <;> omega
      · intro hA
        rcases hA with ⟨h0, hlo, hhi⟩ | ⟨h0, hlo, hhi⟩ | ⟨h1, _, _⟩
        · apply hzA
          refine Or.inl ⟨?_, ?_, ?_⟩
          · simpa [hp0] using h0
          · rw [hp1] at hlo; omega
          · rw [hp1] at hhi; omega
        · apply hzA
          refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
          · simpa [hp0] using h0
          · rw [hp1] at hlo; omega
          · rw [hp1] at hhi; omega
        · rw [hp1] at h1; omega
    · rw [hp]; exact xbs_adj_add_unit z 1
    · rw [hp]
      have hdec : (2 - (z 1 + 1)).natAbs < (2 - z 1).natAbs := by
        have h1 : ((2 - (z 1 + 1)).natAbs : ℤ) = 2 - (z 1 + 1) :=
          Int.natAbs_of_nonneg (by omega)
        have h2 : ((2 - z 1).natAbs : ℤ) = 2 - z 1 := Int.natAbs_of_nonneg (by omega)
        omega
      simp only [xbs_Br]
      simp [unit]
      omega
  · have hz1eq : z 1 = 2 := by omega
    have hz0ne : z 0 ≠ 0 := by
      intro h0
      apply hzr
      ext i
      fin_cases i
      · simpa [xbs_pt] using h0
      · simpa [xbs_pt] using hz1eq
    have hnotlt : ¬ z 1 < 2 := by omega
    by_cases hz0lt : z 0 < 0
    · have hp : xbs_Bpar z = z + unit (0 : Fin 2) := by
        rw [xbs_Bpar, if_neg hnotlt, if_pos hz0lt]
      have hp0 : (z + unit (0 : Fin 2)) 0 = z 0 + 1 := by simp [unit]
      have hp1 : (z + unit (0 : Fin 2)) 1 = z 1 := by simp [unit]
      refine ⟨xbs_Bpar z, ?_, ?_, ?_⟩
      · rw [hp]
        refine ⟨?_, ?_⟩
        · change ∀ i, |(z + unit (0 : Fin 2)) i| ≤ (2 : ℤ)
          rw [Fin.forall_fin_two]
          constructor
          · rw [hp0, abs_le]; constructor <;> omega
          · simpa [hp1] using hz1
        · intro hA
          rcases hA with ⟨_, _, hhi⟩ | ⟨_, _, hhi⟩ | ⟨h1, _, _⟩
          · rw [hp1, hz1eq] at hhi; omega
          · rw [hp1, hz1eq] at hhi; omega
          · rw [hp1, hz1eq] at h1; omega
      · rw [hp]; exact xbs_adj_add_unit z 0
      · rw [hp]
        have hdec : (z 0 + 1).natAbs < (z 0).natAbs := xbs_natAbs_add_one_lt hz0lt
        simp only [xbs_Br]
        simp [unit]
        omega
    · by_cases hz0gt : 0 < z 0
      · have hp : xbs_Bpar z = z - unit (0 : Fin 2) := by
          rw [xbs_Bpar, if_neg hnotlt, if_neg hz0lt, if_pos hz0gt]
        have hp0 : (z - unit (0 : Fin 2)) 0 = z 0 - 1 := by simp [unit]
        have hp1 : (z - unit (0 : Fin 2)) 1 = z 1 := by simp [unit]
        refine ⟨xbs_Bpar z, ?_, ?_, ?_⟩
        · rw [hp]
          refine ⟨?_, ?_⟩
          · change ∀ i, |(z - unit (0 : Fin 2)) i| ≤ (2 : ℤ)
            rw [Fin.forall_fin_two]
            constructor
            · rw [hp0, abs_le]; constructor <;> omega
            · simpa [hp1] using hz1
          · intro hA
            rcases hA with ⟨_, _, hhi⟩ | ⟨_, _, hhi⟩ | ⟨h1, _, _⟩
            · rw [hp1, hz1eq] at hhi; omega
            · rw [hp1, hz1eq] at hhi; omega
            · rw [hp1, hz1eq] at h1; omega
        · rw [hp]; exact xbs_adj_sub_unit z 0
        · rw [hp]
          have hdec : (z 0 - 1).natAbs < (z 0).natAbs := xbs_natAbs_sub_one_lt hz0gt
          simp only [xbs_Br]
          simp [unit]
          omega
      · exact absurd (by omega : z 0 = 0) hz0ne

theorem xbs_B_connected :
    ∀ u ∈ xbs_B, ∀ v ∈ xbs_B,
      ReflTransGen (fun a b => a ∈ xbs_B ∧ b ∈ xbs_B ∧ (lattice 2).Adj a b) u v :=
  xbs_connected_of_parent (S := xbs_B) (root := xbs_pt 0 2) (r := xbs_Br) xbs_B_par

/-! ### The boundary is disconnected -/

/-- The sites of `B` adjacent to `A`. -/
def xbs_S : Set (Site 2) := {z | z ∈ xbs_B ∧ ∃ c ∈ xbs_A, (lattice 2).Adj c z}

/-- The boundary relation of the conjecture. -/
def xbs_R (a b : Site 2) : Prop :=
  (a ∈ xbs_B ∧ ∃ c ∈ xbs_A, (lattice 2).Adj c a) ∧
    (b ∈ xbs_B ∧ ∃ c ∈ xbs_A, (lattice 2).Adj c b) ∧ xmh_star a b

theorem xbs_S_ne_zero : ∀ z ∈ xbs_S, z 0 ≠ 0 := by
  intro z hz hz0
  obtain ⟨hzB, c, hcA, hadj⟩ := hz
  have hz1 : |z 1| ≤ 2 := hzB.1 1
  have hz1le : z 1 ≤ 2 := (abs_le.mp hz1).2
  have hz1ge : -2 ≤ z 1 := (abs_le.mp hz1).1
  have hc0 := xbs_abs_sub_le_of_adj hadj 0
  have hc1 := xbs_abs_sub_le_of_adj hadj 1
  rcases hcA with ⟨hc0eq, _, _⟩ | ⟨hc0eq, _, _⟩ | ⟨hc1eq, _, _⟩
  · rw [hz0, hc0eq] at hc0
    norm_num at hc0
  · rw [hz0, hc0eq] at hc0
    norm_num at hc0
  · rw [hc1eq] at hc1
    have hnonpos : ((-4 : ℤ) - z 1) ≤ 0 := by omega
    rw [abs_of_nonpos hnonpos] at hc1
    omega

theorem xbs_no_chain :
    ¬ ReflTransGen xbs_R (xbs_pt (-1) 0) (xbs_pt 1 0) := by
  intro h
  have hstep : ∀ a b, xbs_R a b → a 0 ≤ -1 → b 0 ≤ -1 := by
    intro a b hab _
    have hbS : b ∈ xbs_S := hab.2.1
    have hb0 : b 0 ≠ 0 := xbs_S_ne_zero b hbS
    have hnear : |a 0 - b 0| ≤ 1 := hab.2.2.2 0
    by_cases hble : b 0 ≤ -1
    · exact hble
    · exfalso
      have hb1 : 1 ≤ b 0 := by omega
      have hdiff : a 0 - b 0 ≤ 0 := by omega
      have hge : (2 : ℤ) ≤ |a 0 - b 0| := by
        rw [abs_of_nonpos hdiff]; omega
      omega
  have hmem : ∀ z, ReflTransGen xbs_R (xbs_pt (-1) 0) z → z 0 ≤ -1 := by
    intro z hz
    induction hz with
    | refl => simp [xbs_pt]
    | tail _ hab ih => exact hstep _ _ hab ih
  have := hmem (xbs_pt 1 0) h
  simp [xbs_pt] at this

theorem xbs_box_boundaryStar_refuted :
    ¬ (∀ A B : Set (Site 2),
      (∀ u ∈ A, ∀ v ∈ A, ReflTransGen (fun a b => a ∈ A ∧ b ∈ A ∧ (lattice 2).Adj a b) u v) →
      (∀ u ∈ B, ∀ v ∈ B, ReflTransGen (fun a b => a ∈ B ∧ b ∈ B ∧ (lattice 2).Adj a b) u v) →
      (∀ z ∈ B, z ∈ cent 2 2) →
      (∀ z, z ∈ A → z ∈ B → False) →
      (∀ b ∈ B, ∀ z, (lattice 2).Adj b z → z ∈ cent 2 2 → z ∉ A → z ∈ B) →
      ∀ x y : Site 2, (x ∈ B ∧ ∃ c ∈ A, (lattice 2).Adj c x) →
        (y ∈ B ∧ ∃ c ∈ A, (lattice 2).Adj c y) →
        ReflTransGen (fun a b => (a ∈ B ∧ ∃ c ∈ A, (lattice 2).Adj c a) ∧
          (b ∈ B ∧ ∃ c ∈ A, (lattice 2).Adj c b) ∧ xmh_star a b) x y) := by
  intro h
  have hx : xbs_pt (-1) 0 ∈ xbs_B ∧ ∃ c ∈ xbs_A, (lattice 2).Adj c (xbs_pt (-1) 0) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i; fin_cases i <;> simp [xbs_pt]
    · intro hA
      rcases hA with ⟨h0, _, _⟩ | ⟨h0, _, _⟩ | ⟨h1, _, _⟩
      · exact absurd h0 (by norm_num [xbs_pt])
      · exact absurd h0 (by norm_num [xbs_pt])
      · exact absurd h1 (by norm_num [xbs_pt])
    · refine ⟨xbs_pt (-2) 0, Or.inl ⟨rfl, by norm_num [xbs_pt], by norm_num [xbs_pt]⟩, ?_⟩
      have h2 : xbs_pt (-2) 0 + unit (0 : Fin 2) = xbs_pt (-1) 0 := by
        ext i; fin_cases i <;> simp [xbs_pt, unit]
      rw [← h2]; exact xbs_adj_add_unit _ 0
  have hy : xbs_pt 1 0 ∈ xbs_B ∧ ∃ c ∈ xbs_A, (lattice 2).Adj c (xbs_pt 1 0) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i; fin_cases i <;> simp [xbs_pt]
    · intro hA
      rcases hA with ⟨h0, _, _⟩ | ⟨h0, _, _⟩ | ⟨h1, _, _⟩
      · exact absurd h0 (by norm_num [xbs_pt])
      · exact absurd h0 (by norm_num [xbs_pt])
      · exact absurd h1 (by norm_num [xbs_pt])
    · refine ⟨xbs_pt 2 0, Or.inr (Or.inl ⟨rfl, by norm_num [xbs_pt], by norm_num [xbs_pt]⟩), ?_⟩
      have h2 : xbs_pt 2 0 - unit (0 : Fin 2) = xbs_pt 1 0 := by
        ext i; fin_cases i <;> simp [xbs_pt, unit]
      rw [← h2]; exact xbs_adj_sub_unit _ 0
  exact xbs_no_chain (h xbs_A xbs_B xbs_A_connected xbs_B_connected
    (fun z hz => hz.1) (fun z hA hB => hB.2 hA)
    (fun b hb z hAdj hzcent hzA => ⟨hzcent, hzA⟩) (xbs_pt (-1) 0) (xbs_pt 1 0) hx hy)

end Exploding
