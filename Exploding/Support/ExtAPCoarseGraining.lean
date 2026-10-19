/-
The box-crossing coarse-graining input.

The named input `Exploding.xmj_BoxCrossingCoarseGraining` asserts that, at every
density above `bondCritical d`, the box crossings imply the exponential upper tail
of the chemical distance.  This file shows that the input is not a reduction of the
Antal--Pisztora statement `Exploding.External.AntalPisztoraChemicalDistance` to anything
simpler.

Write `BC d` for `Exploding.xap15_BoxCrossing d` and `AP` for the Antal--Pisztora statement.
The statement is `∀ d, 2 ≤ d → AP d`, where `AP d` is its statement at dimension `d`
(a tail bound at every density above `bondCritical d`), and the coarse-graining
input is exactly `∀ d, 2 ≤ d → BC d → AP d`.  Hence

* the Antal--Pisztora statement implies the coarse-graining input, the box-crossing
  hypothesis being discarded;
* box crossing and the coarse-graining input together imply the Antal--Pisztora statement;
* consequently, once box crossing is available in every dimension, the
  coarse-graining input is *equivalent* to the Antal--Pisztora statement.  Since box
  crossing is itself equivalent to the RSW extension `xmj2_SupercriticalCrossingExtension`,
  the same equivalence holds with either hypothesis.  Proving the coarse-graining is
  therefore proving the Antal--Pisztora statement; it isolates no smaller statement.

The route that one might hope to use --- transferring the high-density bound down
to lower densities by the pointwise coupling of configurations --- is refuted:
`Exploding.xap12_BigDistance` is not monotone in the configuration, because opening
one more bond can shorten the chemical distance below the detour ratio.  The final
section exhibits the counterexample.
-/
import Exploding.Support.ExtAPBoxCrossingSupercritical

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

variable {d : ℕ}

/-! ### The coarse-graining input and the Antal--Pisztora statement under box crossing -/

/-- The coarse-graining input follows from the Antal--Pisztora statement: the
box-crossing hypothesis is simply discarded. -/
theorem xmy_coarseGraining_of_antalPisztora
    (h : Exploding.External.AntalPisztoraChemicalDistance) :
    xmj_BoxCrossingCoarseGraining :=
  fun d _hd _hbc => h d _hd

/-- Box crossing and the coarse-graining input together give the Antal--Pisztora statement. -/
theorem xmy_antalPisztora_of_boxCrossing_coarseGraining
    (hbc : ∀ d : ℕ, 2 ≤ d → xap15_BoxCrossing d)
    (hcg : xmj_BoxCrossingCoarseGraining) :
    Exploding.External.AntalPisztoraChemicalDistance :=
  fun d hd => hcg d hd (hbc d hd)

/-- **The coarse-graining input is exactly the Antal--Pisztora statement once box crossing is
available.**  Under box crossing in every dimension the two statements are
equivalent, so the coarse-graining input does not reduce the Antal--Pisztora statement to a
weaker claim. -/
theorem xmy_coarseGraining_iff_antalPisztora_of_boxCrossing
    (hbc : ∀ d : ℕ, 2 ≤ d → xap15_BoxCrossing d) :
    xmj_BoxCrossingCoarseGraining ↔ Exploding.External.AntalPisztoraChemicalDistance :=
  ⟨xmy_antalPisztora_of_boxCrossing_coarseGraining hbc, xmy_coarseGraining_of_antalPisztora⟩

/-- The same equivalence with box crossing replaced by the RSW extension, which is
equivalent to it. -/
theorem xmy_coarseGraining_iff_antalPisztora_of_extension
    (hext : ∀ d : ℕ, 2 ≤ d → xmj2_SupercriticalCrossingExtension d) :
    xmj_BoxCrossingCoarseGraining ↔ Exploding.External.AntalPisztoraChemicalDistance :=
  xmy_coarseGraining_iff_antalPisztora_of_boxCrossing
    (fun d hd => xmx_boxCrossing_of_extension d hd (hext d hd))

/-- The supercritical reduction assembled from box crossing and the coarse-graining
input; by the equivalence above this is the Antal--Pisztora statement in another form and
adds nothing to its direct use. -/
theorem xmy_supercriticalReduction_of_boxCrossing_coarseGraining
    (hbc : ∀ d : ℕ, 2 ≤ d → xap15_BoxCrossing d)
    (hcg : xmj_BoxCrossingCoarseGraining) :
    xap12_SupercriticalReduction :=
  fun _ => xmy_antalPisztora_of_boxCrossing_coarseGraining hbc hcg

/-! ### The pointwise coupling is refuted: `BigDistance` is not monotone

The detour and straight configurations of `ℤ²` below show that opening one more
bond can destroy `xap12_BigDistance`.  The detour realises it, the straight path
does not, while the straight configuration contains every open bond of the detour.
-/

/-- The site of `ℤ²` with the two prescribed coordinates. -/
def xmy_pt (a b : ℤ) : Site 2 := ![a, b]

@[simp] theorem xmy_pt_zero (a b : ℤ) : xmy_pt a b 0 = a := rfl
@[simp] theorem xmy_pt_one (a b : ℤ) : xmy_pt a b 1 = b := rfl

@[simp] theorem xmy_pt_eq (a b c e : ℤ) :
    xmy_pt a b = xmy_pt c e ↔ a = c ∧ b = e := by
  constructor
  · intro h
    exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem xmy_pt_origin : xmy_pt 0 0 = (0 : Site 2) := by
  ext j
  fin_cases j <;> simp [xmy_pt]

@[simp] theorem xmy_pt_eq_zero (a b : ℤ) :
    xmy_pt a b = (0 : Site 2) ↔ a = 0 ∧ b = 0 := by
  rw [← xmy_pt_origin, xmy_pt_eq]

theorem xmy_pt_add_unit0 (a b : ℤ) :
    xmy_pt a b + unit (0 : Fin 2) = xmy_pt (a + 1) b := by
  ext j
  fin_cases j <;> simp [xmy_pt, unit, Pi.single_eq_same, Pi.single_eq_of_ne]

theorem xmy_pt_add_unit1 (a b : ℤ) :
    xmy_pt a b + unit (1 : Fin 2) = xmy_pt a (b + 1) := by
  ext j
  fin_cases j <;> simp [xmy_pt, unit, Pi.single_eq_same, Pi.single_eq_of_ne]

/-- The configuration whose only open bonds form the detour
`0 → (0,1) → (1,1) → (2,1) → (2,0)`. -/
def xmy_detour : Site 2 × Fin 2 → Bool :=
  fun e => decide (e = (xmy_pt 0 0, 1) ∨ e = (xmy_pt 0 1, 0) ∨
    e = (xmy_pt 1 1, 0) ∨ e = (xmy_pt 2 0, 1))

/-- The configuration obtained from the detour by opening also the straight path
`0 → (1,0) → (2,0)`. -/
def xmy_straight : Site 2 × Fin 2 → Bool :=
  fun e => xmy_detour e || decide (e = (xmy_pt 0 0, 0) ∨ e = (xmy_pt 1 0, 0))

theorem xmy_detour_le_straight (e : Site 2 × Fin 2) :
    xmy_detour e = true → xmy_straight e = true := by
  intro h
  simp [xmy_straight, h]

/-- The potential increasing by one along each open bond of the detour. -/
def xmy_pot (x : Site 2) : ℤ :=
  if x = (0 : Site 2) then 0
  else if x = xmy_pt 0 1 then 1
  else if x = xmy_pt 1 1 then 2
  else if x = xmy_pt 2 1 then 3
  else if x = xmy_pt 2 0 then 4
  else 0

@[simp] theorem xmy_pot_zero : xmy_pot (0 : Site 2) = 0 := by
  rw [xmy_pot]; simp

@[simp] theorem xmy_pot_01 : xmy_pot (xmy_pt 0 1) = 1 := by
  rw [xmy_pot]; simp

@[simp] theorem xmy_pot_11 : xmy_pot (xmy_pt 1 1) = 2 := by
  rw [xmy_pot]; simp

@[simp] theorem xmy_pot_21 : xmy_pot (xmy_pt 2 1) = 3 := by
  rw [xmy_pot]; simp

@[simp] theorem xmy_pot_20 : xmy_pot (xmy_pt 2 0) = 4 := by
  rw [xmy_pot]; simp

/-- The four open bonds of the detour, as pairs of adjacent sites. -/
theorem xmy_detour_adj_cases {a b : Site 2}
    (h : (openBondGraph xmy_detour).Adj a b) :
    (a = xmy_pt 0 0 ∧ b = xmy_pt 0 1) ∨ (a = xmy_pt 0 1 ∧ b = xmy_pt 1 1) ∨
    (a = xmy_pt 1 1 ∧ b = xmy_pt 2 1) ∨ (a = xmy_pt 2 0 ∧ b = xmy_pt 2 1) ∨
    (b = xmy_pt 0 0 ∧ a = xmy_pt 0 1) ∨ (b = xmy_pt 0 1 ∧ a = xmy_pt 1 1) ∨
    (b = xmy_pt 1 1 ∧ a = xmy_pt 2 1) ∨ (b = xmy_pt 2 0 ∧ a = xmy_pt 2 1) := by
  rw [openBondGraph, SimpleGraph.fromRel_adj] at h
  obtain ⟨_hne, hrel⟩ := h
  have key : ∀ e : Site 2 × Fin 2, xmy_detour e = true →
      e = (xmy_pt 0 0, 1) ∨ e = (xmy_pt 0 1, 0) ∨
      e = (xmy_pt 1 1, 0) ∨ e = (xmy_pt 2 0, 1) := by
    intro e he
    simpa [xmy_detour] using he
  rcases hrel with ⟨i, hb, hω⟩ | ⟨i, ha, hω⟩
  · rcases key (a, i) hω with h | h | h | h
    · have ha : a = xmy_pt 0 0 := by simpa using congrArg Prod.fst h
      have hi : i = (1 : Fin 2) := by simpa using congrArg Prod.snd h
      subst ha; subst hi
      left; exact ⟨rfl, by rw [hb, xmy_pt_add_unit1]; norm_num⟩
    · have ha : a = xmy_pt 0 1 := by simpa using congrArg Prod.fst h
      have hi : i = (0 : Fin 2) := by simpa using congrArg Prod.snd h
      subst ha; subst hi
      right; left; exact ⟨rfl, by rw [hb, xmy_pt_add_unit0]; norm_num⟩
    · have ha : a = xmy_pt 1 1 := by simpa using congrArg Prod.fst h
      have hi : i = (0 : Fin 2) := by simpa using congrArg Prod.snd h
      subst ha; subst hi
      right; right; left; exact ⟨rfl, by rw [hb, xmy_pt_add_unit0]; norm_num⟩
    · have ha : a = xmy_pt 2 0 := by simpa using congrArg Prod.fst h
      have hi : i = (1 : Fin 2) := by simpa using congrArg Prod.snd h
      subst ha; subst hi
      right; right; right; left; exact ⟨rfl, by rw [hb, xmy_pt_add_unit1]; norm_num⟩
  · rcases key (b, i) hω with h | h | h | h
    · have hb' : b = xmy_pt 0 0 := by simpa using congrArg Prod.fst h
      have hi : i = (1 : Fin 2) := by simpa using congrArg Prod.snd h
      subst hb'; subst hi
      right; right; right; right; left
      exact ⟨rfl, by rw [ha, xmy_pt_add_unit1]; norm_num⟩
    · have hb' : b = xmy_pt 0 1 := by simpa using congrArg Prod.fst h
      have hi : i = (0 : Fin 2) := by simpa using congrArg Prod.snd h
      subst hb'; subst hi
      right; right; right; right; right; left
      exact ⟨rfl, by rw [ha, xmy_pt_add_unit0]; norm_num⟩
    · have hb' : b = xmy_pt 1 1 := by simpa using congrArg Prod.fst h
      have hi : i = (0 : Fin 2) := by simpa using congrArg Prod.snd h
      subst hb'; subst hi
      right; right; right; right; right; right; left
      exact ⟨rfl, by rw [ha, xmy_pt_add_unit0]; norm_num⟩
    · have hb' : b = xmy_pt 2 0 := by simpa using congrArg Prod.fst h
      have hi : i = (1 : Fin 2) := by simpa using congrArg Prod.snd h
      subst hb'; subst hi
      right; right; right; right; right; right; right
      exact ⟨rfl, by rw [ha, xmy_pt_add_unit1]; norm_num⟩

/-- An open bond of the detour changes the potential by at most one. -/
theorem xmy_pot_adj {a b : Site 2} (h : (openBondGraph xmy_detour).Adj a b) :
    |xmy_pot a - xmy_pot b| ≤ 1 := by
  rcases xmy_detour_adj_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-- Every open walk in the detour configuration moves the potential by at most its
length. -/
theorem xmy_pot_walk_le {a b : Site 2} (p : (openBondGraph xmy_detour).Walk a b) :
    |xmy_pot a - xmy_pot b| ≤ (p.length : ℤ) := by
  induction p with
  | nil => simp
  | cons hadj p' ih =>
      rw [SimpleGraph.Walk.length_cons]
      push_cast
      have h1 : |xmy_pot _ - xmy_pot _| ≤ (1 : ℤ) := xmy_pot_adj hadj
      have h2 : |xmy_pot _ - xmy_pot _| ≤ (p'.length : ℤ) := ih
      calc |xmy_pot _ - xmy_pot _|
          = |(xmy_pot _ - xmy_pot _) + (xmy_pot _ - xmy_pot _)| := by ring_nf
        _ ≤ |xmy_pot _ - xmy_pot _| + |xmy_pot _ - xmy_pot _| := abs_add_le _ _
        _ ≤ (1 : ℤ) + (p'.length : ℤ) := add_le_add h1 h2
        _ = (p'.length : ℤ) + 1 := by ring

/-- The chemical distance in the detour configuration is four. -/
theorem xmy_edist_detour :
    (openBondGraph xmy_detour).edist (0 : Site 2) (xmy_pt 2 0) = 4 := by
  have e1 : (openBondGraph xmy_detour).Adj (0 : Site 2) (xmy_pt 0 1) := by
    rw [openBondGraph, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl ⟨(1 : Fin 2), ?_, by simp [xmy_detour]⟩⟩
    · intro h
      have h' : xmy_pt 0 1 = (0 : Site 2) := h.symm
      rw [xmy_pt_eq_zero] at h'
      norm_num at h'
    · rw [← xmy_pt_origin, xmy_pt_add_unit1]; norm_num
  have e2 : (openBondGraph xmy_detour).Adj (xmy_pt 0 1) (xmy_pt 1 1) := by
    rw [openBondGraph, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl ⟨(0 : Fin 2), ?_, by simp [xmy_detour]⟩⟩
    · intro h
      have h' : xmy_pt 0 1 = xmy_pt 1 1 := h
      rw [xmy_pt_eq] at h'
      norm_num at h'
    · rw [xmy_pt_add_unit0]; norm_num
  have e3 : (openBondGraph xmy_detour).Adj (xmy_pt 1 1) (xmy_pt 2 1) := by
    rw [openBondGraph, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl ⟨(0 : Fin 2), ?_, by simp [xmy_detour]⟩⟩
    · intro h
      have h' : xmy_pt 1 1 = xmy_pt 2 1 := h
      rw [xmy_pt_eq] at h'
      norm_num at h'
    · rw [xmy_pt_add_unit0]; norm_num
  have e4 : (openBondGraph xmy_detour).Adj (xmy_pt 2 1) (xmy_pt 2 0) := by
    rw [openBondGraph, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inr ⟨(1 : Fin 2), ?_, by simp [xmy_detour]⟩⟩
    · intro h
      have h' : xmy_pt 2 1 = xmy_pt 2 0 := h
      rw [xmy_pt_eq] at h'
      norm_num at h'
    · rw [xmy_pt_add_unit1]; norm_num
  apply le_antisymm
  · calc (openBondGraph xmy_detour).edist (0 : Site 2) (xmy_pt 2 0)
        ≤ ((SimpleGraph.Walk.cons e1 (SimpleGraph.Walk.cons e2
            (SimpleGraph.Walk.cons e3 (SimpleGraph.Walk.cons e4
              SimpleGraph.Walk.nil)))).length : ℕ∞) := SimpleGraph.edist_le _
      _ = 4 := by simp [SimpleGraph.Walk.length_cons]
  · rw [SimpleGraph.edist]
    refine le_iInf fun q => ?_
    have h := xmy_pot_walk_le q
    rw [xmy_pot_zero, xmy_pot_20] at h
    norm_num at h
    exact_mod_cast h

/-- The two-step straight path gives distance at most two in the straight
configuration. -/
theorem xmy_edist_straight_le :
    (openBondGraph xmy_straight).edist (0 : Site 2) (xmy_pt 2 0) ≤ 2 := by
  have e1 : (openBondGraph xmy_straight).Adj (0 : Site 2) (xmy_pt 1 0) := by
    rw [openBondGraph, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl ⟨(0 : Fin 2), ?_, by simp [xmy_straight]⟩⟩
    · intro h
      have h' : xmy_pt 1 0 = (0 : Site 2) := h.symm
      rw [xmy_pt_eq_zero] at h'
      norm_num at h'
    · rw [← xmy_pt_origin, xmy_pt_add_unit0]; norm_num
  have e2 : (openBondGraph xmy_straight).Adj (xmy_pt 1 0) (xmy_pt 2 0) := by
    rw [openBondGraph, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl ⟨(0 : Fin 2), ?_, by simp [xmy_straight]⟩⟩
    · intro h
      have h' : xmy_pt 1 0 = xmy_pt 2 0 := h
      rw [xmy_pt_eq] at h'
      norm_num at h'
    · rw [xmy_pt_add_unit0]; norm_num
  calc (openBondGraph xmy_straight).edist (0 : Site 2) (xmy_pt 2 0)
      ≤ ((SimpleGraph.Walk.cons e1 (SimpleGraph.Walk.cons e2
          SimpleGraph.Walk.nil)).length : ℕ∞) := SimpleGraph.edist_le _
    _ ≤ 2 := by simp [SimpleGraph.Walk.length_cons]

/-- **`xap12_BigDistance` is not monotone in the configuration.**  There are two
configurations, the second containing all open bonds of the first, such that the
first satisfies the tail event and the second does not.  This refutes the pointwise
coupling used to transfer a bound from high to lower densities. -/
theorem xmy_bigDistance_not_monotone :
    ∃ (ω ω' : Site 2 × Fin 2 → Bool) (y : Site 2) (ρ : ℝ),
      (∀ e, ω e = true → ω' e = true) ∧
        xap12_BigDistance 2 ρ ω y ∧ ¬ xap12_BigDistance 2 ρ ω' y := by
  refine ⟨xmy_detour, xmy_straight, xmy_pt 2 0, 3 / 2, xmy_detour_le_straight, ?_, ?_⟩
  · refine ⟨4, xmy_edist_detour, ?_⟩
    have hy : mnorm (xmy_pt 2 0) = (2 : ℤ) := by
      simp [mnorm, xmy_pt, Fin.sum_univ_two]
    rw [hy]
    norm_num
  · rintro ⟨m, hm, hlt⟩
    have hle := xmy_edist_straight_le
    rw [hm] at hle
    have hm2 : m ≤ 2 := by exact_mod_cast hle
    have hm2' : (m : ℝ) ≤ 2 := by exact_mod_cast hm2
    have hy : mnorm (xmy_pt 2 0) = (2 : ℤ) := by
      simp [mnorm, xmy_pt, Fin.sum_univ_two]
    rw [hy] at hlt
    norm_num at hlt
    linarith

end Exploding
