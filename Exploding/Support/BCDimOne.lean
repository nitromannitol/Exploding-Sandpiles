/-
The dimension-one box-crossing clause.

The corrected source states the clause inside the box-crossing proposition at line 2656 of
`paper/corrected-arxiv/exploding-corrected-arxiv.tex`: in dimension one, any law supported on
backgrounds `η ≥ 1` is box-crossing. The dimension-one case is separated at line 2451, and the
proof is "immediate in dimension one" at line 2659: a singleton box is crossed from either
external face once its prescribed seed delivers one chip, since the height is at least one.
The crossing definition and the box-crossing hypothesis are at lines 1269–1272.

The objects `faceOut`, `rboxShift`, `fodo` and `BoxCrossed` are those of
`Exploding.Support.Hypotheses` and `Exploding.Support.Toppling`. With box side `1` the tile at
`j` is the single site `j + 1`, and its two external faces are the sites `j` and `j + 2`.

The all-dimension wrapper `bc_box_crossing_all_dims` joins this clause to the `d ≥ 2` theorem
`bc_box_crossing`, with the interface of that theorem.
-/
import Exploding.Support.Hypotheses
import Exploding.Support.SubGeom
import Exploding.Support.ECProofDyn
import Exploding.Support.Wave
import Exploding.Support.BCProofMain
import Exploding.External.Schonmann

namespace Exploding

open LatticeProb MeasureTheory

/-- The unit vector `e_0` takes the value `1` at the coordinate `0`. -/
theorem bc_dim_one_unit_zero_zero : unit (0 : Fin 1) (0 : Fin 1) = 1 := by
  rw [ec_unit_apply]
  simp

/-- One step of the frozen odometer at a site `x` outside the frozen set, whose background is
at least `1`, whose own seed is `0`, and whose two neighbours in the single direction carry seed
total `1`, topples at time `1`. -/
theorem bc_dim_one_fodo_step (S : Set (Site 1)) (η w0 : Site 1 → ℤ) (x : Site 1)
    (hS : x ∉ S) (hη : 1 ≤ η x) (hw : w0 x = 0)
    (hn : w0 (x + unit 0) + w0 (x - unit 0) = 1) :
    1 ≤ fodo S η w0 1 x := by
  have hlap : lap w0 x = 1 := by
    rw [lap, nbrSumZ, Fin.sum_univ_one, hn, hw]
    norm_num
  have hfc : fconf S η w0 0 x = η x + 1 := by
    rw [fconf, fodo_zero, hlap]
  have hcond : 2 * ((1 : ℕ) : ℤ) ≤ fconf S η w0 0 x := by
    rw [hfc]
    push_cast
    omega
  show 1 ≤ fodo S η w0 (0 + 1) x
  rw [fodo_succ, if_neg hS, fodo_zero, hw, if_pos hcond]
  norm_num

/-- Every singleton tile of the one-dimensional box of side `1` is crossed in both directions
by a background with `η ≥ 1`, from time `1` on. -/
theorem bc_dim_one_crossed (η : Site 1 → ℤ) (hη : ∀ x, (1 : ℤ) ≤ η x) (j : Site 1) :
    BoxCrossed η (fun _ : Fin 1 => 1) j := by
  intro i hi t ht x hx
  have hi0 : i = 0 := Subsingleton.elim _ _
  subst hi0
  have ht1 : 1 ≤ t := by simpa using ht
  have hxB := hx
  simp only [rboxShift, Set.mem_setOf_eq] at hxB
  have hx0 : x 0 = j 0 + 1 := by
    have h := hxB 0
    simp only [Nat.cast_one, one_mul] at h
    omega
  have hS : x ∉ (rboxShift (fun _ : Fin 1 => 1) j)ᶜ := fun h => h hx
  refine le_trans ?_ (fodo_mono_time' _ η _ ht1 x)
  cases hi
  · -- low face: the seed sits on `x - unit 0`, the site `j 0`
    have hoff : x - unit 0 ∉ rboxShift (fun _ : Fin 1 => 1) j := by
      intro h
      have h' := h
      simp only [rboxShift, Set.mem_setOf_eq] at h'
      have h2 := h' 0
      simp only [Pi.sub_apply, bc_dim_one_unit_zero_zero, Nat.cast_one, one_mul] at h2
      omega
    have hF : x - unit 0 ∈ faceOut (fun _ : Fin 1 => 1) j 0 false := by
      refine ⟨Or.inr ⟨hoff, x, hx, adj_sub_unit x 0⟩, ?_⟩
      simp only [Set.mem_setOf_eq, Pi.sub_apply, bc_dim_one_unit_zero_zero,
        if_neg Bool.false_ne_true]
      simp only [Nat.cast_one, one_mul]
      omega
    have hxnF : x ∉ faceOut (fun _ : Fin 1 => 1) j 0 false := by
      intro h
      have h2 := h.2
      simp only [Set.mem_setOf_eq, Bool.false_eq_true, if_false, Nat.cast_one, one_mul] at h2
      omega
    have hplusnF : x + unit 0 ∉ faceOut (fun _ : Fin 1 => 1) j 0 false := by
      intro h
      have h2 := h.2
      simp only [Set.mem_setOf_eq, Pi.add_apply, bc_dim_one_unit_zero_zero, Bool.false_eq_true,
        if_false, Nat.cast_one, one_mul] at h2
      omega
    refine bc_dim_one_fodo_step _ η _ x hS (hη x) ?_ ?_
    · exact Set.indicator_of_notMem hxnF _
    · rw [Set.indicator_of_notMem hplusnF, Set.indicator_of_mem hF]
      norm_num
  · -- high face: the seed sits on `x + unit 0`, the site `j 0 + 2`
    have hoff : x + unit 0 ∉ rboxShift (fun _ : Fin 1 => 1) j := by
      intro h
      have h' := h
      simp only [rboxShift, Set.mem_setOf_eq] at h'
      have h2 := h' 0
      simp only [Pi.add_apply, bc_dim_one_unit_zero_zero, Nat.cast_one, one_mul] at h2
      omega
    have hF : x + unit 0 ∈ faceOut (fun _ : Fin 1 => 1) j 0 true := by
      refine ⟨Or.inr ⟨hoff, x, hx, adj_add_unit x 0⟩, ?_⟩
      simp only [Set.mem_setOf_eq, Pi.add_apply, bc_dim_one_unit_zero_zero, if_true]
      simp only [Nat.cast_one, one_mul]
      omega
    have hxnF : x ∉ faceOut (fun _ : Fin 1 => 1) j 0 true := by
      intro h
      have h2 := h.2
      simp only [Set.mem_setOf_eq, if_true, Nat.cast_one, one_mul] at h2
      omega
    have hminusnF : x - unit 0 ∉ faceOut (fun _ : Fin 1 => 1) j 0 true := by
      intro h
      have h2 := h.2
      simp only [Set.mem_setOf_eq, Pi.sub_apply, bc_dim_one_unit_zero_zero, if_true, Nat.cast_one,
        one_mul] at h2
      omega
    refine bc_dim_one_fodo_step _ η _ x hS (hη x) ?_ ?_
    · exact Set.indicator_of_notMem hxnF _
    · rw [Set.indicator_of_notMem hminusnF, Set.indicator_of_mem hF]
      norm_num

/-- The dimension-one box-crossing clause (corrected source, line 2656). Any probability law on
`Site 1 → ℤ` concentrated on backgrounds `η ≥ 1` is box-crossing, with box side `1`. -/
theorem bc_dim_one_box_crossing (P : Measure (Site 1 → ℤ)) [IsProbabilityMeasure P]
    (hsupp : P {η : Site 1 → ℤ | ∀ x, (1 : ℤ) ≤ η x} = 1) :
    BoxCrossingHyp 1 P := by
  unfold BoxCrossingHyp
  intro δ hδ
  refine ⟨fun _ => 1, fun _ => Nat.one_pos, fun j => ?_⟩
  have hsub : {η : Site 1 → ℤ | ∀ x, (1 : ℤ) ≤ η x} ⊆
      {η | BoxCrossed η (fun _ : Fin 1 => 1) j} :=
    fun η hη => bc_dim_one_crossed η hη j
  have hle := measure_mono (μ := P) hsub
  rw [hsupp] at hle
  exact lt_of_lt_of_le (ENNReal.ofReal_lt_one.mpr (by linarith)) hle

/-- The Dirac law at the constant background `1` is box-crossing. Its support premise
`η ≥ 1` holds at the constant background itself. -/
theorem bc_dim_one_dirac_one_box_crossing :
    BoxCrossingHyp 1 (Measure.dirac (fun _ : Site 1 => (1 : ℤ))) := by
  refine bc_dim_one_box_crossing _ ?_
  have hmem : (fun _ : Site 1 => (1 : ℤ)) ∈
      {η : Site 1 → ℤ | ∀ x, (1 : ℤ) ≤ η x} := by
    simp
  exact Measure.dirac_apply_of_mem hmem

/-- On the constant background `1`, the unit tile at `j` (box side `1`) is crossed from its low
external face `faceOut _ j 0 false` and from its high external face `faceOut _ j 0 true`. -/
theorem bc_dim_one_const_one_tile_both_faces (j : Site 1) :
    CrossedInDirection (fun _ : Site 1 => (1 : ℤ)) (fun _ : Fin 1 => 1) j 0 false ∧
      CrossedInDirection (fun _ : Site 1 => (1 : ℤ)) (fun _ : Fin 1 => 1) j 0 true :=
  ⟨bc_dim_one_crossed (fun _ : Site 1 => (1 : ℤ)) (fun _ => le_rfl) j 0 false,
    bc_dim_one_crossed (fun _ : Site 1 => (1 : ℤ)) (fun _ => le_rfl) j 0 true⟩

/-- Box-crossing in every positive dimension. For `d ≥ 2` this is `bc_box_crossing`; for `d = 1`
it is `bc_dim_one_box_crossing`, whose support premise is the product lower bound `bc_nu_good`
at `d = 1`. The interface is that of `bc_box_crossing`. -/
theorem bc_box_crossing_all_dims (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ)
    (hν : IsProbabilityMeasure ν) (hlow : ν {m : ℤ | (d : ℤ) ≤ m} = 1)
    (hhit : 0 < ν {(2 * (d : ℤ) - 1)}) (hSch : External.SchonmannBootstrap) :
    BoxCrossingHyp d (Measure.infinitePi fun _ : Site d => ν) := by
  rcases Nat.lt_or_ge d 2 with h2 | h2
  · obtain rfl : d = 1 := by omega
    refine bc_dim_one_box_crossing _ ?_
    simpa only [Nat.cast_one] using bc_nu_good 1 ν hlow
  · exact bc_box_crossing d h2 ν hν hlow hhit hSch

end Exploding
