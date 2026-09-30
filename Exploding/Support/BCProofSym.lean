/-
Lattice symmetries for the box-crossing proof (Proposition 7.5 of
`paper/exploding.tex`, "We conclude by symmetry").

A *lattice symmetry* is a bijection `h` of `ℤ^d` that preserves nearest-neighbour
adjacency and the neighbour sum.  Translations, coordinate permutations and the
reflection `x_i ↦ c - x_i` are lattice symmetries; the frozen odometer `fodo`
commutes with them, which transports crossing of one face of one tile to crossing
of any other face of any other tile.
-/
import Exploding.Support.Hypotheses

open Exploding LatticeProb MeasureTheory

variable {d : ℕ}

/-- A lattice symmetry: a bijection of `ℤ^d` preserving adjacency and the neighbour sum. -/
structure BCSym (h : Site d → Site d) : Prop where
  bij : Function.Bijective h
  adj : ∀ x y, (lattice d).Adj (h x) (h y) ↔ (lattice d).Adj x y
  nbr : ∀ (u : Site d → ℤ) (x : Site d), nbrSumZ (fun y => u (h y)) x = nbrSumZ u (h x)

/-- A map with a two-sided inverse that preserves adjacency in both directions and the
neighbour sum is a lattice symmetry. -/
theorem bc_sym_of_inv (h h' : Site d → Site d) (hh' : ∀ x, h (h' x) = x)
    (h'h : ∀ x, h' (h x) = x)
    (adj_h : ∀ x y, (lattice d).Adj x y → (lattice d).Adj (h x) (h y))
    (adj_h' : ∀ x y, (lattice d).Adj x y → (lattice d).Adj (h' x) (h' y))
    (nbr : ∀ (u : Site d → ℤ) (x : Site d), nbrSumZ (fun y => u (h y)) x = nbrSumZ u (h x)) :
    BCSym h where
  bij := ⟨fun a b hab => by rw [← h'h a, ← h'h b, hab], fun y => ⟨h' y, hh' y⟩⟩
  adj x y := ⟨fun hxy => by
      have := adj_h' _ _ hxy
      rwa [h'h, h'h] at this, adj_h x y⟩
  nbr := nbr

theorem bc_sym_comp {g h : Site d → Site d} (hg : BCSym g) (hh : BCSym h) :
    BCSym (fun x => g (h x)) where
  bij := hg.bij.comp hh.bij
  adj x y := (hg.adj _ _).trans (hh.adj x y)
  nbr u x := by
    rw [show (fun y => u (g (h y))) = (fun y => (fun z => u (g z)) (h y)) from rfl,
      hh.nbr (fun z => u (g z)) x, hg.nbr u (h x)]

/-! ### Translations -/

theorem bc_sym_add (v : Site d) : BCSym (fun x : Site d => x + v) := by
  refine bc_sym_of_inv _ (fun x => x - v) (fun x => by simp) (fun x => by simp) ?_ ?_ ?_
  · intro x y hxy
    obtain ⟨i, hi | hi⟩ := hxy
    · exact ⟨i, Or.inl (by rw [hi]; abel)⟩
    · exact ⟨i, Or.inr (by rw [hi]; abel)⟩
  · intro x y hxy
    obtain ⟨i, hi | hi⟩ := hxy
    · exact ⟨i, Or.inl (by rw [hi]; abel)⟩
    · exact ⟨i, Or.inr (by rw [hi]; abel)⟩
  · intro u x
    simp only [nbrSumZ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_right_comm, sub_add_eq_add_sub, add_sub_right_comm]

/-! ### Coordinate permutations -/

theorem bc_unit_comp_perm (σ : Equiv.Perm (Fin d)) (i : Fin d) :
    (fun l => unit i (σ l)) = unit (σ.symm i) := by
  funext l
  simp only [unit, Pi.single_apply]
  congr 1
  exact propext (σ.apply_eq_iff_eq_symm_apply)

theorem bc_sym_perm (σ : Equiv.Perm (Fin d)) : BCSym (fun (x : Site d) (l : Fin d) => x (σ l)) := by
  have key : ∀ (σ : Equiv.Perm (Fin d)) (x y : Site d), (lattice d).Adj x y →
      (lattice d).Adj (fun l => x (σ l)) (fun l => y (σ l)) := by
    intro σ x y hxy
    obtain ⟨i, hi | hi⟩ := hxy
    · refine ⟨σ.symm i, Or.inl ?_⟩
      funext l
      have := congrFun hi (σ l)
      simp only [Pi.add_apply] at this ⊢
      rw [this, ← bc_unit_comp_perm σ i]
    · refine ⟨σ.symm i, Or.inr ?_⟩
      funext l
      have := congrFun hi (σ l)
      simp only [Pi.add_apply] at this ⊢
      rw [this, ← bc_unit_comp_perm σ i]
  refine bc_sym_of_inv _ (fun (x : Site d) (l : Fin d) => x (σ.symm l)) (fun x => by simp)
    (fun x => by simp) (key σ) (key σ.symm) ?_
  intro u x
  simp only [nbrSumZ]
  have hl : ∀ i : Fin d, (fun l => (x + unit i) (σ l)) = (fun l => x (σ l)) + unit (σ.symm i) := by
    intro i
    funext l
    have := congrFun (bc_unit_comp_perm σ i) l
    simp only [Pi.add_apply] at this ⊢
    rw [this]
  have hl' : ∀ i : Fin d, (fun l => (x - unit i) (σ l)) = (fun l => x (σ l)) - unit (σ.symm i) := by
    intro i
    funext l
    have := congrFun (bc_unit_comp_perm σ i) l
    simp only [Pi.sub_apply] at this ⊢
    rw [this]
  simp only [hl, hl']
  exact Equiv.sum_comp σ.symm
    (fun i => u ((fun l => x (σ l)) + unit i) + u ((fun l => x (σ l)) - unit i))

/-! ### Reflections -/

/-- The reflection `x_i ↦ c - x_i` of `ℤ^d`. -/
def bcRefl (i : Fin d) (c : ℤ) (x : Site d) : Site d := Function.update x i (c - x i)

theorem bcRefl_apply (i : Fin d) (c : ℤ) (x : Site d) (l : Fin d) :
    bcRefl i c x l = if l = i then c - x i else x l := by
  simp only [bcRefl, Function.update_apply]

theorem bcRefl_add_unit (i : Fin d) (c : ℤ) (x : Site d) (m : Fin d) :
    bcRefl i c (x + unit m) = if m = i then bcRefl i c x - unit i else bcRefl i c x + unit m := by
  funext l
  by_cases hm : m = i
  · subst hm
    by_cases hl : l = m
    · subst hl; simp [bcRefl_apply, unit]; ring
    · simp [bcRefl_apply, unit, hl]
  · by_cases hl : l = i
    · subst hl; simp [bcRefl_apply, unit, hm, Ne.symm hm]
    · simp [bcRefl_apply, unit, hm, hl]

theorem bcRefl_sub_unit (i : Fin d) (c : ℤ) (x : Site d) (m : Fin d) :
    bcRefl i c (x - unit m) = if m = i then bcRefl i c x + unit i else bcRefl i c x - unit m := by
  funext l
  by_cases hm : m = i
  · subst hm
    by_cases hl : l = m
    · subst hl; simp [bcRefl_apply, unit]; ring
    · simp [bcRefl_apply, unit, hl]
  · by_cases hl : l = i
    · subst hl; simp [bcRefl_apply, unit, hm, Ne.symm hm]
    · simp [bcRefl_apply, unit, hm, hl]

theorem bcRefl_invol (i : Fin d) (c : ℤ) (x : Site d) : bcRefl i c (bcRefl i c x) = x := by
  funext l
  by_cases hl : l = i
  · subst hl; simp [bcRefl_apply]
  · simp [bcRefl_apply, hl]

theorem bc_sym_refl (i : Fin d) (c : ℤ) : BCSym (bcRefl i c) := by
  have key : ∀ x y : Site d, (lattice d).Adj x y →
      (lattice d).Adj (bcRefl i c x) (bcRefl i c y) := by
    intro x y hxy
    obtain ⟨m, hm | hm⟩ := hxy
    · subst hm
      rw [bcRefl_add_unit]
      by_cases hmi : m = i
      · subst hmi
        rw [if_pos rfl]
        exact ⟨m, Or.inr (by abel)⟩
      · rw [if_neg hmi]
        exact ⟨m, Or.inl rfl⟩
    · subst hm
      rw [bcRefl_add_unit]
      by_cases hmi : m = i
      · subst hmi
        rw [if_pos rfl]
        exact ⟨m, Or.inl (by abel)⟩
      · rw [if_neg hmi]
        exact ⟨m, Or.inr rfl⟩
  refine bc_sym_of_inv _ (bcRefl i c) (bcRefl_invol i c) (bcRefl_invol i c) key key ?_
  intro u x
  simp only [nbrSumZ]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [bcRefl_add_unit, bcRefl_sub_unit]
  by_cases hmi : m = i
  · simp only [hmi, if_true]
    ring
  · simp only [hmi, if_false]

/-! ### The frozen odometer commutes with lattice symmetries -/

/-- The `S`-frozen odometer commutes with lattice symmetries. -/
theorem bc_fodo_comp {h : Site d → Site d} (hs : BCSym h) (S : Set (Site d))
    (η w0 : Site d → ℤ) (t : ℕ) (x : Site d) :
    fodo (h ⁻¹' S) (fun y => η (h y)) (fun y => w0 (h y)) t x = fodo S η w0 t (h x) := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    rw [fodo_succ, fodo_succ]
    by_cases hx : h x ∈ S
    · rw [if_pos (show x ∈ h ⁻¹' S from hx), if_pos hx]
    · rw [if_neg (show x ∉ h ⁻¹' S from hx), if_neg hx, ih x]
      congr 2
      simp only [fconf, lap]
      have hfun : fodo (h ⁻¹' S) (fun y => η (h y)) (fun y => w0 (h y)) t
          = fun y => fodo S η w0 t (h y) := funext ih
      rw [hfun, hs.nbr (fodo S η w0 t) x]

/-- Closure commutes with preimages under lattice symmetries. -/
theorem bc_closureN_preimage {h : Site d → Site d} (hs : BCSym h) (A : Set (Site d)) :
    h ⁻¹' closureN A = closureN (h ⁻¹' A) := by
  ext x
  simp only [closureN, outerBoundary, Set.mem_preimage, Set.mem_union, Set.mem_setOf_eq]
  refine or_congr Iff.rfl (and_congr Iff.rfl ⟨?_, ?_⟩)
  · rintro ⟨y, hy, hadj⟩
    obtain ⟨y', rfl⟩ := hs.bij.2 y
    exact ⟨y', hy, (hs.adj x y').1 hadj⟩
  · rintro ⟨y, hy, hadj⟩
    exact ⟨h y, hy, (hs.adj x y).2 hadj⟩

/-- Crossing transports along lattice symmetries that carry the tile and the face over. -/
theorem bc_crossed_transport {h : Site d → Site d} (hs : BCSym h) (η : Site d → ℤ)
    (k k' : Fin d → ℕ) (j j' : Site d) (i i' : Fin d) (hi hi' : Bool)
    (hprod : ∏ l, k l = ∏ l, k' l)
    (hT : h ⁻¹' rboxShift k j = rboxShift k' j')
    (hF : h ⁻¹' faceOut k j i hi = faceOut k' j' i' hi')
    (hc : CrossedInDirection (fun y => η (h y)) k' j' i' hi') :
    CrossedInDirection η k j i hi := by
  intro t ht x hx
  obtain ⟨y, rfl⟩ := hs.bij.2 x
  have hy : y ∈ rboxShift k' j' := by rw [← hT]; exact hx
  have h1 := hc t (by rw [← hprod]; exact ht) y hy
  have h2 := bc_fodo_comp hs ((rboxShift k j)ᶜ) η
    (Set.indicator (faceOut k j i hi) (1 : Site d → ℤ)) t y
  rw [show h ⁻¹' (rboxShift k j)ᶜ = (rboxShift k' j')ᶜ by rw [Set.preimage_compl, hT]] at h2
  have h3 : (fun y => Set.indicator (faceOut k j i hi) (1 : Site d → ℤ) (h y))
      = Set.indicator (faceOut k' j' i' hi') (1 : Site d → ℤ) := by
    rw [← hF]
    funext z
    by_cases hz : h z ∈ faceOut k j i hi
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (show z ∈ h ⁻¹' faceOut k j i hi from hz)]
      rfl
    · rw [Set.indicator_of_notMem hz,
        Set.indicator_of_notMem (show z ∉ h ⁻¹' faceOut k j i hi from hz)]
  rw [h3] at h2
  rw [← h2]
  exact h1

/-- The law of a constant product measure is invariant under a lattice symmetry. -/
theorem bc_map_infinitePi {h : Site d → Site d} (hs : BCSym h) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] :
    (Measure.infinitePi fun _ : Site d => ν).map (fun (η : Site d → ℤ) (x : Site d) => η (h x))
      = Measure.infinitePi fun _ : Site d => ν := by
  have := MeasureTheory.Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Site d => ν) hs.bij.1
  simpa using this

/-! ### Tiles and faces under translations and direction changes -/

theorem bc_shift_rbox (k : Fin d → ℕ) (j : Site d) :
    (fun x : Site d => x + fun l => (k l : ℤ) * j l) ⁻¹' rboxShift k j = rboxShift k 0 := by
  ext x
  simp only [Set.mem_preimage, rboxShift, Set.mem_setOf_eq, Pi.add_apply, Pi.zero_apply,
    mul_zero, add_zero, zero_add]
  constructor
  · intro H l
    have := H l
    constructor <;> linarith [this.1, this.2]
  · intro H l
    have := H l
    constructor <;> linarith [this.1, this.2]

theorem bc_shift_face (k : Fin d → ℕ) (j : Site d) (i : Fin d) (hi : Bool) :
    (fun x : Site d => x + fun l => (k l : ℤ) * j l) ⁻¹' faceOut k j i hi
      = faceOut k 0 i hi := by
  ext x
  simp only [faceOut, Set.preimage_inter]
  rw [bc_closureN_preimage (bc_sym_add (fun l => (k l : ℤ) * j l)), bc_shift_rbox]
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, Pi.add_apply, Pi.zero_apply,
    mul_zero, zero_add]
  refine and_congr Iff.rfl ?_
  cases hi
  · simp
  · simp
    constructor <;> intro h <;> linarith

theorem bc_faceOut_zero (n : ℕ) (i : Fin d) (hi : Bool) :
    faceOut (fun _ : Fin d => n) (0 : Site d) i hi
      = closureN (rboxShift (fun _ : Fin d => n) 0) ∩
          {x | x i = if hi then (n : ℤ) + 1 else 0} := by
  simp [faceOut]

theorem bc_swap_rbox (n : ℕ) (a i : Fin d) :
    (fun (x : Site d) (l : Fin d) => x (Equiv.swap a i l)) ⁻¹' rboxShift (fun _ : Fin d => n) 0
      = rboxShift (fun _ : Fin d => n) 0 := by
  ext x
  simp only [Set.mem_preimage, rboxShift, Set.mem_setOf_eq]
  constructor
  · intro H l
    simpa [Equiv.swap_apply_self] using H (Equiv.swap a i l)
  · intro H l
    exact H _

theorem bc_refl_rbox (n : ℕ) (i : Fin d) :
    bcRefl i ((n : ℤ) + 1) ⁻¹' rboxShift (fun _ : Fin d => n) 0
      = rboxShift (fun _ : Fin d => n) 0 := by
  have key : ∀ y : Site d, y ∈ rboxShift (fun _ : Fin d => n) 0 →
      bcRefl i ((n : ℤ) + 1) y ∈ rboxShift (fun _ : Fin d => n) 0 := by
    intro y hy l
    have := hy l
    simp only [mul_zero, add_zero, zero_add, Pi.zero_apply] at this ⊢
    rw [bcRefl_apply]
    by_cases hl : l = i
    · subst hl
      rw [if_pos rfl]
      constructor <;> linarith [this.1, this.2]
    · rw [if_neg hl]
      exact this
  ext y
  simp only [Set.mem_preimage]
  refine ⟨fun h => ?_, key y⟩
  have := key _ h
  rwa [bcRefl_invol] at this

/-- For every direction `i` and face `hi` there is a lattice symmetry fixing the base box
and carrying the face `(i, hi)` to the low face in direction `a`. -/
theorem bc_exists_dir_sym (n : ℕ) (a i : Fin d) (hi : Bool) :
    ∃ g : Site d → Site d, BCSym g ∧
      g ⁻¹' rboxShift (fun _ : Fin d => n) 0 = rboxShift (fun _ : Fin d => n) 0 ∧
      g ⁻¹' faceOut (fun _ : Fin d => n) 0 i hi = faceOut (fun _ : Fin d => n) 0 a false := by
  have hsw := bc_sym_perm (Equiv.swap a i)
  cases hi with
  | false =>
    refine ⟨fun (x : Site d) (l : Fin d) => x (Equiv.swap a i l), hsw, bc_swap_rbox n a i, ?_⟩
    rw [bc_faceOut_zero, bc_faceOut_zero, Set.preimage_inter,
      bc_closureN_preimage hsw, bc_swap_rbox]
    ext x
    simp [Equiv.swap_apply_right]
  | true =>
    have hcomp := bc_sym_comp (bc_sym_refl i ((n : ℤ) + 1)) hsw
    have hR : (fun x : Site d => bcRefl i ((n : ℤ) + 1) (fun l => x (Equiv.swap a i l)))
        ⁻¹' rboxShift (fun _ : Fin d => n) 0 = rboxShift (fun _ : Fin d => n) 0 := by
      ext x
      have h1 : bcRefl i ((n : ℤ) + 1) (fun l => x (Equiv.swap a i l))
            ∈ rboxShift (fun _ : Fin d => n) 0
          ↔ (fun l => x (Equiv.swap a i l)) ∈ rboxShift (fun _ : Fin d => n) 0 := by
        rw [← Set.mem_preimage (f := bcRefl i ((n : ℤ) + 1)), bc_refl_rbox]
      have h2 : (fun l => x (Equiv.swap a i l)) ∈ rboxShift (fun _ : Fin d => n) 0
          ↔ x ∈ rboxShift (fun _ : Fin d => n) 0 := by
        rw [← Set.mem_preimage (f := fun (x : Site d) (l : Fin d) => x (Equiv.swap a i l)),
          bc_swap_rbox]
      exact h1.trans h2
    refine ⟨fun x => bcRefl i ((n : ℤ) + 1) (fun l => x (Equiv.swap a i l)), hcomp, hR, ?_⟩
    rw [bc_faceOut_zero, bc_faceOut_zero, Set.preimage_inter, bc_closureN_preimage hcomp, hR]
    ext x
    simp [bcRefl_apply, Equiv.swap_apply_right]

/-- **Crossing transport.**  For the constant box of side `n`, every tile `j`, direction `i` and
face `hi`, there is a lattice symmetry `h` such that crossing of the base box `j = 0` in the
direction `a` through its low face, for the background `η ∘ h`, gives crossing of the tile
`j` through the face `(i, hi)` for `η`. -/
theorem bc_exists_sym_for_face (n : ℕ) (a i : Fin d) (hi : Bool) (j : Site d) :
    ∃ h : Site d → Site d, BCSym h ∧ ∀ η : Site d → ℤ,
      CrossedInDirection (fun y => η (h y)) (fun _ : Fin d => n) 0 a false →
        CrossedInDirection η (fun _ : Fin d => n) j i hi := by
  obtain ⟨g, hg, hgR, hgF⟩ := bc_exists_dir_sym n a i hi
  have hadd := bc_sym_add (d := d) (fun l => ((fun _ : Fin d => n) l : ℤ) * j l)
  refine ⟨fun x => g x + fun l => ((fun _ : Fin d => n) l : ℤ) * j l,
    bc_sym_comp hadd hg, fun η hc => ?_⟩
  refine bc_crossed_transport (bc_sym_comp hadd hg) η (fun _ : Fin d => n) (fun _ : Fin d => n)
    j 0 i a hi false rfl ?_ ?_ hc
  · show g ⁻¹' ((fun x : Site d => x + fun l => ((fun _ : Fin d => n) l : ℤ) * j l) ⁻¹'
      rboxShift (fun _ : Fin d => n) j) = _
    rw [bc_shift_rbox, hgR]
  · show g ⁻¹' ((fun x : Site d => x + fun l => ((fun _ : Fin d => n) l : ℤ) * j l) ⁻¹'
      faceOut (fun _ : Fin d => n) j i hi) = _
    rw [bc_shift_face, hgF]
