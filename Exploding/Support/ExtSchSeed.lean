/-
A grid of disjoint blocks of a given side inside a near-cube box, the probability that a box is
fully occupied, and the bound `(1 - π)^N` for the probability that none of `N` independent
disjoint blocks is good when each is good with probability at least `π`.
-/
import Exploding.Support.ExtSchBox
import Exploding.Support.ExtSchProb

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- Lower corner of the block with index `q` in the grid of blocks of side `Lb`. -/
def xsp_blo (J : Finset (Fin d)) (LO : Site d) (Lb : ℕ) (q : J → ℕ) (j : Fin d) : ℤ :=
  if h : j ∈ J then LO j + (Lb : ℤ) * (q ⟨j, h⟩ : ℕ) else LO j

/-- Upper corner of the block with index `q` in the grid of blocks of side `Lb`. -/
def xsp_bhi (J : Finset (Fin d)) (LO : Site d) (Lb : ℕ) (q : J → ℕ) (j : Fin d) : ℤ :=
  if h : j ∈ J then LO j + (Lb : ℤ) * (q ⟨j, h⟩ : ℕ) + (Lb : ℤ) - 1 else LO j

/-- Every block is a near-cube of side `Lb` (all sides exactly `Lb`). -/
theorem xsp_block_near (J : Finset (Fin d)) (LO : Site d) {Lb : ℕ} (_hLb : 1 ≤ Lb) (q : J → ℕ) :
    xsb_Near J Lb (xsp_blo J LO Lb q) (xsp_bhi J LO Lb q) := by
  refine ⟨fun i hi => Or.inl ?_, fun i hi => ?_⟩
  · simp only [xsp_blo, xsp_bhi, dif_pos hi]
    ring
  · simp only [xsp_blo, xsp_bhi, dif_neg hi]

/-- The blocks with index below `s / Lb` lie in the box. -/
theorem xsp_block_subset {J : Finset (Fin d)} {LO HI : Site d} {s Lb : ℕ} (_hLb : 1 ≤ Lb)
    (hR : xsb_Near J s LO HI) (q : J → Fin (s / Lb)) :
    xsb_box (xsp_blo J LO Lb (fun j => (q j : ℕ))) (xsp_bhi J LO Lb (fun j => (q j : ℕ)))
      ⊆ xsb_box LO HI := by
  intro x hx j
  obtain ⟨hx1, hx2⟩ := hx j
  by_cases hj : j ∈ J
  · have hqlt : (q ⟨j, hj⟩ : ℕ) < s / Lb := (q ⟨j, hj⟩).isLt
    have hmul : Lb * ((q ⟨j, hj⟩ : ℕ) + 1) ≤ s :=
      (Nat.mul_le_mul_left Lb hqlt).trans (Nat.mul_div_le s Lb)
    have hmulZ : (Lb : ℤ) * (((q ⟨j, hj⟩ : ℕ) : ℤ) + 1) ≤ (s : ℤ) := by exact_mod_cast hmul
    have hside : (s : ℤ) ≤ HI j - LO j + 1 := by
      rcases hR.1 j hj with h | h <;> omega
    have hnn : (0 : ℤ) ≤ (Lb : ℤ) * ((q ⟨j, hj⟩ : ℕ) : ℤ) :=
      mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    simp only [xsp_blo, xsp_bhi, dif_pos hj] at hx1 hx2
    constructor
    · linarith
    · nlinarith
  · have hthin := hR.2 j hj
    simp only [xsp_blo, xsp_bhi, dif_neg hj] at hx1 hx2
    constructor
    · exact hx1
    · omega

/-- Distinct indices give disjoint blocks. -/
theorem xsp_block_disjoint {J : Finset (Fin d)} {LO : Site d} {s Lb : ℕ} (_hLb : 1 ≤ Lb)
    {q q' : J → Fin (s / Lb)} (h : q ≠ q') :
    Disjoint (xsb_box (xsp_blo J LO Lb (fun j => (q j : ℕ))) (xsp_bhi J LO Lb (fun j => (q j : ℕ))))
      (xsb_box (xsp_blo J LO Lb (fun j => (q' j : ℕ)))
        (xsp_bhi J LO Lb (fun j => (q' j : ℕ)))) := by
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp h
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨h1, h2⟩ := hx j₀.1
  obtain ⟨h1', h2'⟩ := hx' j₀.1
  simp only [xsp_blo, xsp_bhi, dif_pos j₀.2] at h1 h2 h1' h2'
  have hj₀' : (q j₀ : ℕ) ≠ (q' j₀ : ℕ) := fun he => hj₀ (Fin.ext he)
  rcases Nat.lt_or_gt_of_ne hj₀' with hlt | hlt
  · have hmul : Lb * ((q j₀ : ℕ) + 1) ≤ Lb * (q' j₀ : ℕ) := Nat.mul_le_mul_left Lb hlt
    have hmulZ : (Lb : ℤ) * (((q j₀ : ℕ) : ℤ) + 1) ≤ (Lb : ℤ) * ((q' j₀ : ℕ) : ℤ) := by
      exact_mod_cast hmul
    linarith
  · have hmul : Lb * ((q' j₀ : ℕ) + 1) ≤ Lb * (q j₀ : ℕ) := Nat.mul_le_mul_left Lb hlt
    have hmulZ : (Lb : ℤ) * (((q' j₀ : ℕ) : ℤ) + 1) ≤ (Lb : ℤ) * ((q j₀ : ℕ) : ℤ) := by
      exact_mod_cast hmul
    linarith

/-- There are `M ^ |J|` indices. -/
theorem xsp_card_grid (J : Finset (Fin d)) (M : ℕ) :
    Fintype.card (J → Fin M) = M ^ J.card := by
  simp

/-- A box with all sides `ℓ` along `J` and thin off `J` has `ℓ ^ |J|` sites. -/
theorem xsp_box_ncard {J : Finset (Fin d)} {lo hi : Site d} {ℓ : ℕ}
    (hside : ∀ i ∈ J, hi i - lo i + 1 = (ℓ : ℤ)) (hthin : ∀ i ∉ J, lo i = hi i) :
    (xsb_box lo hi).ncard = ℓ ^ J.card := by
  have h : xsb_box lo hi = ↑(Fintype.piFinset (fun i => Finset.Icc (lo i) (hi i))) := by
    ext x
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    simp only [xsb_box, Set.mem_setOf_eq, Finset.mem_Icc]
  have hcard : ∀ i, (hi i + 1 - lo i).toNat = if i ∈ J then ℓ else 1 := fun i => by
    by_cases hi' : i ∈ J
    · rw [if_pos hi']
      have := hside i hi'
      omega
    · rw [if_neg hi']
      have := hthin i hi'
      omega
  rw [h, Set.ncard_coe_finset, Fintype.card_piFinset]
  simp only [Int.card_Icc, hcard]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

variable {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)]

/-- The probability that such a box is fully occupied is `p ^ (ℓ ^ |J|)`. -/
theorem xsp_seed_prob (hd : 1 ≤ d) {J : Finset (Fin d)} {lo hi : Site d} {ℓ : ℕ}
    (hside : ∀ i ∈ J, hi i - lo i + 1 = (ℓ : ℤ)) (hthin : ∀ i ∉ J, lo i = hi i) :
    (xsch_mu d p).real {η | ∀ x ∈ xsb_box lo hi, η x = 2 * (d : ℤ)} = p ^ (ℓ ^ J.card) := by
  have hfin := xsb_box_finite lo hi
  have hset : {η : Site d → ℤ | ∀ x ∈ xsb_box lo hi, η x = 2 * (d : ℤ)}
      = {η | ∀ x ∈ hfin.toFinset, η x = 2 * (d : ℤ)} := by
    ext η
    simp only [Set.mem_setOf_eq, Set.Finite.mem_toFinset]
  rw [hset, xsch_occ_prob hd, ← Set.ncard_eq_toFinset_card _ hfin, xsp_box_ncard hside hthin]

/-- If events determined on disjoint finite sets are each good with probability at least `π`,
the probability that none is good is at most `(1 - π)` to the number of events. -/
theorem xsp_none_good_le {ι : Type*} [Fintype ι] (A : ι → Set (Site d))
    (hfin : ∀ i, (A i).Finite) (hdisj : Pairwise (Function.onFun Disjoint A))
    (F : ι → Set (Site d → ℤ)) (hF : ∀ i, xsch_Det (A i) (F i)) {π : ℝ}
    (hπ : ∀ i, π ≤ (xsch_mu d p).real (F i)) :
    (xsch_mu d p).real (⋂ i, (F i)ᶜ) ≤ (1 - π) ^ Fintype.card ι := by
  have h := xsch_indep_iInter (p := p) A hfin hdisj (fun i => (F i)ᶜ)
    (fun i => (hF i).compl) Finset.univ
  have hU : (⋂ i ∈ (Finset.univ : Finset ι), (F i)ᶜ) = ⋂ i, (F i)ᶜ := by simp
  rw [hU] at h
  rw [h]
  have hle : ∀ i ∈ (Finset.univ : Finset ι), (xsch_mu d p).real (F i)ᶜ ≤ 1 - π := fun i _ => by
    rw [measureReal_compl ((hF i).measurableSet (hfin i)), probReal_univ]
    linarith [hπ i]
  calc ∏ i ∈ (Finset.univ : Finset ι), (xsch_mu d p).real (F i)ᶜ
      ≤ ∏ _i ∈ (Finset.univ : Finset ι), (1 - π) :=
        Finset.prod_le_prod (fun i _ => measureReal_nonneg) hle
    _ = (1 - π) ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]

end Exploding
