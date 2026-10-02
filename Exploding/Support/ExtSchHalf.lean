/-
The half-split of a box into `2^d` half-boxes, one for each choice of the lower or the upper half
in every direction, and the L-shape lemma: if all half-boxes but one are internally spanned, the
whole box is.  The faces selected by the missing half-box lie in other half-boxes, so they are
toppled, and the corner growth of the box finishes.  The half-boxes of a near-cube box of size
`s` are near-cubes of size `s / 2`.
-/
import Exploding.Support.ExtSchCorner

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The length of the lower half of the side in direction `i`. -/
def xsh_m (lo hi : Site d) (i : Fin d) : ℤ := (hi i - lo i + 1) / 2

/-- The lower corner of the half-box selected by `σ`. -/
def xsh_lo (lo hi : Site d) (σ : Fin d → Bool) (i : Fin d) : ℤ :=
  if σ i = true then lo i + xsh_m lo hi i else lo i

/-- The upper corner of the half-box selected by `σ`. -/
def xsh_hi (lo hi : Site d) (σ : Fin d → Bool) (i : Fin d) : ℤ :=
  if σ i = true then hi i else lo i + xsh_m lo hi i - 1

/-- The half-box selected by `σ`: the upper half of the side in direction `i` if `σ i`, the lower
half otherwise. -/
def xsh_sub (lo hi : Site d) (σ : Fin d → Bool) : Set (Site d) :=
  xsb_box (xsh_lo lo hi σ) (xsh_hi lo hi σ)

/-- The half-boxes lie in the box. -/
theorem xsh_sub_subset {lo hi : Site d} (hn : ∀ i, 1 ≤ hi i - lo i + 1) (σ : Fin d → Bool) :
    xsh_sub lo hi σ ⊆ xsb_box lo hi := by
  intro x hx i
  have h := hx i
  have hi' := hn i
  simp only [xsh_lo, xsh_hi, xsh_m] at h
  constructor
  · split_ifs at h <;> omega
  · split_ifs at h <;> omega

/-- The half-boxes of a near-cube box of size `s` are near-cubes of size `s / 2`. -/
theorem xsh_sub_near {lo hi : Site d} {s : ℕ} (hs : 2 ≤ s)
    (hR : xsb_Near (Finset.univ : Finset (Fin d)) s lo hi) (σ : Fin d → Bool) :
    xsb_Near (Finset.univ : Finset (Fin d)) (s / 2) (xsh_lo lo hi σ) (xsh_hi lo hi σ) := by
  -- `hs` is not needed: the side computation is valid for every `s`.
  have _ := hs
  refine ⟨fun i _ => ?_, fun i hi => absurd (Finset.mem_univ i) hi⟩
  have h := hR.1 i (Finset.mem_univ i)
  have hc : ((s / 2 : ℕ) : ℤ) = (s : ℤ) / 2 := by omega
  rw [hc]
  simp only [xsh_lo, xsh_hi, xsh_m]
  split_ifs <;> omega

/-- Distinct half-boxes are disjoint. -/
theorem xsh_sub_disjoint {lo hi : Site d} (hn : ∀ i, 2 ≤ hi i - lo i + 1)
    {σ σ' : Fin d → Bool} (h : σ ≠ σ') : Disjoint (xsh_sub lo hi σ) (xsh_sub lo hi σ') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  apply h
  funext j
  by_contra hj
  have h1 := (hx j).1
  have h2 := (hx j).2
  have h3 := (hx' j).1
  have h4 := (hx' j).2
  have hnj := hn j
  simp only [xsh_lo, xsh_hi, xsh_m] at h1 h2 h3 h4
  cases hσ : σ j <;> cases hσ' : σ' j <;> simp_all <;> omega

/-- Every site of the box lies in the half-box whose selector records, in each direction, whether
the site is in the upper half. -/
theorem xsh_mem_sub (lo hi x : Site d) (hx : x ∈ xsb_box lo hi) :
    x ∈ xsh_sub lo hi (fun j => decide (lo j + xsh_m lo hi j ≤ x j)) := by
  intro j
  have h := hx j
  simp only [xsh_lo, xsh_hi, decide_eq_true_eq]
  by_cases hj : lo j + xsh_m lo hi j ≤ x j
  · rw [if_pos hj, if_pos hj]
    exact ⟨hj, h.2⟩
  · rw [if_neg hj, if_neg hj]
    exact ⟨h.1, by omega⟩

/-- **L-shape lemma for the half-split.**  If all half-boxes but one are internally spanned,
then the box is internally spanned. -/
theorem xsh_sp_of_all_but_one (hd : 1 ≤ d) {lo hi : Site d} (hn : ∀ i, 2 ≤ hi i - lo i + 1)
    (σ0 : Fin d → Bool) (η : Site d → ℤ)
    (hgood : ∀ σ, σ ≠ σ0 → xsch_Sp (Finset.univ : Finset (Fin d)) (xsh_sub lo hi σ) η) :
    xsch_Sp (Finset.univ : Finset (Fin d)) (xsb_box lo hi) η := by
  refine xsk_corner_growth hd (fun i => by have := hn i; omega) σ0 subset_rfl η ?_
  intro x hx hface
  obtain ⟨i, hfi⟩ := hface
  set σ' : Fin d → Bool := fun j => decide (lo j + xsh_m lo hi j ≤ x j) with hσ'
  have hni := hn i
  have hne : σ' ≠ σ0 := by
    intro heq
    have hii : σ' i = σ0 i := by rw [heq]
    rcases hfi with ⟨hci, hxi⟩ | ⟨hci, hxi⟩
    · have : σ' i = false := by
        simp only [hσ', hxi, xsh_m, decide_eq_false_iff_not]
        omega
      rw [this, hci] at hii
      exact Bool.noConfusion hii
    · have : σ' i = true := by
        simp only [hσ', hxi, xsh_m]
        exact decide_eq_true (by omega)
      rw [this, hci] at hii
      exact Bool.noConfusion hii
  have htop := hgood σ' hne x (xsh_mem_sub lo hi x hx)
  exact xsch_Top_mono (xsh_sub_subset (fun j => by have := hn j; omega) σ') htop

end Exploding
