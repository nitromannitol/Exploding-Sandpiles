/-
Lemma 2.1 of the paper: a path of topplings fills its bounding rectangle.
-/
import Exploding.Support.Vocab
import Exploding.Support.SubFill

open Exploding LatticeProb
/-- **Lemma 2.1** (`paper/corrected-arxiv/exploding-corrected-arxiv.tex:401-405`, label `lemma:local_convexity`).

"Let `A := {z^(i)}` be a finite path `z^(i) ∼ z^(i+1)`.  Let `w_t` denote
`A`-frozen parallel toppling with initial conditions `w_0(x) = 1{x ∈ A}` on the whole
lattice (zero off `A`), `s_0' = η + Δw_0`.  Then, `w_t|_{br(A)} = 1`, for all `t ≥ |br(A)|`."

`fodo A η w₀` evolves `s_t' = η + Δ w_t`, so its initial configuration is the delivered
seed `η + Δ w₀`.

The path is given by its vertices `z 0, …, z m`, consecutive ones adjacent, and
`A` is their image.  Section 2 fixes `η` as in `(1.2)`, so `2d - 2 ≤ η ≤ 2d - 1`.
`w_0 = 1{x ∈ A}` is `Set.indicator A 1`.
`|br(A)|` is the cardinality of the bounding rectangle, whose finiteness is
carried explicitly rather than read through `Set.ncard = 0`. -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.local_convexity (d : ℕ) (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (m : ℕ) (z : ℕ → Site d) (hpath : ∀ i : ℕ, i < m → (lattice d).Adj (z i) (z (i + 1)))
    (A : Set (Site d)) (hA : A = z '' {i : ℕ | i ≤ m})
    (hfin : (br A).Finite) (t : ℕ) (ht : hfin.toFinset.card ≤ t)
    (x : Site d) (hx : x ∈ br A) :
    fodo A η (Set.indicator A 1) t x = 1
-- FROZEN-STATEMENT-END
:= by
  have _hd := hd
  subst hA
  have hcard : (br (z '' {i : ℕ | i ≤ m})).ncard ≤ t := by
    rw [Set.ncard_eq_toFinset_card _ hfin]
    exact ht
  have hmin := br_subset_supp_card (z '' {i : ℕ | i ≤ m}) hfin
    (fillSet_path m z hpath)
  have h1 : fodo (z '' {i : ℕ | i ≤ m}) (fun _ => 2 * (d : ℤ) - 2)
      (Set.indicator (z '' {i : ℕ | i ≤ m}) 1) hfin.toFinset.card x = 1 := hmin hx
  have hmono := fodo_mono_time' (z '' {i : ℕ | i ≤ m}) (fun _ => 2 * (d : ℤ) - 2)
    (Set.indicator (z '' {i : ℕ | i ≤ m}) 1) ht x
  rw [h1] at hmono
  exact local_convexity_wlog_eta (z '' {i : ℕ | i ≤ m}) η hlow hhigh t x
    (le_antisymm (fodo_indicator_le_one _ t x) hmono)
