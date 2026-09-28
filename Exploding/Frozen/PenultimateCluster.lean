/-
Lemma 3.5 of the paper: penultimate clusters are polylogarithmically small.
-/
import Exploding.Support.Vocab
import Exploding.Support.SubPen
import Exploding.Frozen.Renormalization
import Exploding.External.LiggettSchonmannStaceyBoundedDegree
import Exploding.External.MathieuHoles
import Exploding.External.AntalPisztora

open Exploding LatticeProb MeasureTheory

/-- **Lemma 3.5** (`exploding.tex:792-798`, label
`lemma:last_penultimate_cluster`).

"There is a constant `γ > 0` so that for all `n` sufficiently large and
`|x| ≤ n`, `P(x) ⊂ x + [-(log n)^γ, (log n)^γ]^d`."

`γ` is deterministic, so it is bound before `η`; "for all `n` sufficiently
large" is a threshold that may depend on `η`, so it is bound inside.  `|x|` is
the Manhattan norm.

Section 3 runs on the event of Proposition 2.2, so the results the paper cites
for it enter as explicit hypotheses: `hLSSB` (Liggett, Schonmann and Stacey,
Corollary 1.4), `hHole` (Mathieu, Lemma 5.2) and `hChem` (Antal and Pisztora,
Theorem 1.1). -/
-- FROZEN-STATEMENT-BEGIN
theorem Exploding.Frozen.last_penultimate_cluster (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ᵐ η ∂(toyLaw d p), ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ x : Site d, mnorm x ≤ (n : ℤ) →
        ∀ y ∈ penultimateCluster η x, ∀ i, ((|y i - x i| : ℤ) : ℝ) ≤ Real.log n ^ γ
-- FROZEN-STATEMENT-END
:= by
  refine ⟨(5 : ℝ) / 2 + 1, by norm_num, ?_⟩
  obtain ⟨k0, hk0⟩ :=
    Exploding.Frozen.renormalization_properties d hd p hp hp1 hLSSB hHole hChem
  obtain ⟨c, C, hc, hC, hren⟩ := hk0 (max k0 1) (le_max_left _ _)
  filter_upwards [aux_penultimate_bounds d p hp hp1, hren] with η hb hren'
  obtain ⟨Cinf, hCinf, hcomp, hchem⟩ := hren'
  obtain ⟨n0c, hn0c⟩ := hcomp
  refine ⟨max n0c (max 1 (Nat.ceil (Real.exp 2))), ?_⟩
  intro n hn x hx y hy i
  -- the threshold gives `log n ≥ 2`
  have hn0c : n0c ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hne : Nat.ceil (Real.exp 2) ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hlog2 : 2 ≤ Real.log n := by
    have h1 : Real.exp 2 ≤ (n : ℝ) := by
      have := Nat.le_ceil (Real.exp 2)
      exact le_trans this (by exact_mod_cast hne)
    have h2 : Real.log (Real.exp 2) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (Real.exp_pos 2) h1
    rwa [Real.log_exp] at h2
  have hlog0 : 0 ≤ Real.log n := by linarith
  have hlogpow : 0 ≤ Real.log n ^ ((5 : ℝ) / 2) := Real.rpow_nonneg hlog0 _
  -- the penultimate cluster: `y = x`, or a neighbour `y'` of `y` is positive
  rcases hy with hxy | ⟨y', hy'adj, hy'pos⟩
  · rw [hxy]
    have h1 : ((|x i - x i| : ℤ) : ℝ) = 0 := by simp
    rw [h1]
    exact Real.rpow_nonneg hlog0 _
  · -- `pen_box_pos` gives a positive rectangle from `x` to `y'`
    obtain ⟨m, path, h0, hm, hadj, hfin, hpos⟩ :=
      pen_box_pos hd η (fun z => (hb z).1) (fun z => (hb z).2) x y' hy'pos
    sorry
