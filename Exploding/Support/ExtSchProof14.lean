/-
The dimensional obstruction to the base scale.

`xsch8_Base d p` is exactly the finite-volume statement of Schonmann's theorem:
some cube is internally spanned with probability at least `1 - 2^{-2d}`.  It is
the last open claim of the renormalization scheme.

The renormalization recursion `xsch8_Recursion d p` (proved in `ExtSchProof12`)
relates `xsch8_a d p (2 * n)` to `xsch8_a d p n` *at the same dimension* `d`, and
the one-dimensional base `xsch8_Base 1 p` (proved in `ExtSchProof13`) is a
statement about `xsch8_a 1 p`.  For `d ≥ 2` these two functions are unrelated:
`xsch8_a d p` and `xsch8_a 1 p` are built from the measures `xsch_mu d p` and
`xsch_mu 1 p` on the different site sets `Fin d → ℤ` and `Fin 1 → ℤ`, and no
lemma in the development compares them.  Consequently the recursion gives no
access to the one-dimensional base, and no dimension-local argument can supply
the base: any nonnegative sequence obeying the recursion with `1 < C` may be
identically `1`, for which no scale has `C * a < 1`.

We record

* `xsch14_recursion_not_sufficient`, the precise refutation of "recursion alone
  implies a base scale";
* `xsch14_base_iff_span`, the reformulation of the base as a spanning-probability
  statement (`xsch13_sp_compl`);
* `xsch14_base_scale_one`, the unconditional base for `p` close to `1` (scale one,
  where the cube is a single site and occupancy alone spans it);
* `xsch14_base_of_Percolates`, the sharpest reduction, to the finite-volume
  percolation estimate `xsch13_Percolates`;
* `xsch14_schonmann_of_blockPercolation`, the conditional assembly of the target.

The genuine missing input remains the finite-volume percolation estimate
(`a n → 0`), i.e. the coarse graining to supercritical block percolation; it is
not a consequence of the recursion plus the one-dimensional base.
-/
import Exploding.Support.ExtSchProof13

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

/-- The recursion alone does not force a base scale.  For any `C > 1` the
nonnegative sequence `a ≡ 1` satisfies `a (2 * n) ≤ C * a n ^ 2` while
`C * a n = C > 1` at every scale. -/
theorem xsch14_recursion_not_sufficient (C : ℝ) (hC : 1 < C) :
    ¬ (∀ a : ℕ → ℝ, (∀ n, 0 ≤ a n) → (∀ n, a (2 * n) ≤ C * (a n) ^ 2) →
        ∃ n0, C * a n0 < 1) := by
  intro h
  have h2 : ∀ n, (fun _ : ℕ => (1 : ℝ)) (2 * n) ≤ C * ((fun _ : ℕ => (1 : ℝ)) n) ^ 2 := by
    intro n
    show (1 : ℝ) ≤ C * (1 : ℝ) ^ 2
    nlinarith [hC.le]
  obtain ⟨n0, hn0⟩ := h (fun _ : ℕ => (1 : ℝ)) (fun _ => zero_le_one) h2
  have hn0' : C * 1 < 1 := hn0
  linarith

/-- Reformulation: the base scale says exactly that some cube is internally
spanned with probability exceeding `1 - 2^{-2 d}`. -/
theorem xsch14_base_iff_span {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)] :
    xsch8_Base d p ↔ ∃ n : ℕ, (xsch_mu d p).real
        {η | xsch_Sp (Finset.univ : Finset (Fin d)) (cube d n) η}
          > 1 - 1 / (2 : ℝ) ^ (2 * d) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (2 * d) := by positivity
  have ht : (1 / (2 : ℝ) ^ (2 * d)) * (2 : ℝ) ^ (2 * d) = 1 := by field_simp
  have key : ∀ n : ℕ, (xsch_mu d p).real
      {η | xsch_Sp (Finset.univ : Finset (Fin d)) (cube d n) η} = 1 - xsch8_a d p n :=
    fun n => xsch13_sp_compl n
  rw [xsch8_Base]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [key n]; nlinarith [hn, hpos, ht]⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [key n] at hn; nlinarith [hn, hpos, ht]⟩

/-- **Scale one.**  At `n = 1` the cube is a single site, so it is spanned as
soon as that site is occupied.  Hence the base holds whenever
`p > 1 - 2^{-2d}`. -/
theorem xsch14_base_scale_one {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)] (hd : 1 ≤ d)
    (hp : 1 - 1 / (2 : ℝ) ^ (2 * d) < p) : xsch8_Base d p := by
  have hcube : cube d 1 = {fun _ : Fin d => (1 : ℤ)} := by
    ext x
    simp only [cube, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      funext i
      have h1 := (h i).1
      have h2 := (h i).2
      omega
    · intro h i
      rw [h]
      exact ⟨le_rfl, le_rfl⟩
  have hsub : {η : Site d → ℤ | η (fun _ : Fin d => (1 : ℤ)) = 2 * (d : ℤ)}
      ⊆ {η | xsch_Sp (Finset.univ : Finset (Fin d)) (cube d 1) η} := by
    intro η hη
    rw [hcube]
    exact xsch_Sp_of_occ fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hη
  have hocc : (xsch_mu d p).real
      {η : Site d → ℤ | η (fun _ : Fin d => (1 : ℤ)) = 2 * (d : ℤ)} = p := by
    have h := xsch_occ_prob (d := d) (p := p) hd ({(fun _ : Fin d => (1 : ℤ))} : Finset (Site d))
    rw [Finset.card_singleton, pow_one] at h
    simpa using h
  have hge : (xsch_mu d p).real
      {η | xsch_Sp (Finset.univ : Finset (Fin d)) (cube d 1) η} ≥ p := by
    have hmono := measureReal_mono hsub (measure_ne_top (xsch_mu d p) _)
    linarith [hocc, hmono]
  rw [xsch14_base_iff_span]
  exact ⟨1, by linarith⟩

/-- **The sharpest reduction.**  The base scale follows from the finite-volume
percolation estimate `xsch13_Percolates` (`a n → 0`). -/
theorem xsch14_base_of_Percolates {p : ℝ} [Fact (0 ≤ p ∧ p ≤ 1)]
    (h : xsch13_Percolates d p) : xsch8_Base d p :=
  xsch13_base_of_Percolates h

/-- **Conditional assembly.**  The coarse block-percolation estimate implies the
target `Exploding.External.SchonmannBootstrap`. -/
theorem xsch14_schonmann_of_blockPercolation
    (h : ∀ d : ℕ, 1 ≤ d → ∀ p : ℝ, 0 < p → p < 1 → xsch7_BlockPercolation d p) :
    Exploding.External.SchonmannBootstrap :=
  xsch7_schonmann_of_blockPercolation h

end Exploding
