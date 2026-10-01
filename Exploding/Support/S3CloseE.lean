/-
Proposition 5.1 (generalized last wave), closeness of the arrival times, part E:
the lengths `Pn`, `Z` and the lighting times are powers of the logarithm, with an exponent that
depends only on `d` and on the path-filling exponent.
-/
import Exploding.Support.S3CloseD

open Exploding LatticeProb MeasureTheory Filter

namespace Exploding

/-- The exponent of the polylogarithmic bounds: it depends only on `d` and `γp`. -/
noncomputable def s3k_Etop (d : ℕ) (γp : ℝ) : ℝ :=
  (d : ℝ) * ((d : ℝ) * (5 / 2) + γp + (γp + 5))

theorem s3k_PL_r2 : s3k_PL (fun n : ℕ => ((glws_r2 n : ℕ) : ℝ)) (5 / 2) := by
  unfold glws_r2
  exact s3k_PL_ceil (s3k_PL_log2' (5 / 2) (by norm_num)) (by norm_num)

theorem s3k_PL_Pn (γp : ℝ) (hγp : 0 < γp) (kmax d : ℕ) :
    s3k_PL (fun n : ℕ => ((glws_Pn γp kmax d n : ℕ) : ℝ)) ((d : ℝ) * (5 / 2) + γp) := by
  have h1 : s3k_PL (fun n : ℕ => ((glws_r2 n : ℕ) : ℝ) + 2) (5 / 2) :=
    s3k_PL_add_same s3k_PL_r2 (s3k_PL_mono (s3k_PL_const 2 (by norm_num)) (by norm_num))
  have h2 := s3k_PL_nsmul h1 (kmax : ℝ) (Nat.cast_nonneg _)
  have h3 := s3k_PL_pow h2 d
  have h4 : s3k_PL (fun n : ℕ => ((⌈Real.log ((2 * n : ℕ) : ℝ) ^ γp⌉₊ : ℕ) : ℝ)) γp :=
    s3k_PL_ceil (s3k_PL_log2 γp hγp.le) hγp.le
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have h5 := s3k_PL_add_same
    (s3k_PL_mono h3 (e' := (d : ℝ) * (5 / 2) + γp) (by nlinarith))
    (s3k_PL_mono h4 (e' := (d : ℝ) * (5 / 2) + γp) (by nlinarith))
  have hfun : (fun n : ℕ => ((glws_Pn γp kmax d n : ℕ) : ℝ)) =
      fun n : ℕ => (((kmax : ℝ) * (((glws_r2 n : ℕ) : ℝ) + 2)) ^ d) +
        ((⌈Real.log ((2 * n : ℕ) : ℝ) ^ γp⌉₊ : ℕ) : ℝ) := by
    funext n
    unfold glws_Pn
    push_cast
    ring
  rw [hfun]
  exact h5

theorem s3k_PL_Z2 (γp : ℝ) (hγp : 0 < γp) :
    s3k_PL (fun n : ℕ => ((glws_Zn γp (2 * n) : ℕ) : ℝ)) (γp + 5) := by
  unfold glws_Zn
  exact s3k_PL_ceil (s3k_PL_log2 (γp + 5) (by linarith)) (by linarith)

theorem s3k_PL_Z1 (γp : ℝ) (hγp : 0 < γp) :
    s3k_PL (fun n : ℕ => ((glws_Zn γp n : ℕ) : ℝ)) (γp + 5) := by
  unfold glws_Zn
  exact s3k_PL_ceil (s3k_PL_logn (γp + 5) (by linarith)) (by linarith)

theorem s3k_E_ge (d : ℕ) (hd : 1 ≤ d) (γp : ℝ) (hγp : 0 < γp) :
    (d : ℝ) * (5 / 2) + γp ≤ s3k_Etop d γp ∧ (d : ℝ) * ((d : ℝ) * (5 / 2) + γp) ≤ s3k_Etop d γp ∧
      (d : ℝ) * (γp + 5) ≤ s3k_Etop d γp ∧ 0 ≤ s3k_Etop d γp := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  unfold s3k_Etop
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- The lighting time of the far case, after the lit path and the walks. -/
noncomputable def s3k_Tfar (γp : ℝ) (kmax d K A B n : ℕ) : ℕ :=
  glws_Pn γp kmax d n ^ d + K + A * (d * (glws_Pn γp kmax d n + 2 * kmax)) +
    B * glws_Zn γp (2 * n) ^ d

/-- The lighting time of the near case, from the first lit tile. -/
noncomputable def s3k_Tnear (γp : ℝ) (kmax d τ0 J A B n : ℕ) : ℕ :=
  τ0 + A * (J + d * glws_Pn γp kmax d n + d) + B * glws_Zn γp n ^ d

theorem s3k_PL_Tfar (γp : ℝ) (hγp : 0 < γp) (kmax d : ℕ) (hd : 1 ≤ d) (K A B : ℕ) :
    s3k_PL (fun n : ℕ => ((s3k_Tfar γp kmax d K A B n : ℕ) : ℝ)) (s3k_Etop d γp) := by
  obtain ⟨e1, e2, e3, e4⟩ := s3k_E_ge d hd γp hγp
  have hP := s3k_PL_Pn γp hγp kmax d
  have hPd := s3k_PL_mono (s3k_PL_pow hP d) e2
  have hZ := s3k_PL_mono (s3k_PL_pow (s3k_PL_Z2 γp hγp) d) e3
  have hKc := s3k_PL_mono (s3k_PL_const (K : ℝ) (Nat.cast_nonneg _)) e4
  have hmid : s3k_PL (fun n : ℕ => (A : ℝ) * ((d : ℝ) * (((glws_Pn γp kmax d n : ℕ) : ℝ) +
      2 * (kmax : ℝ)))) (s3k_Etop d γp) := by
    have h1 : s3k_PL (fun n : ℕ => ((glws_Pn γp kmax d n : ℕ) : ℝ) + 2 * (kmax : ℝ))
        (s3k_Etop d γp) :=
      s3k_PL_add_same (s3k_PL_mono hP e1)
        (s3k_PL_mono (s3k_PL_const (2 * (kmax : ℝ)) (by positivity)) e4)
    exact s3k_PL_nsmul (s3k_PL_nsmul h1 (d : ℝ) (Nat.cast_nonneg _)) (A : ℝ) (Nat.cast_nonneg _)
  have hfin := s3k_PL_add_same (s3k_PL_add_same (s3k_PL_add_same hPd hKc) hmid)
    (s3k_PL_nsmul hZ (B : ℝ) (Nat.cast_nonneg _))
  have hfun : (fun n : ℕ => ((s3k_Tfar γp kmax d K A B n : ℕ) : ℝ)) =
      fun n : ℕ => (((((glws_Pn γp kmax d n : ℕ) : ℝ) ^ d + (K : ℝ)) +
        (A : ℝ) * ((d : ℝ) * (((glws_Pn γp kmax d n : ℕ) : ℝ) + 2 * (kmax : ℝ)))) +
        (B : ℝ) * (((glws_Zn γp (2 * n) : ℕ) : ℝ) ^ d)) := by
    funext n
    unfold s3k_Tfar
    push_cast
    ring
  rw [hfun]
  exact hfin

theorem s3k_PL_Tnear (γp : ℝ) (hγp : 0 < γp) (kmax d : ℕ) (hd : 1 ≤ d) (τ0 J A B : ℕ) :
    s3k_PL (fun n : ℕ => ((s3k_Tnear γp kmax d τ0 J A B n : ℕ) : ℝ)) (s3k_Etop d γp) := by
  obtain ⟨e1, e2, e3, e4⟩ := s3k_E_ge d hd γp hγp
  have hP := s3k_PL_Pn γp hγp kmax d
  have hZ := s3k_PL_mono (s3k_PL_pow (s3k_PL_Z1 γp hγp) d) e3
  have hτ := s3k_PL_mono (s3k_PL_const (τ0 : ℝ) (Nat.cast_nonneg _)) e4
  have hmid : s3k_PL (fun n : ℕ => (A : ℝ) * (((J : ℝ) + (d : ℝ) * ((glws_Pn γp kmax d n : ℕ) : ℝ))
      + (d : ℝ))) (s3k_Etop d γp) := by
    have h1 : s3k_PL (fun n : ℕ => (J : ℝ) + (d : ℝ) * ((glws_Pn γp kmax d n : ℕ) : ℝ) + (d : ℝ))
        (s3k_Etop d γp) :=
      s3k_PL_add_same
        (s3k_PL_add_same (s3k_PL_mono (s3k_PL_const (J : ℝ) (Nat.cast_nonneg _)) e4)
          (s3k_PL_nsmul (s3k_PL_mono hP e1) (d : ℝ) (Nat.cast_nonneg _)))
        (s3k_PL_mono (s3k_PL_const (d : ℝ) (Nat.cast_nonneg _)) e4)
    exact s3k_PL_nsmul h1 (A : ℝ) (Nat.cast_nonneg _)
  have hfin := s3k_PL_add_same (s3k_PL_add_same hτ hmid)
    (s3k_PL_nsmul hZ (B : ℝ) (Nat.cast_nonneg _))
  have hfun : (fun n : ℕ => ((s3k_Tnear γp kmax d τ0 J A B n : ℕ) : ℝ)) =
      fun n : ℕ => ((τ0 : ℝ) + (A : ℝ) * (((J : ℝ) + (d : ℝ) * ((glws_Pn γp kmax d n : ℕ) : ℝ))
        + (d : ℝ))) + (B : ℝ) * (((glws_Zn γp n : ℕ) : ℝ) ^ d) := by
    funext n
    unfold s3k_Tnear
    push_cast
    ring
  rw [hfun]
  exact hfin

end Exploding
