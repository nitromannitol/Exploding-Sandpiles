/-
The last-wave vocabulary of Section 3 of `paper/exploding.tex`, beyond the
definitions of `Exploding.Support.Vocab`: the neighbours of a site, the `n`-wave
along a stretch of time, the penultimate wave at its centre and off its cluster,
and the shape of the `ℕ∞`-valued arrival times.

The one substantive statement here is that the penultimate wave vanishes off its
own penultimate cluster.  At a site `x` outside the cluster the wave equation
reads `ũ(x) = ⌊(∑_{y ∼ x} ũ(y) + η(x)) / 2d⌋`, so a positive value would force
`∑_{y ∼ x} ũ(y) ≥ 1` because `η(x) ≤ 2d - 1`, and then some neighbour of `x`
would carry positive mass, putting `x` in the cluster by `(3.3)`.  This is the
step the proof of Lemma 3.4 reads as "`ũ^{(b)}` is zero on `∂°P(b)`".
-/
import Exploding.Support.Vocab

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-! ### Neighbours -/

/-- `x + e_i` is a neighbour of `x`. -/
theorem adj_add_unit (x : Site d) (i : Fin d) : (lattice d).Adj (x + unit i) x :=
  ⟨i, Or.inr rfl⟩

/-- `x - e_i` is a neighbour of `x`. -/
theorem adj_sub_unit (x : Site d) (i : Fin d) : (lattice d).Adj (x - unit i) x :=
  ⟨i, Or.inl (by abel)⟩

/-- A nonnegative function has a nonnegative neighbour sum. -/
theorem nbrSumZ_nonneg (u : Site d → ℤ) (hu : ∀ y, 0 ≤ u y) (x : Site d) :
    0 ≤ nbrSumZ u x :=
  Finset.sum_nonneg fun _ _ => add_nonneg (hu _) (hu _)

/-- Comparing neighbour sums needs the comparison only at the neighbours. -/
theorem nbrSumZ_mono_adj (u v : Site d → ℤ) (x : Site d)
    (h : ∀ y, (lattice d).Adj y x → u y ≤ v y) : nbrSumZ u x ≤ nbrSumZ v x := by
  simp only [nbrSumZ]
  refine Finset.sum_le_sum ?_
  intro i _
  exact add_le_add (h _ (adj_add_unit x i)) (h _ (adj_sub_unit x i))

/-- A positive neighbour sum of a nonnegative function is carried by a neighbour. -/
theorem exists_adj_pos_of_nbrSumZ_pos (u : Site d → ℤ) (hu : ∀ y, 0 ≤ u y) (x : Site d)
    (h : 0 < nbrSumZ u x) : ∃ y, (lattice d).Adj y x ∧ 0 < u y := by
  by_contra hcon
  have hcon' : ∀ y, (lattice d).Adj y x → u y ≤ 0 := fun y hy =>
    not_lt.mp fun hpos => hcon ⟨y, hy, hpos⟩
  have hz : ∀ i : Fin d, u (x + unit i) + u (x - unit i) = 0 := by
    intro i
    have h1 : u (x + unit i) = 0 := le_antisymm (hcon' _ (adj_add_unit x i)) (hu _)
    have h2 : u (x - unit i) = 0 := le_antisymm (hcon' _ (adj_sub_unit x i)) (hu _)
    rw [h1, h2]; ring
  have hs : nbrSumZ u x = 0 := by
    simp only [nbrSumZ]
    exact Finset.sum_eq_zero fun i _ => hz i
  rw [hs] at h
  exact lt_irrefl 0 h

/-! ### The `n`-wave along a stretch of time -/

/-- On a nonnegative background the `n`-wave is nondecreasing along any stretch
of time. -/
theorem wave_mono_time (η : Site d → ℤ) (hη : ∀ y, 0 ≤ η y) (hd : (0 : ℤ) < 2 * (d : ℤ))
    (n : ℕ) (z : Site d) {s t : ℕ} (hst : s ≤ t) (x : Site d) :
    wave η n z s x ≤ wave η n z t x := by
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih => exact le_trans ih (wave_mono_t η hη hd n z t x)

/-! ### The penultimate cluster -/

/-- The centre lies in its own penultimate cluster, by `(3.3)`. -/
theorem centre_mem_penultimateCluster (η : Site d → ℤ) (z : Site d) :
    z ∈ penultimateCluster η z := Or.inl rfl

/-- A neighbour of a site carrying penultimate mass lies in the penultimate
cluster, by `(3.3)`. -/
theorem mem_penultimateCluster_of_adj (η : Site d → ℤ) (z x y : Site d)
    (hadj : (lattice d).Adj y x) (hy : 0 < penultimateWave η z y) :
    x ∈ penultimateCluster η z := Or.inr ⟨y, hadj, hy⟩

/-! ### The penultimate wave -/

/-- On a nonnegative background the penultimate wave is nonnegative. -/
theorem penultimateWave_nonneg (η : Site d → ℤ) (hη : ∀ y, 0 ≤ η y) (z x : Site d) :
    0 ≤ penultimateWave η z x := by
  unfold penultimateWave
  split
  · simp
  · exact wave_nonneg η hη _ z _ x

/-- The penultimate wave at its own centre is `M̂_η(z) - 1`. -/
theorem penultimateWave_at_centre (η : Site d → ℤ) (z : Site d)
    (hM : 1 ≤ waveThreshold η z) :
    penultimateWave η z z = (waveThreshold η z : ℤ) - 1 := by
  by_cases h : waveThreshold η z = 1
  · simp [penultimateWave, h]
  · simp only [penultimateWave, if_neg h, waveTerminal, wave_at_centre]
    push_cast [Nat.cast_sub hM]
    ring

/-- When the last-wave index exceeds one, the wave one below it stabilizes, by
the minimality in the definition of `M̂_η(z)`. -/
theorem penultimate_stabilizable (η : Site d → ℤ) (z : Site d)
    (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n z)
    (h1 : waveThreshold η z ≠ 1) :
    WaveStabilizable η (waveThreshold η z - 1) z := by
  have hne : {n : ℕ | 1 ≤ n ∧ ¬ WaveStabilizable η n z}.Nonempty := hlast
  have hmem : 1 ≤ waveThreshold η z ∧ ¬ WaveStabilizable η (waveThreshold η z) z :=
    Nat.sInf_mem hne
  have hM1 : 1 ≤ waveThreshold η z := hmem.1
  by_contra hcon
  have hm : waveThreshold η z - 1 ∈ {n : ℕ | 1 ≤ n ∧ ¬ WaveStabilizable η n z} :=
    ⟨by omega, hcon⟩
  have hle : waveThreshold η z ≤ waveThreshold η z - 1 := Nat.sInf_le hm
  omega

/-- Away from its centre the penultimate wave satisfies the wave equation.  When
`M̂_η(z) = 1` the wave is identically zero and the equation is the statement that
`0 ≤ η(x) < 2d`. -/
theorem penultimateWave_fixed (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (z : Site d) (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n z)
    {x : Site d} (hx : x ≠ z) :
    penultimateWave η z x = (nbrSumZ (penultimateWave η z) x + η x) / (2 * (d : ℤ)) := by
  by_cases h1 : waveThreshold η z = 1
  · have hp : penultimateWave η z = 0 := by simp [penultimateWave, h1]
    rw [hp]
    have h0 : nbrSumZ (0 : Site d → ℤ) x = 0 := by simp [nbrSumZ]
    rw [h0]
    have hlt : η x < 2 * (d : ℤ) := by linarith [hhigh x]
    have := Int.ediv_eq_zero_of_lt (hlow x) hlt
    simpa using this.symm
  · simp only [penultimateWave, if_neg h1]
    exact waveTerminal_fixed η (waveThreshold η z - 1) z
      (penultimate_stabilizable η z hlast h1) hx

/-- The penultimate wave vanishes off its own penultimate cluster. -/
theorem penultimateWave_eq_zero_of_not_mem (η : Site d → ℤ)
    (hlow : ∀ x, 0 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (z : Site d) (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n z)
    {x : Site d} (hx : x ∉ penultimateCluster η z) :
    penultimateWave η z x = 0 := by
  have hnn := penultimateWave_nonneg η hlow z x
  rcases eq_or_lt_of_le hnn with h | h
  · exact h.symm
  · exfalso
    have hne : x ≠ z := fun hxz => hx (hxz ▸ centre_mem_penultimateCluster η z)
    have hfix := penultimateWave_fixed η hlow hhigh z hlast hne
    have hSnn : 0 ≤ nbrSumZ (penultimateWave η z) x :=
      nbrSumZ_nonneg _ (penultimateWave_nonneg η hlow z) x
    rcases lt_or_ge (nbrSumZ (penultimateWave η z) x + η x) (2 * (d : ℤ)) with hc | hge
    · have hzero : (nbrSumZ (penultimateWave η z) x + η x) / (2 * (d : ℤ)) = 0 :=
        Int.ediv_eq_zero_of_lt (by linarith [hlow x]) hc
      rw [hzero] at hfix
      linarith
    · have hS : 0 < nbrSumZ (penultimateWave η z) x := by linarith [hhigh x]
      obtain ⟨y, hadj, hy⟩ :=
        exists_adj_pos_of_nbrSumZ_pos _ (penultimateWave_nonneg η hlow z) x hS
      exact hx (mem_penultimateCluster_of_adj η z x y hadj hy)

/-! ### The shape of an `ℕ∞`-valued arrival time -/

/-- An `ℕ∞`-infimum over a nonempty set of naturals is attained. -/
theorem sInf_coe_attained {P : ℕ → Prop} (h : ∃ n : ℕ, P n) :
    ∃ n : ℕ, P n ∧ sInf {t : ℕ∞ | ∃ m : ℕ, t = (m : ℕ∞) ∧ P m} = (n : ℕ∞) := by
  classical
  refine ⟨sInf {n | P n}, Nat.sInf_mem h, le_antisymm ?_ ?_⟩
  · exact sInf_le ⟨sInf {n | P n}, rfl, Nat.sInf_mem h⟩
  · refine le_sInf ?_
    rintro t ⟨m, rfl, hm⟩
    exact_mod_cast Nat.sInf_le hm

/-- An `ℕ∞`-infimum over an empty set of naturals is `⊤`. -/
theorem sInf_coe_top {P : ℕ → Prop} (h : ¬ ∃ n : ℕ, P n) :
    sInf {t : ℕ∞ | ∃ m : ℕ, t = (m : ℕ∞) ∧ P m} = ⊤ := by
  have hempty : {t : ℕ∞ | ∃ m : ℕ, t = (m : ℕ∞) ∧ P m} = ∅ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
    rintro m rfl hm
    exact h ⟨m, hm⟩
  rw [hempty, sInf_empty]

/-- A finite penultimate-cluster arrival time is attained at a natural number. -/
theorem clusterArrival_exists (η : Site d → ℤ) (y x : Site d)
    (h : clusterArrival η y x ≠ ⊤) :
    ∃ n : ℕ, 1 ≤ n ∧ (∀ w ∈ penultimateCluster η x, 0 < lastWave η y n w) ∧
      clusterArrival η y x = (n : ℕ∞) := by
  by_cases hex : ∃ n : ℕ, 1 ≤ n ∧ ∀ w ∈ penultimateCluster η x, 0 < lastWave η y n w
  · obtain ⟨n, hn, heq⟩ :=
      sInf_coe_attained (P := fun n : ℕ => 1 ≤ n ∧ ∀ w ∈ penultimateCluster η x,
        0 < lastWave η y n w) hex
    exact ⟨n, hn.1, hn.2, heq⟩
  · exact absurd (sInf_coe_top (P := fun n : ℕ => 1 ≤ n ∧ ∀ w ∈ penultimateCluster η x,
      0 < lastWave η y n w) hex) h

end Exploding
