/-
The last open claim of `Exploding.Frozen.approximate_subadditive`.

## The double-toppling claim is false

The previous reduction (`ASProof6.lean`, `ASProof7.lean`) isolated the claim

  `hdouble : ∃ T, ∀ y, 0 < penultimateWave η 0 y → 2 ≤ podo (explodingPile η) T y`

in the case where no site topples infinitely often.  It is refuted for a deterministic
background, and with it the unrestricted `hpodo` that the frozen body carried for *every*
background `η`.

Take `d = 2` and the background `η = 3` on
`{(0,0), (0,1), (-1,-1)} ∪ {(k,0) : k ≥ 2}` and `η = 2` elsewhere, so `2d-2 ≤ η ≤ 2d-1`.

* The `1`-wave is `1` on `{(0,0),(0,1)}` and nowhere else: a site with `η = 2` needs two
  lit neighbours and a site with `η = 3` one, and no other site has them.  It stabilizes.
  The `2`-wave is `2` at the origin and `1` on the half strip `{x ≥ -1, |y| ≤ 1}`, so it
  does not stabilize.  Hence `waveThreshold η 0 = 2`, `penultimateWave η 0` is `1` on
  `{(0,0),(0,1)}`, and the penultimate cluster is finite.
* The piles `η + nδ₀`, `n ≤ 3`, have finite avalanches (the origin and `(0,1)` topple
  once), and `η + 4δ₀` has an avalanche along the strip, so `explosionThreshold η = 4`
  and `explodingPile η` is not stabilizable.
* Let `v = 1` on the half strip and `v (0,0) = 2`.  Then `explodingPile η + Δv ≤ 3` at
  every site (checked by hand: the origin ends with `3`, the strip sites with at most `3`,
  every site next to the strip sees one toppling neighbour and holds `2 + 1`), so by the
  least action principle `podo (explodingPile η) t ≤ v` for all `t`.  No site topples
  infinitely often, but `podo (explodingPile η) t (0,1) ≤ 1 < 2` for all `t` although
  `penultimateWave η 0 (0,1) = 1`.  Moreover `(0,2)` lies in the penultimate cluster and
  never topples, so the weaker `∃ t0, ∀ x ∈ penultimateCluster η 0, 1 ≤ podo _ t0 x` fails
  too.  (An exact simulation of the definitions on an `81 × 81` window agrees:
  threshold `4`, `1`-wave `{(0,0),(0,1)}`, odometer `v`.)

The frozen theorem is almost sure, and the extra input is Lemma 3.6: almost surely the
last wave reaches every site.  In the example the last wave stays on the strip.

## What is proved here

`asd_hpodo_of_reach`: for `2d-2 ≤ η ≤ 2d-1`, not robust, with a finite penultimate
cluster, if the last wave reaches every site then the exploding pile topples the whole
penultimate cluster at a common time.  If some site topples infinitely often this is
`as7_hpodo_of_infTopple`.  Otherwise every odometer is bounded; the limit odometer `V`
is stable and finite, dominates the `N`-wave with `N = V 0`
(`glw_wave_to_explosive_dom`), the `N`-wave dominates the last wave since `M̂ ≤ N`
(an `N`-wave with `N < M̂` is stabilizable, so would confine the topplings to a
finite set), and so `V` is positive wherever the last wave is.

`asd_reach_ae`: almost surely the last wave reaches every site (Lemma 3.6).
`asd_approximate_subadditive`: the almost sure assembly with the corrected `hpodo`.
-/
import Exploding.Support.ASProof
import Exploding.Support.ASProof2
import Exploding.Support.ASProof3
import Exploding.Support.ASProof4
import Exploding.Support.ASProof5
import Exploding.Support.ASProof7
import Exploding.Support.ASSpecial
import Exploding.Support.GLWProofAux
import Exploding.Support.PUBProofF
import Exploding.External.LiggettSchonmannStaceyBoundedDegree
import Exploding.External.MathieuHoles
import Exploding.External.AntalPisztora

open Exploding LatticeProb MeasureTheory

/-- A pile with nonnegative initial values never has a negative site: a site only
loses `2d` chips when it holds at least `2d`. -/
theorem asd_pconf_nonneg {d : ℕ} (σ : Site d → ℤ) (hσ : ∀ x, 0 ≤ σ x) :
    ∀ t : ℕ, ∀ x : Site d, 0 ≤ pconf σ t x := by
  intro t
  induction t with
  | zero =>
    intro x
    have h0 : lap (podo σ 0) x = 0 := by
      simp [lap, nbrSumZ, podo_zero]
    simp only [pconf, h0, add_zero]
    exact hσ x
  | succ t ih =>
    intro x
    have hmono : nbrSumZ (podo σ t) x ≤ nbrSumZ (podo σ (t + 1)) x :=
      nbrSumZ_mono (fun y => podo_mono_step σ t y) x
    have hstep := podo_succ σ t x
    by_cases hc : 2 * (d : ℤ) ≤ pconf σ t x
    · rw [if_pos hc] at hstep
      simp only [pconf, lap] at hc ⊢
      rw [hstep]
      nlinarith
    · rw [if_neg hc, add_zero] at hstep
      have := ih x
      simp only [pconf, lap] at this ⊢
      rw [hstep]
      linarith

/-- Off the origin, the parallel odometer of `explodingPile η` is bounded by the wave:
`v_t ≤ u_t^{(N)}` whenever the origin never topples more than `N` times. -/
theorem asd_podo_le_wave {d : ℕ} (hd : 1 ≤ d) (η : Site d → ℤ) (hnn : ∀ x, 0 ≤ η x) (N : ℕ)
    (hN : ∀ t, podo (explodingPile η) t (0 : Site d) ≤ (N : ℤ)) :
    ∀ t : ℕ, ∀ x : Site d, podo (explodingPile η) t x ≤ wave η N (0 : Site d) t x := by
  have hdz : (0 : ℤ) < 2 * (d : ℤ) := by exact_mod_cast (by omega : 0 < 2 * d)
  have hσ : ∀ x, 0 ≤ explodingPile η x := by
    intro x
    simp only [explodingPile]
    have h1 : 0 ≤ (explosionThreshold η : ℤ) * dirac (0 : Site d) x := by
      have h2 : 0 ≤ dirac (0 : Site d) x := by unfold dirac; split_ifs <;> norm_num
      positivity
    linarith [hnn x]
  intro t
  induction t with
  | zero =>
    intro x
    by_cases h : x = (0 : Site d)
    · subst h; simp
    · simp [wave_zero, h]
  | succ t ih =>
    intro x
    by_cases h : x = (0 : Site d)
    · subst h
      rw [wave_at_centre]
      exact hN (t + 1)
    · rw [wave_of_ne _ _ _ _ _ h]
      have hσx : explodingPile η x = η x := by
        simp only [explodingPile]
        rw [dirac_of_ne h, mul_zero, add_zero]
      have h1 : nbrSumZ (podo (explodingPile η) t) x ≤ nbrSumZ (wave η N (0 : Site d) t) x :=
        nbrSumZ_mono ih x
      have hstep := podo_succ (explodingPile η) t x
      have hpn := asd_pconf_nonneg (explodingPile η) hσ t x
      refine le_trans ?_ (Int.ediv_le_ediv hdz (by linarith : nbrSumZ (podo (explodingPile η) t) x + η x
        ≤ nbrSumZ (wave η N (0 : Site d) t) x + η x))
      rw [Int.le_ediv_iff_mul_le hdz]
      by_cases hc : 2 * (d : ℤ) ≤ pconf (explodingPile η) t x
      · rw [if_pos hc] at hstep
        rw [hstep]
        simp only [pconf, lap, hσx] at hc
        nlinarith
      · rw [if_neg hc, add_zero] at hstep
        rw [hstep]
        simp only [pconf, lap, hσx] at hpn
        nlinarith

/-- The `n`-wave on a background with `0 ≤ η ≤ 2d - 1` is supported in the ball of radius
`t` at time `t`. -/
theorem asd_wave_support {d : ℕ} (η : Site d → ℤ) (hnn : ∀ x, 0 ≤ η x)
    (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1) (n : ℕ) :
    ∀ t : ℕ, ∀ x : Site d, 0 < wave η n (0 : Site d) t x → mnorm x ≤ (t : ℤ) := by
  intro t
  induction t with
  | zero =>
    intro x hx
    by_cases h : x = (0 : Site d)
    · subst h; simp [mnorm]
    · simp [wave_zero, h] at hx
  | succ t ih =>
    intro x hx
    by_cases h : x = (0 : Site d)
    · subst h
      have : mnorm (0 : Site d) = 0 := by simp [mnorm]
      rw [this]; positivity
    · rw [wave_of_ne _ _ _ _ _ h] at hx
      have hwn : ∀ y, 0 ≤ wave η n (0 : Site d) t y := fun y => wave_nonneg η hnn n 0 t y
      have hpos : 0 < nbrSumZ (wave η n (0 : Site d) t) x := by
        by_contra hcon
        have hnb0 : 0 ≤ nbrSumZ (wave η n (0 : Site d) t) x :=
          Finset.sum_nonneg fun _ _ => add_nonneg (hwn _) (hwn _)
        have hz : nbrSumZ (wave η n (0 : Site d) t) x = 0 := by omega
        rw [hz, zero_add] at hx
        have hxd : η x / (2 * (d : ℤ)) = 0 := by
          apply Int.ediv_eq_zero_of_lt (hnn x)
          linarith [hhigh x]
        rw [hxd] at hx
        exact lt_irrefl 0 hx
      obtain ⟨y, hyx, hypos⟩ := exists_adj_pos_of_nbrSumZ_pos _ hwn x hpos
      have hmy : mnorm y ≤ (t : ℤ) := ih y hypos
      have hdist : mnorm x ≤ mnorm y + 1 := by
        have h1 := pub_mnorm_sub_le x y (0 : Site d)
        have h2 := pub_adj_mnorm hyx
        simp only [sub_zero] at h1
        rw [h2] at h1
        linarith
      push_cast
      linarith

/-- The terminal odometer of a pile all of whose odometers are bounded: a stable finite
function that eventually equals the odometer at every site. -/
theorem asd_limit_odometer {d : ℕ} (σ : Site d → ℤ)
    (hbdd : ∀ x : Site d, ∃ B : ℤ, ∀ t : ℕ, podo σ t x ≤ B) :
    ∃ (V : Site d → ℤ) (T : Site d → ℕ),
      (∀ x t, T x ≤ t → podo σ t x = V x) ∧ (∀ x t, podo σ t x ≤ V x) ∧
      (∀ x, σ x + lap V x ≤ 2 * (d : ℤ) - 1) := by
  classical
  have hstab : ∀ x : Site d, ∃ T : ℕ, ∀ t : ℕ, T ≤ t → podo σ t x = podo σ T x := fun x =>
    as4_mono_bdd_eventually_constant (fun t => podo σ t x)
      (fun s t hst => as_podo_mono σ hst x) (hbdd x)
  choose T hT using hstab
  have hVeq : ∀ x t, T x ≤ t → podo σ t x = podo σ (T x) x := fun x t ht => hT x t ht
  have hVle : ∀ x t, podo σ t x ≤ podo σ (T x) x := by
    intro x t
    rcases le_total t (T x) with h | h
    · exact as_podo_mono σ h x
    · exact le_of_eq (hVeq x t h)
  refine ⟨fun x => podo σ (T x) x, T, hVeq, hVle, ?_⟩
  intro x
  set τ : ℕ := max (T x) (Finset.univ.sup (fun i : Fin d => max (T (x + unit i)) (T (x - unit i))))
    with hτ
  have hτx : T x ≤ τ := le_max_left _ _
  have hτn : ∀ i : Fin d, T (x + unit i) ≤ τ ∧ T (x - unit i) ≤ τ := by
    intro i
    have h1 : max (T (x + unit i)) (T (x - unit i)) ≤
        Finset.univ.sup (fun i : Fin d => max (T (x + unit i)) (T (x - unit i))) :=
      Finset.le_sup (f := fun i : Fin d => max (T (x + unit i)) (T (x - unit i)))
        (Finset.mem_univ i)
    exact ⟨le_trans (le_max_left _ _) (le_trans h1 (le_max_right _ _)),
      le_trans (le_max_right _ _) (le_trans h1 (le_max_right _ _))⟩
  have hnb : nbrSumZ (podo σ τ) x = nbrSumZ (fun y => podo σ (T y) y) x := by
    unfold nbrSumZ
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hVeq _ τ (hτn i).1, hVeq _ τ (hτn i).2]
  have h1 : podo σ (τ + 1) x = podo σ τ x := by
    rw [hVeq x (τ + 1) (by omega), hVeq x τ hτx]
  rw [podo_succ] at h1
  have h3 : ¬ (2 * (d : ℤ) ≤ pconf σ τ x) := by
    intro hle
    rw [if_pos hle] at h1
    omega
  simp only [pconf, lap] at h3
  have hxτ : podo σ τ x = podo σ (T x) x := hVeq x τ hτx
  rw [hnb, hxτ] at h3
  simp only [lap]
  omega

/-- **`hpodo` when the last wave reaches every site.**  If `2d - 2 ≤ η ≤ 2d - 1`, the
pile `explodingPile η` is not stabilizable, the penultimate cluster is finite and the
last wave is eventually positive at every site, then the pile topples the whole
penultimate cluster at one common time. -/
theorem asd_hpodo_of_reach {d : ℕ} (hd : 2 ≤ d) (η : Site d → ℤ)
    (hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x) (hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1)
    (hnr : ¬ Robust η)
    (hlast : ∃ n : ℕ, 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d))
    (hfin : (penultimateCluster η (0 : Site d)).Finite)
    (hall : ∀ x : Site d, ∃ m : ℕ, 0 < lastWave η (0 : Site d) m x) :
    ∃ t0 : ℕ, ∀ x ∈ penultimateCluster η (0 : Site d),
      1 ≤ podo (explodingPile η) t0 x := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hdz : (0 : ℤ) < 2 * (d : ℤ) := by exact_mod_cast (by omega : 0 < 2 * d)
  have hnn : ∀ x, 0 ≤ η x := fun x => by linarith [hlow x]
  by_cases hinf : ∃ x : Site d, as2_InfTopple (explodingPile η) x
  · exact as7_hpodo_of_infTopple hd1 η hfin hinf
  · -- every odometer is bounded
    have hbdd : ∀ x : Site d, ∃ B : ℤ, ∀ t : ℕ, podo (explodingPile η) t x ≤ B := by
      intro x
      by_contra hx
      apply hinf
      refine ⟨x, fun N => ?_⟩
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      exact hx ⟨(N : ℤ), hcon⟩
    obtain ⟨V, T, hVeq, hVle, hVstab⟩ := asd_limit_odometer (explodingPile η) hbdd
    have hVnn : ∀ x, 0 ≤ V x := fun x => by
      have := as_podo_nonneg (explodingPile η) (T x) x
      rw [hVeq x (T x) le_rfl] at this
      exact this
    have hσoff : ∀ x : Site d, x ≠ (0 : Site d) → explodingPile η x = η x := by
      intro x hx
      simp only [explodingPile]
      rw [dirac_of_ne hx, mul_zero, add_zero]
    have hstable : ∀ x : Site d, x ≠ (0 : Site d) → η x + lap V x ≤ 2 * (d : ℤ) - 1 := by
      intro x hx
      have := hVstab x
      rwa [hσoff x hx] at this
    -- the origin topples, and `N := V 0`
    obtain ⟨s, hs⟩ := as5_origin_topples_of_not_stabilizable hd1 (explodingPile η)
      (fun x hx => by rw [hσoff x hx]; exact hhigh x)
      (as_explosionThreshold_spec η hnr).2
    have hV0pos : 1 ≤ V (0 : Site d) := by
      have h1 := hVle (0 : Site d) s
      omega
    set N : ℕ := (V (0 : Site d)).toNat with hNdef
    have hNcast : (N : ℤ) = V (0 : Site d) := Int.toNat_of_nonneg (hVnn _)
    have hN1 : 1 ≤ N := by omega
    have hNbd : ∀ t, podo (explodingPile η) t (0 : Site d) ≤ (N : ℤ) := by
      intro t; rw [hNcast]; exact hVle _ t
    have hB := asd_podo_le_wave hd1 η hnn N hNbd
    have hdom : ∀ t x, wave η N (0 : Site d) t x ≤ V x :=
      glw_wave_to_explosive_dom η N V hVnn (le_of_eq hNcast) hstable
    -- the threshold of the last wave is at most `N`
    have hmem := Nat.sInf_mem hlast
    have hMN : waveThreshold η (0 : Site d) ≤ N := by
      by_contra hlt
      push Not at hlt
      have hnotmem : N ∉ {n : ℕ | 1 ≤ n ∧ ¬ WaveStabilizable η n (0 : Site d)} :=
        Nat.notMem_of_lt_sInf hlt
      have hws : WaveStabilizable η N (0 : Site d) := by
        by_contra hnws
        exact hnotmem ⟨hN1, hnws⟩
      obtain ⟨T0, hT0⟩ := hws
      have hsubset : {x : Site d | ∃ t : ℕ, 0 < podo (explodingPile η) t x} ⊆
          {x : Site d | mnorm x ≤ (T0 : ℤ)} := by
        rintro x ⟨t, ht⟩
        have hw : 0 < wave η N (0 : Site d) t x := lt_of_lt_of_le ht (hB t x)
        show mnorm x ≤ (T0 : ℤ)
        rcases le_total t T0 with h | h
        · have := asd_wave_support η hnn hhigh N t x hw
          have h' : (t : ℤ) ≤ (T0 : ℤ) := by exact_mod_cast h
          linarith
        · rw [hT0 t h] at hw
          exact le_trans (asd_wave_support η hnn hhigh N T0 x hw) le_rfl
      have hfinset : {x : Site d | mnorm x ≤ (T0 : ℤ)}.Finite := by
        refine as_coord_bdd_finite (0 : Site d) (T0 : ℝ) _ ?_
        intro y hy i
        have h1 := abs_coord_le_mnorm y i
        have h2 : |y i - (0 : Site d) i| ≤ (T0 : ℤ) := by
          simp only [Pi.zero_apply, sub_zero]
          exact le_trans h1 hy
        exact_mod_cast h2
      exact (as_explosionThreshold_spec η hnr).2
        (as2_finite_toppling_set_stabilizable hd1 (explodingPile η) (hfinset.subset hsubset))
    -- every site topples at a finite time
    have hpos : ∀ x : Site d, 1 ≤ podo (explodingPile η) (T x) x := by
      intro x
      obtain ⟨m, hm⟩ := hall x
      have h1 : wave η (waveThreshold η (0 : Site d)) (0 : Site d) m x ≤
          wave η N (0 : Site d) m x := wave_mono_n η hdz (0 : Site d) hMN m x
      have h2 : 0 < V x := by
        have h3 : 0 < wave η (waveThreshold η (0 : Site d)) (0 : Site d) m x := hm
        exact lt_of_lt_of_le h3 (le_trans h1 (hdom m x))
      rw [hVeq x (T x) le_rfl]
      omega
    refine ⟨hfin.toFinset.sup T, fun x hx => ?_⟩
    have hxT : T x ≤ hfin.toFinset.sup T := Finset.le_sup (f := T) (hfin.mem_toFinset.mpr hx)
    exact le_trans (hpos x) (as_podo_mono (explodingPile η) hxT x)

/-- **Lemma 3.6, reach form.**  Almost surely the last wave reaches every site: the
linear arrival bound of Lemma 3.6 makes `lastArrival η 0 x` a natural number, so the
last wave is positive at `x` at some time. -/
theorem asd_reach_ae (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∀ᵐ η ∂(toyLaw d p), ∀ x : Site d, ∃ m : ℕ, 0 < lastWave η (0 : Site d) m x := by
  obtain ⟨γ, C, _hγ, _hC, hae⟩ :=
    pub_penultimate_upper_bound d hd p hp hp1 hLSSB hHole hChem
  filter_upwards [hae] with η hreach x
  obtain ⟨n0, hn0⟩ := hreach
  have hxnn : 0 ≤ mnorm x := pub_mnorm_nonneg x
  have hxle : mnorm x ≤ ((max n0 (mnorm x).toNat : ℕ) : ℤ) := by
    have h1 : mnorm x ≤ (((mnorm x).toNat : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hxnn]
    have h2 : (((mnorm x).toNat : ℕ) : ℤ) ≤ ((max n0 (mnorm x).toNat : ℕ) : ℤ) := by
      exact_mod_cast le_max_right n0 (mnorm x).toNat
    linarith
  obtain ⟨m, hm, _⟩ := hn0 (max n0 (mnorm x).toNat) (le_max_left _ _) x hxle
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  have htop : lastArrival η (0 : Site d) x = ⊤ := by
    unfold lastArrival
    exact sInf_coe_top (by rintro ⟨m', hm'⟩; have := hcon m'; have := hm'.2; omega)
  rw [htop] at hm
  exact (by simp : (m : ℕ∞) ≠ ⊤) hm.symm

/-- **Proposition 4.1, the almost sure assembly with the corrected `hpodo`.**  The
unrestricted `hpodo` of `as3_approximate_subadditive_of_gaps` is false for deterministic
backgrounds (see the header); here it is supplied by `asd_hpodo_of_reach` on the almost
sure event on which the last wave reaches every site. -/
theorem asd_approximate_subadditive
    (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hLSSB : Exploding.External.LiggettSchonmannStaceyBoundedDegree)
    (hHole : Exploding.External.MathieuHoleVolume)
    (hChem : Exploding.External.AntalPisztoraChemicalDistance) :
    ∀ᵐ η ∂(toyLaw d p), ∃ C1 C2 : ℕ, ∀ x : Site d,
      arrival η x ≤ lastArrival η (0 : Site d) x + (C1 : ℕ∞) ∧
        lastArrival η (0 : Site d) x ≤ arrival η x + (C2 : ℕ∞) := by
  filter_upwards [as_eta_bounds d hd p hp hp1,
    Exploding.Frozen.finite_exploding d hd p hp hp1 hLSSB hHole hChem,
    as_penultimateCluster_finite d hd p hp hp1 hLSSB hHole hChem,
    as3_hlastreach d hd p hp hp1 hLSSB hHole hChem,
    asd_reach_ae d hd p hp hp1 hLSSB hHole hChem] with η hbounds hlast hPfin hlastreach hreach
  have hlow : ∀ x, 2 * (d : ℤ) - 2 ≤ η x := fun x => (hbounds x).1
  have hhigh : ∀ x, η x ≤ 2 * (d : ℤ) - 1 := fun x => (hbounds x).2
  have hnotrobust : ¬ Robust η := by
    intro hrob
    obtain ⟨n, hn1, hnstab⟩ := hlast
    exact hnstab (as4_hrobust d hd η hlow hhigh hrob n hn1)
  have hexp1 : 1 ≤ explosionThreshold η := (as_explosionThreshold_spec η hnotrobust).1
  obtain ⟨C1, hC1⟩ := as_ineq1 hd η hlow hhigh hlast
    (asd_hpodo_of_reach hd η hlow hhigh hnotrobust hlast hPfin hreach)
  obtain ⟨C2, hC2⟩ := as_ineq2 hd η hlow hhigh hlast hexp1
    hlastreach (as3_tildeP_finite η hhigh) (assp_special d hd η hlow hhigh)
  exact ⟨C1, C2, fun x => ⟨hC1 x, hC2 x⟩⟩
