/-
The step of the induction on the number of directions.  If near-cube boxes along `k - 1`
directions fail to be spanned with probability decaying faster than any polynomial in their size,
so do near-cube boxes along `k` directions.  The failure bound `g a` for one dimension less is the
supremum of the failure probabilities of the near-cube boxes of size `a`.  A seed size `ℓ` makes
the failure of the layers of a block at most one half, so that a block of size `Lb ≥ ℓ` is spanned
with probability at least `π = p ^ (ℓ ^ k) / 2`, and the grid of blocks of side
`Lb = ⌊√s⌋ + 1` gives the decay of the box.
-/
import Exploding.Support.ExtSchBlock
import Exploding.Support.ExtSchGrid
import Exploding.Support.ExtSchNum
import Exploding.Support.ExtSchOne

namespace Exploding

open LatticeProb MeasureTheory

variable {d : ℕ}

section Level
variable {p : ℝ}

/-- The supremum of the failure probabilities of the near-cube boxes of size `a` along `k`
directions. -/
noncomputable def xsr_gbound (d : ℕ) (p : ℝ) (k a : ℕ) : ℝ :=
  sSup {x | ∃ (J' : Finset (Fin d)) (lo hi : Site d), J'.card = k ∧ xsb_Near J' a lo hi ∧
    x = (xsch_mu d p).real {η | ¬ xsch_Sp J' (xsb_box lo hi) η}}

/-- The bound is nonnegative. -/
theorem xsr_gbound_nonneg (k a : ℕ) : 0 ≤ xsr_gbound d p k a :=
  Real.sSup_nonneg (by rintro x ⟨_, _, _, _, _, rfl⟩; exact measureReal_nonneg)

/-- The bound dominates the failure probability of every near-cube box of that size. -/
theorem xsr_gbound_ge [Fact (0 ≤ p ∧ p ≤ 1)] {k a : ℕ} {J' : Finset (Fin d)} {lo hi : Site d}
    (hJ' : J'.card = k) (hn : xsb_Near J' a lo hi) :
    (xsch_mu d p).real {η | ¬ xsch_Sp J' (xsb_box lo hi) η} ≤ xsr_gbound d p k a :=
  le_csSup ⟨1, by rintro x ⟨_, _, _, _, _, rfl⟩; exact measureReal_le_one⟩
    ⟨J', lo, hi, hJ', hn, rfl⟩

/-- The decay of the failure probabilities passes to the bound. -/
theorem xsr_gbound_decay [Fact (0 ≤ p ∧ p ≤ 1)] {k : ℕ} (hprev : xsb_Decay d p k) (Q : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : ℕ, 1 ≤ a → xsr_gbound d p k a ≤ c / (a : ℝ) ^ Q := by
  obtain ⟨c, hc, hcQ⟩ := hprev Q
  refine ⟨c, hc, fun a ha => ?_⟩
  have ha' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  refine Real.sSup_le ?_ (by positivity)
  rintro x ⟨J', lo, hi, hJ', hn, rfl⟩
  exact hcQ J' lo hi a hJ' ha hn

variable [Fact (0 ≤ p ∧ p ≤ 1)]

/-- **The step of the induction.** -/
theorem xsr_level_step (hp : 0 < p) {k : ℕ} (hk : 2 ≤ k) (hprev : xsb_Decay d p (k - 1)) :
    xsb_Decay d p k := by
  set g : ℕ → ℝ := xsr_gbound d p (k - 1) with hgdef
  have hg0 : ∀ a, 0 ≤ g a := fun a => xsr_gbound_nonneg _ _
  have hgdec := xsr_gbound_decay hprev
  obtain ⟨ℓ, hℓ, hsum⟩ := xsn_exists_seed_size k g hg0 hgdec
  have hp1 : p ≤ 1 := (Fact.out : 0 ≤ p ∧ p ≤ 1).2
  set π : ℝ := p ^ (ℓ ^ k) / 2 with hπ
  have hπ0 : 0 < π := by positivity
  have hπ1 : π < 1 := by
    have : p ^ (ℓ ^ k) ≤ 1 := pow_le_one₀ hp.le hp1
    rw [hπ]
    linarith
  intro Q
  obtain ⟨c', hc', hstep⟩ := xsn_decay_step k (by omega) π hπ0 hπ1 g hg0 hgdec Q
  refine ⟨max c' ((max (ℓ * ℓ) 2 : ℕ) ^ Q : ℝ), lt_max_of_lt_left hc',
    fun J lo hi s hJ hs hnear => ?_⟩
  have hs' : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hspos : (0 : ℝ) < (s : ℝ) ^ Q := by positivity
  by_cases hsmall : s < max (ℓ * ℓ) 2
  · calc (xsch_mu d p).real {η | ¬ xsch_Sp J (xsb_box lo hi) η} ≤ 1 := measureReal_le_one
      _ ≤ ((max (ℓ * ℓ) 2 : ℕ) : ℝ) ^ Q / (s : ℝ) ^ Q := by
          rw [le_div_iff₀ hspos, one_mul]
          exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hsmall.le) Q
      _ ≤ max c' ((max (ℓ * ℓ) 2 : ℕ) ^ Q : ℝ) / (s : ℝ) ^ Q :=
          div_le_div_of_nonneg_right (le_max_right _ _) hspos.le
  · have hS : max (ℓ * ℓ) 2 ≤ s := not_lt.mp hsmall
    have hℓs : ℓ * ℓ ≤ s := le_trans (le_max_left _ _) hS
    have h2s : 2 ≤ s := le_trans (le_max_right _ _) hS
    have hLbs : Nat.sqrt s + 1 ≤ s := Nat.sqrt_lt_self (by omega)
    have hℓLb : ℓ ≤ Nat.sqrt s + 1 := (Nat.le_sqrt.2 hℓs).trans (Nat.le_succ _)
    have hJne : J.Nonempty := Finset.card_pos.1 (by omega)
    have hd : 1 ≤ d := by
      obtain ⟨i, _⟩ := hJne
      exact Fin.pos i
    have hgJ : ∀ (J' : Finset (Fin d)) (lo hi : Site d) (a : ℕ), J'.card = J.card - 1 → 1 ≤ a →
        xsb_Near J' a lo hi →
          (xsch_mu d p).real {η | ¬ xsch_Sp J' (xsb_box lo hi) η} ≤ g a :=
      fun J' lo hi a hc _ hn => xsr_gbound_ge (by rw [hc, hJ]) hn
    have hblock : ∀ lo' hi' : Site d, (∀ i ∈ J, hi' i - lo' i + 1 = ((Nat.sqrt s + 1 : ℕ) : ℤ)) →
        (∀ i ∉ J, lo' i = hi' i) →
          π ≤ (xsch_mu d p).real {η | xsch_Sp J (xsb_box lo' hi') η} := by
      intro lo' hi' hside hthin
      obtain ⟨hi0, hhi0⟩ : ∃ hi0 : Site d,
          ∀ j, hi0 j = if j ∈ J then lo' j + (ℓ : ℤ) - 1 else lo' j := ⟨_, fun _ => rfl⟩
      have hℓz : (ℓ : ℤ) ≤ ((Nat.sqrt s + 1 : ℕ) : ℤ) := by exact_mod_cast hℓLb
      have hvalid : xss_Valid (⟨J, lo', hi', lo', hi0, ℓ⟩ : xss_Plan d) (Nat.sqrt s + 1) := by
        refine ⟨hJne, ⟨fun i hi => Or.inl (hside i hi), hthin⟩, ⟨fun i hi => Or.inl ?_,
          fun i hi => ?_⟩, fun j => ?_, hℓLb⟩
        · show hi0 i - lo' i + 1 = (ℓ : ℤ)
          rw [hhi0, if_pos hi]
          ring
        · show lo' i = hi0 i
          rw [hhi0, if_neg hi]
        · show lo' j ≤ lo' j ∧ hi0 j ≤ hi' j
          by_cases hj : j ∈ J
          · have h1 := hside j hj
            rw [hhi0, if_pos hj]
            exact ⟨le_rfl, by omega⟩
          · rw [hhi0, if_neg hj]
            exact ⟨le_rfl, (hthin j hj).le⟩
      have hseed : ∀ i ∈ (⟨J, lo', hi', lo', hi0, ℓ⟩ : xss_Plan d).J,
          (⟨J, lo', hi', lo', hi0, ℓ⟩ : xss_Plan d).hi0 i
            - (⟨J, lo', hi', lo', hi0, ℓ⟩ : xss_Plan d).lo0 i + 1 = (ℓ : ℤ) := by
        intro i hi
        show hi0 i - lo' i + 1 = (ℓ : ℤ)
        rw [hhi0, if_pos hi]
        ring
      have hb := xsr_block_good (p := p) (⟨J, lo', hi', lo', hi0, ℓ⟩ : xss_Plan d) hd hvalid hℓ
        hseed hg0 hgJ
      have hb' : p ^ (ℓ ^ J.card) * (1 - (J.card : ℝ) * ∑ a ∈ Finset.Icc ℓ (Nat.sqrt s + 1), g a)
          ≤ (xsch_mu d p).real {η | xsch_Sp J (xsb_box lo' hi') η} := hb
      rw [hJ] at hb'
      have h12 := hsum (Nat.sqrt s + 1)
      calc π = p ^ (ℓ ^ k) * (1 / 2) := by rw [hπ]; ring
        _ ≤ p ^ (ℓ ^ k) * (1 - (k : ℝ) * ∑ a ∈ Finset.Icc ℓ (Nat.sqrt s + 1), g a) :=
            mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hp.le _)
        _ ≤ _ := hb'
    have hgrid := xsr_fail_le_blocks (p := p) hJne (Nat.succ_pos _) hLbs hnear hblock hg0 hgJ
    rw [hJ] at hgrid
    calc (xsch_mu d p).real {η | ¬ xsch_Sp J (xsb_box lo hi) η}
        ≤ min 1 ((1 - π) ^ ((s / (Nat.sqrt s + 1)) ^ k) +
            (((s / (Nat.sqrt s + 1)) ^ k : ℕ) : ℝ) *
              ((k : ℝ) * ∑ a ∈ Finset.Icc (Nat.sqrt s + 1) s, g a)) :=
          le_min measureReal_le_one hgrid
      _ ≤ c' / (s : ℝ) ^ Q := hstep s hs
      _ ≤ max c' ((max (ℓ * ℓ) 2 : ℕ) ^ Q : ℝ) / (s : ℝ) ^ Q :=
          div_le_div_of_nonneg_right (le_max_left _ _) hspos.le

/-- **The induction on the number of directions.**  Near-cube boxes along any positive number
of directions fail to be spanned with probability decaying faster than any polynomial in their
size. -/
theorem xsr_decay_all (hp : 0 < p) {k : ℕ} (hk : 1 ≤ k) : xsb_Decay d p k := by
  induction k, hk using Nat.le_induction with
  | base => exact xs1_decay hp
  | succ n hn ih => exact xsr_level_step hp (by omega) (by simpa using ih)

end Level

end Exploding
