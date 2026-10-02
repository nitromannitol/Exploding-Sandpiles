/-
The growth schedule of a box inside a larger box.

A plan grows a starting box `lo0 .. hi0` of side `L` inside a target box `LO .. HI` along the
directions of `J`, one layer at a time.  Time is divided into rounds of `|J|` steps.  In round `r`
the directions of `J` are visited in increasing order, and the visited direction is brought to
side `L + r + 1` unless it has reached the side of the target.  Hence at every time all sides of
the box along `J` are `L + r` or `L + r + 1` for the current round `r`, or the sides of the
target; so every layer added is a near-cube of the lower dimension, with `L + r` as its size.
A direction is grown upward until it reaches the target and downward afterwards.

Everything is given in closed form, as a function of the time, so that the layers do not depend
on the background.
-/
import Exploding.Support.ExtSchBox

namespace Exploding

open LatticeProb

variable {d : ℕ}

/-- The data of a growth: the directions `J`, the target box `LO .. HI`, the starting box
`lo0 .. hi0`, and the size `L` of the starting box. -/
structure xss_Plan (d : ℕ) where
  J : Finset (Fin d)
  LO : Site d
  HI : Site d
  lo0 : Site d
  hi0 : Site d
  L : ℕ

/-- The plan is valid for a target of size `s`: the starting box is a near-cube of size `L`
inside the target, which is a near-cube of size `s ≥ L`, along a nonempty set of directions. -/
def xss_Valid (P : xss_Plan d) (s : ℕ) : Prop :=
  P.J.Nonempty ∧ xsb_Near P.J s P.LO P.HI ∧ xsb_Near P.J P.L P.lo0 P.hi0 ∧
    (∀ j, P.LO j ≤ P.lo0 j ∧ P.hi0 j ≤ P.HI j) ∧ P.L ≤ s

/-- The side length of the interval from `lo j` to `hi j`. -/
def xss_len (lo hi : Site d) (j : Fin d) : ℤ := hi j - lo j + 1

/-- The position of `j` among the directions of `J`, counted in increasing order from `0`. -/
def xss_pos (J : Finset (Fin d)) (j : Fin d) : ℕ := (J.filter (· < j)).card

/-- The side of the box in direction `j` after `t` steps. -/
def xss_side (P : xss_Plan d) (t : ℕ) (j : Fin d) : ℤ :=
  if j ∈ P.J then
    min (xss_len P.LO P.HI j) (max (xss_len P.lo0 P.hi0 j)
      ((P.L : ℤ) + ((t / P.J.card : ℕ) : ℤ) +
        (if xss_pos P.J j < t % P.J.card then 1 else 0)))
  else xss_len P.lo0 P.hi0 j

/-- The number of layers added in direction `j` during the first `t` steps. -/
def xss_grown (P : xss_Plan d) (t : ℕ) (j : Fin d) : ℤ :=
  xss_side P t j - xss_len P.lo0 P.hi0 j

/-- The upper corner after `t` steps: a direction grows upward until the target. -/
def xss_hi (P : xss_Plan d) (t : ℕ) (j : Fin d) : ℤ :=
  P.hi0 j + min (xss_grown P t j) (P.HI j - P.hi0 j)

/-- The lower corner after `t` steps: the growth beyond the upper wall goes downward. -/
def xss_lo (P : xss_Plan d) (t : ℕ) (j : Fin d) : ℤ :=
  P.lo0 j - (xss_grown P t j - min (xss_grown P t j) (P.HI j - P.hi0 j))

/-- The box after `t` steps. -/
def xss_box (P : xss_Plan d) (t : ℕ) : Set (Site d) :=
  xsb_box (fun j => xss_lo P t j) (fun j => xss_hi P t j)

/-- The layer added at step `t`: empty when the visited direction does not grow. -/
def xss_layer (P : xss_Plan d) (t : ℕ) : Set (Site d) := xss_box P (t + 1) \ xss_box P t

/-- The direction visited at step `t`: the direction of `J` at position `t mod |J|`. -/
noncomputable def xss_dir (P : xss_Plan d) (hJ : P.J.Nonempty) (t : ℕ) : Fin d :=
  if h : ∃ j ∈ P.J, xss_pos P.J j = t % P.J.card then h.choose else Classical.choose hJ

/-- The number of steps of the plan up to a target of size `s`. -/
def xss_steps (P : xss_Plan d) (s : ℕ) : ℕ := (s - P.L + 1) * P.J.card

end Exploding
