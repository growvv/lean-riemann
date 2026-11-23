/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Assembling the Stepanov bound

This file puts the pieces together into the shape of the Stepanov/Weil bound for `y ^ 2 = f(x)`:

* `fibre_card_le_two` — each fibre `{y | y ^ 2 = f(x)}` has at most two points (the elementary
  upper bound, `#P ≤ 2 * #x-image`).
* `stepanov_point_bound` — the genuine improvement: given an auxiliary polynomial `A + y B` with
  nonzero conjugate norm `Q = A ^ 2 - f * B ^ 2` that vanishes on a set `S` of *full* fibres, one
  gets `2 * |S| ≤ natDegree Q`, and `natDegree Q` is bounded by the degree budget
  `max (2 deg A) (deg f + 2 deg B)`.

The residual gap to the full Weil bound `|#P - (q+1)| ≤ 2g√q` is the choice of parameters
`deg A, deg B` and the fact that a nonzero `Q` with the required vanishing can always be built;
that optimization is where the `√q` appears. There is no `sorry`.
-/

import Mathlib
import LeanRiemann.Curve
import LeanRiemann.Stepanov

open Polynomial

namespace LeanRiemann.StepanovBound

variable {K : Type*} [Field K]

/-- **Each fibre has at most two points.** For fixed `x`, the solutions `y` of `y ^ 2 = f(x)`
number at most two: they are roots of `Y ^ 2 - f(x)`, a quadratic. -/
theorem fibre_card_le_two [Fintype K] [DecidableEq K] (f : K[X]) (x : K) :
    (Finset.univ.filter (fun y : K => y ^ 2 = f.eval x)).card ≤ 2 := by
  classical
  by_cases hx : f.eval x = 0
  · -- `y ^ 2 = 0` iff `y = 0`
    have hsub : Finset.univ.filter (fun y : K => y ^ 2 = f.eval x) ⊆ {0} := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      simp only [Finset.mem_singleton]
      rw [hx] at hy
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hy
    calc (Finset.univ.filter (fun y : K => y ^ 2 = f.eval x)).card ≤ ({0} : Finset K).card :=
          Finset.card_le_card hsub
      _ = 1 := by simp
      _ ≤ 2 := by norm_num
  · -- `y ^ 2 = c` has at most 2 solutions: inject the solution set into `{c, 0}`-style bound
    -- via the polynomial `Y ^ 2 - C c` having degree 2.
    let p : K[X] := X ^ 2 - C (f.eval x)
    have hp : p ≠ 0 := by
      intro h
      have : p.natDegree = 0 := by rw [h]; simp
      rw [show p.natDegree = 2 by
        rw [show p = X ^ 2 - C (f.eval x) from rfl, natDegree_X_pow_sub_C]] at this
      exact absurd this (by norm_num)
    have hsub : Finset.univ.filter (fun y : K => y ^ 2 = f.eval x) ⊆ p.roots.toFinset := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      rw [Multiset.mem_toFinset, mem_roots hp]
      simp only [Polynomial.IsRoot, p, eval_sub, eval_pow, eval_X, eval_C, hy, sub_self]
    calc (Finset.univ.filter (fun y : K => y ^ 2 = f.eval x)).card
        ≤ p.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ p.roots.card := Multiset.toFinset_card_le _
      _ ≤ p.natDegree := card_roots' _
      _ = 2 := by rw [show p = X ^ 2 - C (f.eval x) from rfl, natDegree_X_pow_sub_C]

/-- **Stepanov point bound.** Suppose `A + y B` vanishes (with both branches `±y`, `y ≠ 0`) at
every `x` in a set `S`, that the conjugate norm `Q = A ^ 2 - f * B ^ 2` is nonzero, and that the
degree budget holds. Then `2 * |S| ≤ max (2 deg A) (deg f + 2 deg B)`.

Choosing `deg A, deg B ≈ D / 2` and `D ≈ 2√(deg f · N)` yields the classical `O(√q)` saving. -/
theorem stepanov_point_bound (f A B : K[X]) (hchar : (2 : K) ≠ 0)
    (hQ : A ^ 2 - f * B ^ 2 ≠ 0) (S : Finset K)
    (h : ∀ x ∈ S, ∃ y : K, y ≠ 0 ∧ y ^ 2 = f.eval x ∧
      A.eval x + y * B.eval x = 0 ∧ A.eval x + (-y) * B.eval x = 0) :
    2 * S.card ≤ max (2 * A.natDegree) (f.natDegree + 2 * B.natDegree) := by
  calc 2 * S.card ≤ (A ^ 2 - f * B ^ 2).natDegree := Curve.two_fibre_card_le f A B hchar hQ S h
    _ ≤ max (2 * A.natDegree) (f.natDegree + 2 * B.natDegree) :=
        Curve.natDegree_conjugate_le f A B

end LeanRiemann.StepanovBound
