/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Folding the function space: the Frobenius mechanism

Stepanov's method lives over a finite field `𝔽_q` because there the polynomial `X ^ q - X`
*vanishes at every point*: `a ^ q = a` for all `a`. Consequently, reducing any polynomial `p`
modulo `X ^ q - X` yields a polynomial `p %ₘ (X ^ q - X)` of degree `< q` that takes *exactly the
same values* as `p` everywhere on `𝔽_q`. This is the precise sense in which "Frobenius folds the
function space": arbitrarily high degree is collapsed to `< q` without changing any evaluation,
which is what lets the multiplicity bookkeeping (degree budget `k * |S|`) win.

Over `ℚ` no nonzero polynomial vanishes at every rational point (`rat_no_folding_polynomial`),
so there is no such folding and the degree budget cannot be reset. This file makes both halves
precise. There is no `sorry`.
-/

import Mathlib
import LeanRiemann.Stepanov

open Polynomial

namespace LeanRiemann.Folding

/-- **`X ^ q - X` vanishes everywhere on a finite field.** For `q = #K`, `a ^ q - a = 0` for all
`a : K`. This is the folding polynomial of the function-field method. -/
theorem X_pow_card_sub_X_isRoot {K : Type*} [Field K] [Fintype K] (a : K) :
    (X ^ Fintype.card K - X : K[X]).IsRoot a := by
  simp only [IsRoot, eval_sub, eval_pow, eval_X, Stepanov.frobenius_fixed, sub_self]

/-- The folding polynomial `X ^ q - X` is monic over a finite field. -/
theorem monic_X_pow_card_sub_X {K : Type*} [Field K] [Fintype K] :
    (X ^ Fintype.card K - X : K[X]).Monic := by
  apply monic_X_pow_sub
  rw [degree_X]
  exact_mod_cast Fintype.one_lt_card

/-- **Reduction modulo the folding polynomial preserves values.** For every `a : K`,
`(p %ₘ (X ^ q - X)).eval a = p.eval a`. So the reduced polynomial of degree `< q` carries the
same data as `p` on all of `K` — Frobenius has folded the high-degree part away. -/
theorem eval_modByMonic_X_pow_card_sub_X {K : Type*} [Field K] [Fintype K]
    (p : K[X]) (a : K) :
    (p %ₘ (X ^ Fintype.card K - X)).eval a = p.eval a := by
  -- `p = (p %ₘ f) + f * (p /ₘ f)`, and `f` vanishes at `a`, so evaluating gives the result.
  have hdiv := modByMonic_add_div p (X ^ Fintype.card K - X)
  have heval := congrArg (Polynomial.eval a) hdiv
  rw [eval_add, eval_mul, X_pow_card_sub_X_isRoot a, zero_mul, add_zero] at heval
  exact heval

/-- The reduced polynomial has degree `< q`. This is the "reset the degree budget" step. -/
theorem degree_modByMonic_lt_card {K : Type*} [Field K] [Fintype K] (p : K[X]) :
    (p %ₘ (X ^ Fintype.card K - X)).degree < (Fintype.card K : WithBot ℕ) := by
  have h := degree_modByMonic_lt p monic_X_pow_card_sub_X
  have hdeg : (X ^ Fintype.card K - X : K[X]).degree = (Fintype.card K : WithBot ℕ) := by
    rw [degree_eq_natDegree monic_X_pow_card_sub_X.ne_zero,
      natDegree_X_pow_sub_X Fintype.one_lt_card]
  rwa [hdeg] at h

/-- **No folding polynomial over `ℚ`.** There is no nonzero polynomial over `ℚ` that vanishes at
every rational point. This is why the degree budget cannot be reset over the integers, and hence
why the Stepanov/Frobenius folding step has no direct `ℚ` analogue. -/
theorem rat_no_folding_polynomial (p : ℚ[X])
    (h : ∀ a : ℚ, p.IsRoot a) : p = 0 :=
  eq_zero_of_infinite_isRoot p (Set.infinite_univ.mono (fun x _ => h x))

end LeanRiemann.Folding
