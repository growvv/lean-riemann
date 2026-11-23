/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Why the elementary transplant stops at `ℤ`

This file collects, in one place, the precise elementary obstructions that appear when one tries
to move Stepanov's function-field argument to the integers. None of these is a statement that the
Riemann Hypothesis cannot be proved — a claimed proof announced in November 2026 goes through
automorphic machinery (chained theta lifts, GGP periods, Galois cohomology) far beyond this
elementary layer. What is proved here is narrower and exact: **the elementary skeleton alone
supplies none of the three things the method needs over `ℤ`.**

The three ingredients, and what happens to each:

1. **A folding polynomial.** Over `𝔽_q` the nonzero polynomial `X ^ q - X` vanishes at every
   point, so any polynomial can be reduced modulo it without changing its values, resetting the
   degree budget (`Folding.eval_modByMonic_X_pow_card_sub_X`,
   `Folding.degree_modByMonic_lt_card`). Over `ℚ` there is no nonzero polynomial vanishing
   everywhere (`Folding.rat_no_folding_polynomial`), so nothing folds.

2. **A finite-dimensional function space.** Over `𝔽_q` evaluation of degree-`< q` polynomials is
   a bijection onto *all* functions (`FunctionSpace.evalMap_bijective`). Over `ℚ` it is not even
   surjective (`FunctionSpace.rat_indicator_not_polynomial`).

3. **A Frobenius conjugation that injects `q` into the degree budget.** Over `𝔽_q`,
   `a ^ q = a` (`Stepanov.frobenius_fixed`) and on a curve `y ^ q = y * (y ^ 2) ^ ((q-1)/2)`
   (`Bound.frobenius_conj`). Over `ℚ`, `x ^ q = x` fails for every `q ≥ 2`
   (`Stepanov.rat_no_frobenius_fold`).

Consequently the elementary inequality chain the engine produces is *scale-invariant*
(`Bound.stepanov_inequalities_scale_invariant`): it bounds no number of points at all. Turning it
into a genuine `√q` bound requires an independent input tying the vanishing multiplicity to `q` —
the role Frobenius plays in the function-field case, and which the automorphic proof supplies by
different means.

There is no `sorry`.
-/

import Mathlib
import LeanRiemann.Stepanov
import LeanRiemann.Folding
import LeanRiemann.FunctionSpace
import LeanRiemann.Bound

open Polynomial

namespace LeanRiemann.Obstruction

/-- **The folding dichotomy.** A finite field has a *nonzero* polynomial vanishing at every point
(`X ^ q - X`), while `ℚ` has none. This is the sharpest form of the failure of the first
ingredient: the "folding polynomial" that lets the function-field method reset its degree budget
exists only in the finite-field world. -/
theorem folding_dichotomy {K : Type*} [Field K] [Fintype K] :
    (∃ f : K[X], f ≠ 0 ∧ ∀ a : K, f.eval a = 0) ∧
      (¬ ∃ p : ℚ[X], p ≠ 0 ∧ ∀ a : ℚ, p.eval a = 0) := by
  refine ⟨?_, ?_⟩
  · refine ⟨X ^ Fintype.card K - X, ?_, ?_⟩
    · exact X_pow_sub_X_ne_zero Fintype.one_lt_card
    · intro a
      simpa [Polynomial.IsRoot] using Folding.X_pow_card_sub_X_isRoot a
  · rintro ⟨p, hp, hroot⟩
    exact hp (Folding.rat_no_folding_polynomial p hroot)

/-- **The elementary chain bounds nothing.** Re-exported from `Bound`: for every `N` and every
`n ≤ N` there are parameters satisfying both elementary Stepanov inequalities. Hence the
elementary skeleton, on its own, gives no upper bound on the number of points — the concrete
sense in which "Stepanov with multiplicity, naively transplanted" is vacuous without a further
input. -/
theorem elementary_chain_no_bound (N n : ℕ) (hn : n ≤ N) :
    ∃ a b m D : ℕ, 0 < m ∧ m * N ≤ D ∧ m * N ≤ max (2 * a) (n + 2 * b) :=
  Bound.stepanov_inequalities_scale_invariant N n hn

end LeanRiemann.Obstruction
