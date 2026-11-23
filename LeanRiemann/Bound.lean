/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Where `√q` comes from — and why the current ingredients do not produce it

Two results, both fully proved:

* `sqrt_of_balanced` — the arithmetic that produces a `√`: if `N ≤ A * t + B / t` for *every*
  `t > 0`, then `N ≤ 2 * √(A * B)`. This is the mechanism behind the `√q` in the Weil bound,
  and it needs a bound that holds *uniformly in a free parameter* `t`.

* `stepanov_inequalities_scale_invariant` — **a negative result.** The two inequalities the
  Stepanov engine currently provides,
  `m * N ≤ D` (existence, `D` = dimension of the degree-`< D` space) and
  `m * N ≤ max (2a) (n + 2b)` (the conjugate-norm degree budget),
  are satisfiable for *every* `N` and every `n ≤ N` (take `m = 1`, `a = b = D = N`). So they
  impose **no upper bound on `N`**, and no choice of parameters can extract a `√q` saving from
  them alone. A genuine `√q` bound needs an *independent* input — a lower bound tying `m * N`
  to `N` that comes from the curve's Frobenius / Riemann–Roch structure. That is precisely the
  content that `Folding.rat_no_folding_polynomial` shows is unavailable over `ℚ`.

There is no `sorry`.
-/

import Mathlib

namespace LeanRiemann.Bound

/-- **The arithmetic source of `√q`.** If `N ≤ A * t + B / t` for all `t > 0` (with `A > 0`,
`B ≥ 0`), then `N ≤ 2 * √(A * B)`. The optimum is at `t = √(B / A)`, where `A * t + B / t`
equals `2√(A B)` — this is the AM–GM inequality in disguise. -/
theorem sqrt_of_balanced (N A B : ℝ) (hA : 0 < A) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 < t → N ≤ A * t + B / t) : N ≤ 2 * Real.sqrt (A * B) := by
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · -- B = 0: `N ≤ A * t` for all `t > 0` forces `N ≤ 0`.
    rw [← hB0, mul_zero, Real.sqrt_zero, mul_zero]
    by_contra hN
    push Not at hN
    have ht : (0 : ℝ) < N / (2 * A) := by positivity
    have hb := h (N / (2 * A)) ht
    rw [← hB0, zero_div, add_zero] at hb
    have heq : A * (N / (2 * A)) = N / 2 := by field_simp
    nlinarith [hb, heq, hN]
  · -- B > 0: plug in the optimal `t = √(B / A)`.
    set t := Real.sqrt (B / A) with ht_def
    have htpos : 0 < t := Real.sqrt_pos.mpr (div_pos hBpos hA)
    have htsq : t ^ 2 = B / A := Real.sq_sqrt (le_of_lt (div_pos hBpos hA))
    have hkey := h t htpos
    have htne : t ≠ 0 := ne_of_gt htpos
    have hpos : 0 < A * t + B / t := by positivity
    have expand : (A * t + B / t) ^ 2 = 4 * (A * B) := by
      have e : A * t + B / t = (A * t ^ 2 + B) / t := by field_simp
      rw [e, htsq]
      field_simp
      have hAt : A * t ^ 2 = B := by rw [htsq]; field_simp
      nlinarith [hAt]
    have hsqrt : Real.sqrt ((A * t + B / t) ^ 2) = A * t + B / t := Real.sqrt_sq (le_of_lt hpos)
    rw [expand] at hsqrt
    have h4 : Real.sqrt (4 * (A * B)) = 2 * Real.sqrt (A * B) := by
      rw [show (4 : ℝ) * (A * B) = 2 ^ 2 * (A * B) by norm_num]
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by norm_num)]
    rw [h4] at hsqrt
    linarith [hkey, hsqrt]

/-- **The obstruction (negative result).** The Stepanov inequality system as formalized —
`m * N ≤ D` and `m * N ≤ max (2a) (n + 2b)` — is satisfiable for every `N` with `n ≤ N`. Hence
it bounds nothing, and parameter tuning cannot extract a `√q` saving. A real bound requires an
independent lower bound on `m * N` from the curve's structure (Frobenius / Riemann–Roch). -/
theorem stepanov_inequalities_scale_invariant (N n : ℕ) (hn : n ≤ N) :
    ∃ a b m D : ℕ, 0 < m ∧ m * N ≤ D ∧ m * N ≤ max (2 * a) (n + 2 * b) := by
  refine ⟨N, N, 1, N, by norm_num, ?_, ?_⟩
  · omega
  · rw [Nat.one_mul]; omega

/-- **Frobenius conjugation on a hyperelliptic curve.** Over an odd finite field, at a point
`(x, y)` with `y ^ 2 = f(x)` one has `y ^ q = y * (y ^ 2) ^ ((q - 1) / 2)`. This identity — the
one genuine extra input that a correct Stepanov argument uses — is where the parameter `t`
appearing in `sqrt_of_balanced` is meant to come from (through the degree of `f ^ ((q-1)/2)`).
Over `ℚ` it has no analogue (`Folding.rat_no_folding_polynomial`). -/
theorem frobenius_conj {K : Type*} [Field K] [Fintype K] (hq : Fintype.card K % 2 = 1)
    (y : K) :
    y ^ Fintype.card K = y * (y ^ 2) ^ ((Fintype.card K - 1) / 2) := by
  have hc : 1 ≤ Fintype.card K := Fintype.card_pos
  have hsplit : Fintype.card K = 2 * ((Fintype.card K - 1) / 2) + 1 := by omega
  nth_rewrite 1 [hsplit]
  rw [pow_add, pow_one, pow_mul]
  ring

end LeanRiemann.Bound
