/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Stepanov step on a hyperelliptic curve

This file formalizes the curve-specific heart of Stepanov's argument for `y ^ 2 = f(x)`.

The auxiliary polynomial is `A(x) + y · B(x)`. Its **conjugate norm** is
`Q(x) = A(x) ^ 2 - f(x) · B(x) ^ 2`, a polynomial in `x` alone. Two facts drive the method:

* `conjugate_vanishes` — if `A(x) + y B(x) = 0` at a curve point `y ^ 2 = f(x)`, then `Q(x) = 0`.
* `two_fibre_double_vanishing` — in odd characteristic, if *both* branches `±y` at the same `x`
  satisfy the vanishing, then `A(x) = B(x) = 0`, so `(X - C x) ^ 2 ∣ Q`: a full fibre forces
  **double** vanishing.

The counting conclusion `two_fibre_card_le` then bounds the number of full fibres by
`natDegree Q / 2` — the multiplicity budget of `LeanRiemann.Stepanov`. There is no `sorry`.
-/

import Mathlib
import LeanRiemann.Stepanov

open Polynomial

namespace LeanRiemann.Curve

variable {K : Type*} [Field K]

/-- **Conjugate vanishing.** At a point `(x, y)` of `y ^ 2 = f(x)`, if the auxiliary polynomial
`A + y B` vanishes, then the conjugate norm `A ^ 2 - f * B ^ 2` vanishes at `x`. -/
theorem conjugate_vanishes (f A B : K[X]) {x y : K}
    (hy : y ^ 2 = f.eval x) (h : A.eval x + y * B.eval x = 0) :
    (A ^ 2 - f * B ^ 2).eval x = 0 := by
  simp only [eval_sub, eval_mul, eval_pow]
  have hsq : A.eval x ^ 2 - f.eval x * B.eval x ^ 2 =
      (A.eval x - y * B.eval x) * (A.eval x + y * B.eval x) := by
    rw [← hy]
    ring
  rw [hsq, h, mul_zero]

/-- Degree budget for the conjugate norm:
`natDegree (A ^ 2 - f * B ^ 2) ≤ max (2 * natDegree A) (natDegree f + 2 * natDegree B)`. -/
theorem natDegree_conjugate_le (f A B : K[X]) :
    (A ^ 2 - f * B ^ 2).natDegree ≤
      max (2 * A.natDegree) (f.natDegree + 2 * B.natDegree) := by
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · rw [natDegree_pow]
    exact le_max_left _ _
  · calc (f * B ^ 2).natDegree ≤ f.natDegree + (B ^ 2).natDegree := natDegree_mul_le
      _ = f.natDegree + 2 * B.natDegree := by rw [natDegree_pow]
      _ ≤ max (2 * A.natDegree) (f.natDegree + 2 * B.natDegree) := le_max_right _ _

/-- **Counting from the conjugate norm.** If `A + y B` vanishes at one point above each
`x ∈ S`, then `|S| ≤ natDegree (A ^ 2 - f * B ^ 2)`, provided the conjugate norm is nonzero. -/
theorem card_le_natDegree_of_conjugate (f A B : K[X])
    (hQ : A ^ 2 - f * B ^ 2 ≠ 0) (S : Finset K)
    (h : ∀ x ∈ S, ∃ y : K, y ^ 2 = f.eval x ∧ A.eval x + y * B.eval x = 0) :
    S.card ≤ (A ^ 2 - f * B ^ 2).natDegree := by
  classical
  have hsub : S ⊆ (A ^ 2 - f * B ^ 2).roots.toFinset := by
    intro x hx
    obtain ⟨y, hy, hv⟩ := h x hx
    rw [Multiset.mem_toFinset, mem_roots hQ]
    exact conjugate_vanishes f A B hy hv
  calc S.card ≤ (A ^ 2 - f * B ^ 2).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ (A ^ 2 - f * B ^ 2).roots.card := Multiset.toFinset_card_le _
    _ ≤ (A ^ 2 - f * B ^ 2).natDegree := card_roots' _

/-! ### Double vanishing at full fibres -/

/-- In odd characteristic, if both branches `±y` (`y ≠ 0`) above `x` give vanishing, then
`A(x) = B(x) = 0`. -/
theorem both_branches_vanish (_f A B : K[X]) (hchar : (2 : K) ≠ 0) {x y : K}
    (hyne : y ≠ 0)
    (h1 : A.eval x + y * B.eval x = 0)
    (h2 : A.eval x + (-y) * B.eval x = 0) :
    A.eval x = 0 ∧ B.eval x = 0 := by
  have h2A : (2 : K) * A.eval x = 0 := by
    have h := h1
    have := h2
    linear_combination h + h2
  have hA0 : A.eval x = 0 := (mul_eq_zero.mp h2A).resolve_left hchar
  refine ⟨hA0, ?_⟩
  have hyB : y * B.eval x = 0 := by
    have := h1
    rw [hA0, zero_add] at this
    exact this
  rcases mul_eq_zero.mp hyB with h | h
  · exact absurd h hyne
  · exact h

/-- **Double vanishing.** In odd characteristic, `A(x) = B(x) = 0` forces
`(X - C x) ^ 2 ∣ A ^ 2 - f * B ^ 2`. -/
theorem two_fibre_double_vanishing (f A B : K[X]) {x : K}
    (hA : A.eval x = 0) (hB : B.eval x = 0) :
    (X - C x) ^ 2 ∣ A ^ 2 - f * B ^ 2 := by
  have hAd : (X - C x) ∣ A := dvd_iff_isRoot.mpr hA
  have hBd : (X - C x) ∣ B := dvd_iff_isRoot.mpr hB
  have hA2 : (X - C x) ^ 2 ∣ A ^ 2 := by
    have := mul_dvd_mul hAd hAd
    simpa [pow_two] using this
  have hB2 : (X - C x) ^ 2 ∣ B ^ 2 := by
    have := mul_dvd_mul hBd hBd
    simpa [pow_two] using this
  exact dvd_sub hA2 (dvd_mul_of_dvd_right hB2 f)

/-- **Full-fibre counting.** In odd characteristic, if every `x ∈ S` has two branches `±y`
(`y ≠ 0`) at which `A + y B` vanishes, then `2 * |S| ≤ natDegree (A ^ 2 - f * B ^ 2)`.

This is the Stepanov multiplicity gain: each full fibre costs *two* units of degree budget. -/
theorem two_fibre_card_le (f A B : K[X]) (hchar : (2 : K) ≠ 0)
    (hQ : A ^ 2 - f * B ^ 2 ≠ 0) (S : Finset K)
    (h : ∀ x ∈ S, ∃ y : K, y ≠ 0 ∧ y ^ 2 = f.eval x ∧
      A.eval x + y * B.eval x = 0 ∧ A.eval x + (-y) * B.eval x = 0) :
    2 * S.card ≤ (A ^ 2 - f * B ^ 2).natDegree := by
  classical
  have hvan : ∀ x ∈ S, 2 ≤ (A ^ 2 - f * B ^ 2).rootMultiplicity x := by
    intro x hx
    obtain ⟨y, hyne, _hy, h1, h2⟩ := h x hx
    obtain ⟨hA0, hB0⟩ := both_branches_vanish f A B hchar hyne h1 h2
    rw [le_rootMultiplicity_iff hQ]
    exact two_fibre_double_vanishing f A B hA0 hB0
  exact Stepanov.stepanov_multiplicity_bound _ hQ S 2 hvan

end LeanRiemann.Curve
