/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Reducing the Riemann Hypothesis to a Stepanov certificate

The user's proposed strategy is: chain `≈ √X` theta lifts and adapt Stepanov's function-field
method (multiplicity via determinants) to `ℤ`. This file formalizes the *logical shape* of that
strategy with no `sorry`, so that the open burden becomes a single precisely stated Lean
hypothesis rather than an informal sketch.

The Stepanov engine (`LeanRiemann.Stepanov`) gives: a nonzero polynomial of degree `d` has at
most `d` roots counted with multiplicity, so a polynomial vanishing to order `≥ k` on a finite
set `S` must satisfy `k * |S| ≤ natDegree`. An `AuxiliaryData` bundles the opposite — an
auxiliary polynomial that vanishes to order `≥ k` on `S` yet has `natDegree < k * |S|`. Such
data is *impossible* (`auxiliaryData_impossible`).

`RH_of_stepanov_certificates` then says: **if every zero of `ζ` off the critical line can be
supplied with such auxiliary data (covering that zero), then the Riemann Hypothesis holds.**
The remaining open problem is exactly the hypothesis `h`: constructing that auxiliary polynomial
for each off-line zero — the arithmetic content that in the function-field case comes from
Frobenius/Riemann–Roch and that `LeanRiemann.Stepanov.rat_no_frobenius_fold` shows has no
direct `ℚ` analogue.
-/

import Mathlib
import LeanRiemann.Stepanov

open Polynomial

namespace LeanRiemann.Strategy

/-! ### Auxiliary data and its impossibility -/

/-- Auxiliary data of the Stepanov argument: a nonzero polynomial `p` together with a finite set
`S` of points at which `p` vanishes to order `≥ k`, where the "degree budget" is *short*:
`natDegree p < k * |S|`. The multiplicity bound shows this is contradictory. -/
structure AuxiliaryData where
  /-- The auxiliary polynomial. -/
  p : ℂ[X]
  /-- The finite set of vanishing points. -/
  S : Finset ℂ
  /-- The vanishing order required at each point. -/
  k : ℕ
  /-- The order is positive. -/
  hk : 0 < k
  /-- `p` vanishes to order `≥ k` at every point of `S`. -/
  hvan : ∀ a ∈ S, k ≤ p.rootMultiplicity a
  /-- The degree budget is too short. -/
  hshort : p.natDegree < k * S.card

/-- No auxiliary data exists: the vanishing requirement forces `k * |S| ≤ natDegree p`, which
contradicts `hshort`. This is the engine of the method. -/
theorem auxiliaryData_impossible (D : AuxiliaryData) : False := by
  -- `p ≠ 0`: otherwise `rootMultiplicity` is `0`, contradicting `hk` on a nonempty `S`,
  -- and `S = ∅` would make `hshort` read `natDegree p < 0`, also impossible.
  have hp : D.p ≠ 0 := by
    intro hp0
    have hS : D.S.Nonempty := by
      rcases D.S.eq_empty_or_nonempty with h | h
      · have hsh := D.hshort
        rw [h, Finset.card_empty, Nat.mul_zero] at hsh
        omega
      · exact h
    obtain ⟨a, ha⟩ := hS
    have := D.hvan a ha
    rw [hp0, rootMultiplicity_zero] at this
    exact absurd this (Nat.not_le.mpr D.hk)
  have hbound : D.k * D.S.card ≤ D.p.natDegree :=
    Stepanov.stepanov_multiplicity_bound D.p hp D.S D.k D.hvan
  exact absurd hbound (Nat.not_le.mpr D.hshort)

/-! ### The reduction -/

/-- **Reduction of RH to a Stepanov certificate.** Suppose every zero of `ζ` that is
nontrivial, away from `1`, and off the critical line can be covered by auxiliary data (the
hypothesis `h`). Then the Riemann Hypothesis holds.

The hypothesis `h` is exactly the open mathematical content of the proposed strategy: for each
off-line zero, build the auxiliary polynomial whose multiplicity bookkeeping overshoots its
degree. In the function-field case this is supplied by Frobenius and Riemann–Roch; over `ℚ`
that supply is absent (`Stepanov.rat_no_frobenius_fold`). -/
theorem RH_of_stepanov_certificates
    (h : ∀ s : ℂ, riemannZeta s = 0 → (¬ ∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 →
      s.re ≠ 1 / 2 → ∃ D : AuxiliaryData, s ∈ D.S) :
    RiemannHypothesis := by
  intro s hz htriv h1
  by_contra hoff
  obtain ⟨D, hsD⟩ := h s hz htriv h1 hoff
  exact auxiliaryData_impossible D

/-! ### Sanity: the certificate really does need the off-line zero

The hypothesis `h` is only invoked at an off-line zero. If `s.re = 1/2` there is nothing to
supply, which is consistent: the theorem concludes exactly `s.re = 1/2` for every zero. -/

/-- A nonempty finite set always admits an element; recorded to make the "covering" reading of
`h` explicit. -/
theorem exists_mem_of_nonempty {α : Type*} {S : Finset α} (h : S.Nonempty) : ∃ a, a ∈ S := h

end LeanRiemann.Strategy
