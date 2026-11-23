/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Stepanov engine, formalized

This file formalizes the *provable core* of Stepanov's method (the technique behind the
Weil bound for function fields over finite fields), stripped of any specific curve:

* `sum_rootMultiplicity_le_natDegree` — a nonzero polynomial of degree `d` has at most `d`
  roots *counted with multiplicity*. This is the "multiplicity bound".
* `stepanov_multiplicity_bound` — if a nonzero polynomial vanishes to order `≥ k` at each
  point of a finite set `S`, then `k * |S| ≤ natDegree p`. This is the counting inequality
  that Stepanov's auxiliary polynomial is designed to contradict.
* `exists_ne_zero_mem_ker` — the dimension count: a linear map out of a larger space into a
  smaller one has a nonzero kernel element. This is how Stepanov *produces* the auxiliary
  polynomial.
* `frobenius_fixed` — over a finite field, `a ^ q = a` for all `a` (`q = #K`). This is the
  "Frobenius folds the function field" identity the method relies on.
* `rat_no_frobenius_fold` — the same identity is *false* over `ℚ`. This is the precise,
  provable reason the method does not transfer from `𝔽_q` to the integers.

Everything here is proved; there is no `sorry`.
-/

import Mathlib

open Polynomial

namespace LeanRiemann.Stepanov

/-! ### The multiplicity bound -/

/-- A nonzero polynomial has at most `natDegree` roots counted with multiplicity.
This is the engine of every Stepanov-style argument: each vanishing condition consumes one
unit of "degree budget". -/
theorem sum_rootMultiplicity_le_natDegree {K : Type*} [Field K]
    (p : K[X]) (_hp : p ≠ 0) (S : Finset K) :
    ∑ a ∈ S, p.rootMultiplicity a ≤ p.natDegree := by
  classical
  -- replace multiplicities by multiplicities of the root multiset
  have hcount : ∀ a : K, p.rootMultiplicity a = Multiset.count a p.roots :=
    fun a => (count_roots p).symm
  simp_rw [hcount]
  -- enlarge `S` to `S ∪ roots.toFinset`; counts outside the roots vanish
  have h1 : ∑ a ∈ S, Multiset.count a p.roots
      ≤ ∑ a ∈ S ∪ p.roots.toFinset, Multiset.count a p.roots := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.subset_union_left
    · intro i _ _; exact Nat.zero_le _
  -- the enlarged sum is exactly the total number of roots (with multiplicity)
  have h2 : ∑ a ∈ S ∪ p.roots.toFinset, Multiset.count a p.roots = p.roots.card := by
    refine Multiset.sum_count_eq_card (fun a ha => ?_)
    rw [Finset.mem_union]
    exact Or.inr (Multiset.mem_toFinset.mpr ha)
  calc ∑ a ∈ S, Multiset.count a p.roots
      ≤ ∑ a ∈ S ∪ p.roots.toFinset, Multiset.count a p.roots := h1
    _ = p.roots.card := h2
    _ ≤ p.natDegree := card_roots' p

/-- **Stepanov counting inequality.** If a nonzero polynomial vanishes to order `≥ k` at
every point of `S`, then `k * |S| ≤ natDegree p`. A Stepanov auxiliary polynomial is built so
that it *must* have too many high-order zeros, contradicting this bound. -/
theorem stepanov_multiplicity_bound {K : Type*} [Field K]
    (p : K[X]) (hp : p ≠ 0) (S : Finset K) (k : ℕ)
    (h : ∀ a ∈ S, k ≤ p.rootMultiplicity a) :
    k * S.card ≤ p.natDegree := by
  calc k * S.card = S.card * k := Nat.mul_comm k S.card
    _ = ∑ _a ∈ S, k := by simp [Finset.sum_const]
    _ ≤ ∑ a ∈ S, p.rootMultiplicity a := Finset.sum_le_sum h
    _ ≤ p.natDegree := sum_rootMultiplicity_le_natDegree p hp S

/-! ### The dimension count (existence of the auxiliary polynomial) -/

/-- **Dimension count.** A linear map from a space of larger dimension into one of smaller
dimension has a nonzero kernel element. This is how the auxiliary polynomial is produced: the
evaluation map on a space of polynomials has more inputs than the number of linear conditions
it is asked to satisfy, so something nonzero is forced to vanish to high order. -/
theorem exists_ne_zero_mem_ker {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (h : Module.finrank K W < Module.finrank K V) :
    ∃ v : V, v ≠ 0 ∧ f v = 0 := by
  have hker : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt h
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨v, hv0, LinearMap.mem_ker.mpr hv⟩

/-! ### Frobenius: where the method lives, and where it dies -/

/-- Over a finite field `K` with `q = #K` elements, the `q`-power map is the identity:
`a ^ q = a` for every `a`. This is the "Frobenius folds the function field" identity that
Stepanov's method depends on. -/
theorem frobenius_fixed {K : Type*} [Field K] [Fintype K] (a : K) :
    a ^ Fintype.card K = a :=
  FiniteField.pow_card a

/-- **The obstruction over `ℚ`.** For any `q ≥ 2`, the `q`-power map is *not* the identity on
`ℚ`. Hence the Frobenius-folding identity `a ^ q = a` that the Stepanov/Weil machinery rests on
has no analogue over the rationals — this is the concrete, provable reason the method does not
carry over to `ℤ` unchanged. -/
theorem rat_no_frobenius_fold (q : ℕ) (hq : 2 ≤ q) :
    ¬ (∀ x : ℚ, x ^ q = x) := by
  intro h
  have h2 : (2 : ℚ) ^ q = 2 := h 2
  have hmono : (2 : ℚ) ^ 2 ≤ (2 : ℚ) ^ q := pow_le_pow_right₀ (by norm_num) hq
  rw [h2] at hmono
  norm_num at hmono

/-! ### Chaining theta lifts -/

/-- A single "theta lift" step: a self-map of a state space that preserves a predicate `P`
(e.g. a positivity / spectral property). -/
structure ThetaStep {State : Type*} (P : State → Prop) where
  /-- The underlying map. -/
  step : State → State
  /-- The map preserves `P`. -/
  preserves : ∀ s, P s → P (step s)

/-- **Chaining.** Iterating a theta lift `n` times preserves `P`. This is the formal content of
"chaining `n` theta lifts": preservation is stable under composition, so a chain of any length
keeps whatever invariant the individual lifts keep. -/
theorem ThetaStep.iterate_preserves {State : Type*} {P : State → Prop}
    (t : ThetaStep P) (n : ℕ) (s : State) (hs : P s) :
    P ((t.step^[n]) s) := by
  induction n generalizing s with
  | zero => simpa using hs
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact t.preserves _ (ih s hs)

/-- The number of lifts in the chain is about `√X` (here `⌊√X⌋`, a computable stand-in for
"`≈ √X`"). -/
def chainLength (X : ℕ) : ℕ := Nat.sqrt X

theorem chainLength_le (X : ℕ) : chainLength X ≤ X :=
  Nat.sqrt_le_self X

/-! ### Determinants implement multiplicity

The user's phrasing is "multiplicity via determinants". Concretely: a Vandermonde matrix built
from *distinct* points is invertible, so a linear system with more unknowns than equations has a
nonzero solution whose vanishing conditions are met — this is the linear-algebra face of the
same `k * |S| ≤ natDegree` bookkeeping. We record both halves. -/

/-- **A Vandermonde matrix on distinct points is nonsingular.** This is the determinant form of
"distinct points are independent", the rigidity that makes determinant counting work. -/
theorem vandermonde_det_ne_zero {K : Type*} [Field K] {n : ℕ} (v : Fin n → K)
    (hv : Function.Injective v) :
    (Matrix.vandermonde v).det ≠ 0 :=
  Matrix.det_vandermonde_ne_zero_iff.mpr hv

/-- **Determinant counting: an overdetermined homogeneous system has a nonzero solution.**
A linear map with more inputs than outputs (here a matrix with more columns than rows) has a
nonzero kernel element. This is how the Stepanov auxiliary polynomial is produced — the
"determinant method" in its linear-algebra form. -/
theorem matrix_exists_ne_zero_mulVec_eq_zero {K : Type*} [Field K]
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) (h : m < n) :
    ∃ v : Fin n → K, v ≠ 0 ∧ A.mulVec v = 0 := by
  have hker : LinearMap.ker A.mulVecLin ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨v, hv0, LinearMap.mem_ker.mp hv⟩

end LeanRiemann.Stepanov
