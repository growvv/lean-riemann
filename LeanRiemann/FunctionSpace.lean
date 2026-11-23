/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The folded function space

Stepanov's dimension count runs inside the space of *polynomial functions* on the base field.
This file proves the structural fact that makes that space finite-dimensional over a finite
field, and shows it fails over `ℚ`:

* `evalMap` — evaluation of a polynomial of degree `< q` at all points of a finite field `K`,
  as a linear map into the space `K → K` of all functions.
* `evalMap_injective` — a polynomial of degree `< q` vanishing everywhere is zero.
* `evalMap_bijective` — **every** function `K → K` is represented by a *unique* polynomial of
  degree `< q`. This is Frobenius folding in its sharpest form: the function space has exactly
  dimension `q`, and the degree-`< q` polynomials fill it.
* `rat_indicator_not_polynomial` — over `ℚ` the analogous map is not surjective: the indicator
  of `{0}` is not a polynomial.

There is no `sorry`.
-/

import Mathlib
import LeanRiemann.Folding

open Polynomial

set_option maxHeartbeats 800000

namespace LeanRiemann.FunctionSpace

variable {K : Type*} [Field K] [Fintype K]

/-- Evaluation of a polynomial of degree `< q` as a linear map into all functions `K → K`. -/
def evalMap : Polynomial.degreeLT K (Fintype.card K) →ₗ[K] (K → K) where
  toFun p := fun x => (p : K[X]).eval x
  map_add' p q := by
    ext x
    simp [eval_add]
  map_smul' c p := by
    ext x
    simp [eval_smul]

/-- A degree-`< q` polynomial that vanishes at every point of the finite field is zero: it would
have `q` roots but degree `< q`. -/
theorem evalMap_injective : Function.Injective (evalMap (K := K)) := by
  classical
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro p hp
  have hzero : (p : K[X]) = 0 := by
    by_contra hne
    have hsub : (Finset.univ : Finset K) ⊆ (p : K[X]).roots.toFinset := by
      intro x _
      rw [Multiset.mem_toFinset, mem_roots hne]
      have hx : (p : K[X]).eval x = 0 := by
        have := congrFun (LinearMap.mem_ker.mp hp) x
        simpa [evalMap] using this
      simpa [Polynomial.IsRoot] using hx
    have hcard : Fintype.card K ≤ (p : K[X]).roots.card := by
      calc Fintype.card K = (Finset.univ : Finset K).card := by simp
        _ ≤ (p : K[X]).roots.toFinset.card := Finset.card_le_card hsub
        _ ≤ (p : K[X]).roots.card := Multiset.toFinset_card_le _
    have hdeg : (p : K[X]).natDegree < Fintype.card K := by
      have hlt := Polynomial.mem_degreeLT.mp p.2
      exact (Polynomial.natDegree_lt_iff_degree_lt hne).mpr hlt
    have := card_roots' (p : K[X])
    omega
  exact Subtype.ext hzero

/-- The two spaces have the same dimension `q`. -/
theorem finrank_eq : Module.finrank K (Polynomial.degreeLT K (Fintype.card K)) =
    Module.finrank K (K → K) := by
  have e : Polynomial.degreeLT K (Fintype.card K) ≃ₗ[K] (Fin (Fintype.card K) → K) :=
    Polynomial.degreeLTEquiv K (Fintype.card K)
  calc Module.finrank K (Polynomial.degreeLT K (Fintype.card K))
      = Module.finrank K (Fin (Fintype.card K) → K) := LinearEquiv.finrank_eq e
    _ = Fintype.card (Fin (Fintype.card K)) := Module.finrank_fintype_fun_eq_card K
    _ = Fintype.card K := Fintype.card_fin _
    _ = Module.finrank K (K → K) := (Module.finrank_fintype_fun_eq_card K).symm

/-- **Every function on a finite field is a polynomial of degree `< q`.** The evaluation map is
onto: dimension `q` on both sides and injectivity force it. -/
theorem evalMap_surjective : Function.Surjective (evalMap (K := K)) := by
  have hker : LinearMap.ker (evalMap (K := K)) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact evalMap_injective
  have htop : LinearMap.range (evalMap (K := K)) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := LinearMap.finrank_range_add_finrank_ker (evalMap (K := K))
    rw [hker, finrank_bot, add_zero] at h
    rw [h]
    exact finrank_eq
  intro F
  have hF : F ∈ LinearMap.range (evalMap (K := K)) := by
    rw [htop]
    exact Submodule.mem_top
  simpa using (LinearMap.mem_range.mp hF)

/-- The evaluation map is a bijection. -/
theorem evalMap_bijective : Function.Bijective (evalMap (K := K)) :=
  ⟨evalMap_injective, evalMap_surjective⟩

/-- **Representation theorem.** Every function `F : K → K` agrees with a polynomial of degree
`< q` at every point. This is the finite-dimensional space Stepanov's dimension count works in. -/
theorem exists_poly_representing (F : K → K) :
    ∃ p : K[X], p.degree < (Fintype.card K : WithBot ℕ) ∧ ∀ x, p.eval x = F x := by
  obtain ⟨p, hp⟩ := evalMap_surjective F
  exact ⟨p, Polynomial.mem_degreeLT.mp p.2, fun x => congrFun hp x⟩

/-! ### Failure over `ℚ` -/

/-- **Over `ℚ` the function space is not spanned by polynomials.** The indicator of `{0}` is not
the evaluation of any polynomial: such a polynomial would vanish at every nonzero rational, hence
be zero, yet take value `1` at `0`. -/
theorem rat_indicator_not_polynomial :
    ¬ ∃ p : ℚ[X], ∀ x : ℚ, p.eval x = if x = 0 then 1 else 0 := by
  rintro ⟨p, hp⟩
  have hroot : ∀ x : ℚ, x ≠ 0 → p.IsRoot x := by
    intro x hx
    have hval : p.eval x = 0 := by
      rw [hp x, ite_eq_right hx]
    simpa [Polynomial.IsRoot] using hval
  have hinfinite : {x : ℚ | p.IsRoot x}.Infinite := by
    have hcompl : ({0}ᶜ : Set ℚ).Infinite :=
      Set.Finite.infinite_compl (Set.finite_singleton (0 : ℚ))
    apply hcompl.mono
    intro x hx
    exact hroot x (by simpa using hx)
  have hp0 : p = 0 := eq_zero_of_infinite_isRoot p hinfinite
  have h0 := hp 0
  rw [hp0] at h0
  simp at h0

end LeanRiemann.FunctionSpace
