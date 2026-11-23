/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Jets and the existence of the Stepanov auxiliary polynomial

This file supplies the missing half of the Stepanov engine: the *existence* of an auxiliary
polynomial with prescribed high-order vanishing at a finite set of points, obtained by dimension
counting on a jet evaluation map.

* `X_sub_C_pow_dvd_iff_hasseDeriv` — `(X - C t)^n ∣ p` iff the first `n` Hasse derivatives of `p`
  vanish at `t`. (The jet, i.e. determinant-friendly, characterization of multiplicity.)
* `jetMap` — the linear map sending `p` to all Hasse jets `(∂^i p)(s)` for `s ∈ S`, `i < k`.
* `exists_auxiliary_polynomial` — if `k * |S| < D`, there is a nonzero `p` of degree `< D` that
  vanishes to order `≥ k` at every point of `S`. This is Stepanov's auxiliary polynomial,
  produced by the dimension count `dim conditions < dim space`.

There is no `sorry`.
-/

import Mathlib
import LeanRiemann.Stepanov

open Polynomial

namespace LeanRiemann.Jets

variable {K : Type*} [Field K]

/-- **Jets detect multiplicity.** `(X - C t)^n` divides `p` exactly when the first `n` Hasse
derivatives of `p` vanish at `t`. This is the "multiplicity via jets/determinants" identity. -/
theorem X_sub_C_pow_dvd_iff_hasseDeriv (p : K[X]) (t : K) (n : ℕ) :
    (X - C t) ^ n ∣ p ↔ ∀ k < n, (hasseDeriv k p).eval t = 0 := by
  rw [Polynomial.X_sub_C_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
  constructor
  · intro h k hk
    have hk' := h k hk
    rwa [← Polynomial.taylor_apply, Polynomial.taylor_coeff] at hk'
  · intro h d hd
    have := h d hd
    rwa [← Polynomial.taylor_apply, Polynomial.taylor_coeff]

/-- The jet evaluation map: send `p` to the family of its Hasse jets at the points of `S`. -/
noncomputable def jetMap (S : Finset K) (k D : ℕ) :
    Polynomial.degreeLT K D →ₗ[K] ((S × Fin k) → K) where
  toFun p q := (Polynomial.hasseDeriv q.2.val (p : K[X])).eval q.1.val
  map_add' p q := by
    ext ⟨s, i⟩
    simp [Polynomial.eval_add]
  map_smul' c p := by
    ext ⟨s, i⟩
    simp [Polynomial.eval_smul]

/-- The jet map has `k * |S|` outputs. -/
theorem finrank_jet_codomain (S : Finset K) (k : ℕ) :
    Module.finrank K ((S × Fin k) → K) = S.card * k := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_coe]

/-- The source has dimension `D`. -/
theorem finrank_degreeLT (D : ℕ) :
    Module.finrank K (Polynomial.degreeLT K D) = D := by
  have e : Polynomial.degreeLT K D ≃ₗ[K] (Fin D → K) := Polynomial.degreeLTEquiv K D
  rw [LinearEquiv.finrank_eq e, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- **Existence of the Stepanov auxiliary polynomial.** If the number of jet conditions `k * |S|`
is smaller than the dimension `D` of the degree-`< D` polynomial space, then some nonzero
polynomial of degree `< D` vanishes to order `≥ k` at *every* point of `S`.

This is the dimension count that drives the method: more unknowns than equations, so a nontrivial
solution exists, and by `X_sub_C_pow_dvd_iff_hasseDeriv` it is highly vanishing. -/
theorem exists_auxiliary_polynomial (S : Finset K) (k D : ℕ)
    (h : S.card * k < D) :
    ∃ p : K[X], p ∈ Polynomial.degreeLT K D ∧ p ≠ 0 ∧
      ∀ s ∈ S, k ≤ p.rootMultiplicity s := by
  classical
  have hrank : Module.finrank K ((S × Fin k) → K) <
      Module.finrank K (Polynomial.degreeLT K D) := by
    rw [finrank_jet_codomain, finrank_degreeLT]
    exact h
  have hker : LinearMap.ker (jetMap (K := K) S k D) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hrank
  obtain ⟨p, hpker, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hpne : (p : K[X]) ≠ 0 := by
    intro hzero
    exact hp0 (Subtype.ext hzero)
  refine ⟨p, p.2, hpne, fun s hs => ?_⟩
  rw [Polynomial.le_rootMultiplicity_iff hpne]
  rw [X_sub_C_pow_dvd_iff_hasseDeriv]
  intro i hi
  have hjet : jetMap (K := K) S k D p = 0 := LinearMap.mem_ker.mp hpker
  have := congrFun hjet (⟨s, hs⟩, ⟨i, hi⟩)
  simpa [jetMap] using this

/-- **The Stepanov engine, in one statement.** If the number of jet conditions `k * |S|` is
below the dimension `D`, then an auxiliary polynomial exists with degree `< D` that vanishes to
order `≥ k` at every point of `S`, and the multiplicity bound then forces `k * |S| ≤ natDegree p`.

This packages the two halves — dimension-count existence and multiplicity counting — into the
single inequality every Stepanov argument is built to contradict. -/
theorem stepanov_engine (S : Finset K) (k D : ℕ) (h : S.card * k < D) :
    ∃ p : K[X], p ∈ Polynomial.degreeLT K D ∧ p ≠ 0 ∧
      k * S.card ≤ p.natDegree ∧ p.natDegree < D := by
  obtain ⟨p, hpD, hpne, hvan⟩ := exists_auxiliary_polynomial S k D h
  refine ⟨p, hpD, hpne, ?_, ?_⟩
  · exact Stepanov.stepanov_multiplicity_bound p hpne S k hvan
  · exact (Polynomial.natDegree_lt_iff_degree_lt hpne).mpr
      (Polynomial.mem_degreeLT.mp hpD)

end LeanRiemann.Jets
