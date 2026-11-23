# lean-riemann

A Lean 4 + Mathlib formalization of **the elementary skeleton of Stepanov's method, and the
precise points where its naive transplant to the integers stops.**

The starting point was the route: *chain `≈ √X` theta lifts between unitary groups, and adapt
Stepanov's function-field method (multiplicity via determinants) to the integers.* This is not a
speculative route — it is the mechanism of the Riemann Hypothesis proof announced on
2026-11-20 by Levent Alpöge (with Claude), released only as a Lean formalization. See
[Relationship to the announced proof](#relationship-to-the-announced-proof) below.

**This repository does not contain a proof of the Riemann Hypothesis**, and it contains **no
`sorry` and no custom axioms** — only Lean's standard three (`propext`, `Classical.choice`,
`Quot.sound`). What it contains is the part of the story that can be checked in a few thousand
lines: the Stepanov engine, the Frobenius folding that makes it work over `𝔽_q`, and machine-
checked proofs that the elementary layer supplies none of what is needed over `ℤ`.

```bash
lake build
lake env lean - <<'EOF'
import LeanRiemann
#print axioms LeanRiemann.Strategy.RH_of_stepanov_certificates
#print axioms LeanRiemann.Obstruction.folding_dichotomy
EOF
```

## Relationship to the announced proof

On 2026-11-20, Levent Alpöge announced a proof of RH and of GRH for Dirichlet L-functions,
published as ~17M lines / 175,187 Lean files with no human-readable write-up. His own note
([alpo.ge/remark.pdf](https://alpo.ge/remark.pdf)) describes exactly this route: Stepanov's
argument uses a divisor involving multiplicity, "multiplicity is hard to find over the integers",
so the argument *chains theta lifts* whose length is `≈ √X`, each lift mimicking `√multiplicity`.

Status of that claim (as of 2026-11-23, from the community verification repository
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
and its [`verification/NOTES.md`](https://github.com/leanprover-community/riemann-hypothesis/blob/main/verification/NOTES.md)):

- **Verified:** all modules build; the exported proof is accepted by independent kernel
  implementations (nanoda, con-leche, lean4lean); the only axioms are the standard three; a static
  scan finds no `axiom`/`sorry`/`opaque`/`native_decide`/`unsafe`; the statements match **Mathlib's
  `RiemannHypothesis`** and an independently written GRH statement in `formal-conjectures`
  (comparator, ~53,000 constants matched by name).
- **Not yet done:** a completed end-to-end `lake comparator` run; the build provenance (the build
  ran unsandboxed); a human-readable proof; peer review. Scope is Dirichlet L-functions, not
  Dedekind/Hecke/ERH.

The present repository sits *below* that proof. It formalizes the elementary layer that the
automorphic proof replaces, and proves — not asserts — why the elementary layer is insufficient on
its own. It is a study of the **skeleton and its breaking point**, not a reconstruction.

## The engine (`LeanRiemann/Stepanov.lean`)

- `sum_rootMultiplicity_le_natDegree` — a nonzero polynomial of degree `d` has at most `d` roots
  counted with multiplicity.
- `stepanov_multiplicity_bound` — if `p ≠ 0` vanishes to order `≥ k` on `S`, then `k * |S| ≤ deg p`.
- `exists_ne_zero_mem_ker` — the dimension count producing the auxiliary polynomial.
- `frobenius_fixed` / `rat_no_frobenius_fold` — `a ^ q = a` over `𝔽_q`, **false** over `ℚ`.
- `vandermonde_det_ne_zero`, `matrix_exists_ne_zero_mulVec_eq_zero` — "multiplicity via
  determinants": distinct points give a nonsingular Vandermonde matrix; an overdetermined
  homogeneous system has a nonzero solution.
- `ThetaStep.iterate_preserves`, `chainLength X = ⌊√X⌋` — the formal shape of "chaining `n` lifts".

## Folding over `𝔽_q`, and its failure over `ℚ` (`Folding.lean`, `FunctionSpace.lean`)

- `X_pow_card_sub_X_isRoot` — `X ^ q - X` vanishes everywhere on `𝔽_q`.
- `eval_modByMonic_X_pow_card_sub_X`, `degree_modByMonic_lt_card` — reducing modulo `X ^ q - X`
  preserves all values and resets the degree to `< q`: Frobenius folds the function space.
- `rat_no_folding_polynomial` — no nonzero `ℚ`-polynomial vanishes at every rational point.
- `evalMap_bijective` — over `𝔽_q`, degree-`< q` polynomials are a **bijection** onto all
  functions `K → K`.
- `rat_indicator_not_polynomial` — over `ℚ` this fails: the indicator of `{0}` is not a polynomial.

## The curve step and the point bound (`Curve.lean`, `StepanovBound.lean`)

For `y ^ 2 = f(x)`, auxiliary polynomial `A + y B`, conjugate norm `Q = A ^ 2 - f B ^ 2`:

- `conjugate_vanishes` — vanishing of `A + y B` at a curve point forces `Q(x) = 0`.
- `both_branches_vanish`, `two_fibre_double_vanishing`, `two_fibre_card_le` — in odd characteristic
  a full fibre forces **double** vanishing: `2 * |S| ≤ natDegree Q`.
- `fibre_card_le_two` — every fibre has at most two points.
- `stepanov_point_bound` — assembled: `2 * |S| ≤ max (2 deg A) (deg f + 2 deg B)`.

## Why `√q` does not come out of the elementary layer (`Bound.lean`, `Obstruction.lean`)

- `sqrt_of_balanced` — the arithmetic source of `√`: if `N ≤ A·t + B/t` for **all** `t > 0`, then
  `N ≤ 2√(A·B)` (AM–GM).
- `stepanov_inequalities_scale_invariant` — **proved negative result.** The elementary
  inequalities (`m*N ≤ D` and `m*N ≤ max (2a) (n+2b)`) are satisfiable for every `N`; they bound
  nothing, so parameter tuning alone cannot produce `√q`.
- `frobenius_conj` — `y^q = y·(y²)^((q−1)/2)`: the genuine extra input a correct function-field
  argument feeds in, with no `ℚ` analogue.
- `folding_dichotomy` — the sharp statement: `𝔽_q` has a nonzero polynomial vanishing everywhere,
  `ℚ` does not.
- `elementary_chain_no_bound` — the elementary chain imposes no bound on the number of points.

## The reduction, and the open step (`Strategy.lean`)

- `AuxiliaryData` / `auxiliaryData_impossible` — data with vanishing order `≥ k` on `S` but degree
  budget `deg p < k·|S|` is contradictory.
- `RH_of_stepanov_certificates` — **if** every off-critical-line zero of `ζ` admits such data,
  **then** `RiemannHypothesis` holds.

The hypothesis here is exactly what the automorphic proof supplies by other means (chained theta
lifts, GGP periods, Galois cohomology); the elementary layer cannot supply it
(`folding_dichotomy`, `elementary_chain_no_bound`). This file states the reduction precisely so the
gap is a named proposition, not a `sorry`.

## Layout

```
LeanRiemann/Stepanov.lean       Stepanov engine, dimension count, determinant counting, theta chain
LeanRiemann/Folding.lean        Frobenius folding over 𝔽_q, and its failure over ℚ
LeanRiemann/FunctionSpace.lean  Evaluation is a bijection over 𝔽_q, not over ℚ
LeanRiemann/Jets.lean           Hasse jets, multiplicity, existence of the auxiliary polynomial
LeanRiemann/Curve.lean          Stepanov step on y² = f(x): conjugate norm, double vanishing
LeanRiemann/StepanovBound.lean  Assembled point bound and fibre bounds
LeanRiemann/Bound.lean          √-balancing lemma, scale-invariance obstruction, Frobenius conjugation
LeanRiemann/Strategy.lean       Reduction of RH to a Stepanov certificate (the open step, isolated)
LeanRiemann/Obstruction.lean    The three elementary obstructions, gathered in one place
```

## References

- L. Alpöge, announcement and Lean archive, <https://alpo.ge/remark.pdf> (2026-11-20).
- Community verification: <https://github.com/leanprover-community/riemann-hypothesis>.
- R. Zhang, *A preliminary note on Alpöge's proposed proof of GRH*,
  <https://www.ihes.fr/~rzhang/files/GRH%20note.pdf> (2026-11-22).
- E. Bombieri, *Counting points on curves over finite fields* (Stepanov's method).
- M. Fried, M. Jarden, *Field Arithmetic*, Ch. 4 (RH for function fields).
