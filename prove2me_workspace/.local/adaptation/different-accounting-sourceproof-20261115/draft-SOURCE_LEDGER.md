# Source ledger: different accounting

Source: `Heights/Different/NumberField.lean` at `721496ca4c158e511d25d8ccf6bfe8503eda73c1`.
Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`. Lean: `v4.33.1`.
The `reference/NumberField.lean` file preserves the complete source as evidence.
Only the declarations listed below enter the proposed import graph.

| Producer | Source lines | Fidelity and actual consumer |
| --- | --- | --- |
| `differentIdeal_ne_bot'` | 43 | Same theorem and proof. Used by the filtered sum, grouped identity, and finite support. |
| `primeSupport`, `mem_primeSupport` | 114-120 | Same finite set and membership proof. Used by local norm decomposition, the filtered sum, grouped identity, and finite support. |
| `log_absNorm_eq_finsum` | 123-148 | Same factorization and logarithm proof. Uses existing Mathlib facts in place of two source aliases. Consumed by the grouped identity. |
| `diffTerm` | 186-188 | Same actual relative-different summand with denominator `[L:ℚ]`. Used by the filtered sum and grouped identity. |
| `diffContrib_eq_sum_filter` | 192-222 | Same nonzero-summand bijection. Uses the existing carriers and Mathlib `multiplicity_eq_zero` directly. Used by the grouped identity and finite support. |
| `log_absNorm_differentIdeal_div_eq_finsum` | 228-252 | Same grouped local identity. Consumed by the second conjunct of the actual-field theorem. |
| `diffContrib_support_finite` | 256-269 | Same support containment in the image of the different's prime support. Consumed by the first conjunct of the actual-field theorem. |
| `belyiActualFieldDifferentAccounting` | Project carrier; source conclusions at 228 and 256 | Installs the exact existing image-field inclusion. Returns both source conclusions for the actual fields. Used by the unchanged conductor-extension composer. |

The source aliases replaced by Mathlib facts are:

- `multiplicity_eq_zero_of_not_dvd h` becomes `multiplicity_eq_zero.mpr h`.
- `one_lt_absNorm P` becomes `NumberField.HeightOneSpectrum.one_lt_absNorm P`.

The proof reuses the existing `primeBelow`, `diffContrib`, and `mem_primesOverFinset_iff'` declarations.
It does not redefine these carriers or change the accounting proposition.
The wrapper keeps the actual fields, inclusion, normalization, and both conjuncts.
No source tower formula, lower bound, upper bound, or unrelated place helper enters this module.

## Existing Mathlib APIs checked before adaptation

| API | Pinned Mathlib path and line | Use |
| --- | --- | --- |
| `Ideal.finite_factors` | `RingTheory/DedekindDomain/Factorization.lean:84` | Finite prime support of a nonzero ideal. |
| `Ideal.finprod_heightOneSpectrum_pow_multiplicity` | `RingTheory/DedekindDomain/Factorization.lean:891` | Exact factorization of a nonzero ideal. |
| `multiplicity_eq_zero` | `RingTheory/Multiplicity.lean:324` | Zero multiplicity outside prime support. |
| `finprod_eq_prod_of_mulSupport_subset` | `Algebra/BigOperators/Finprod.lean:354` | Replace the ideal finprod with a finite product. |
| `NumberField.HeightOneSpectrum.one_lt_absNorm` | `NumberTheory/NumberField/Completion/FinitePlace.lean:120` | Nonzero prime norms for `Real.log_prod`. |
| `Ideal.absNorm` | `RingTheory/Ideal/Norm/AbsNorm.lean:201` | Existing norm homomorphism; `map_prod` and `map_pow` apply directly. |

The targeted search found no existing Mathlib theorem for this grouped logarithmic norm identity.
The draft therefore adapts the source proof using existing ideal factorization.

## Verification state

This unit contains no new axiom, `sorry`, admitted premise, or weaker target.
The generic arithmetic source proofs have complete bodies.
No missing arithmetic step was found during the source review.
No Lean compiler, MCP-CI task, Git command, or external API ran in this subtask.
Compilation and printed axioms remain unverified.
The Checks file prints the four generic arithmetic results and the actual-field wrapper.
The parent must inspect inherited carrier assumptions in the wrapper output.
The separate local-conductor child remains open and can still affect downstream axiom output.

## Ledger update on integration

Replace only the existing accounting row in the previous source ledger.
Change its state from open to the proof closure listed above after MCP-CI acceptance.
Keep the local-conductor child row open until its own source proof passes acceptance.
Do not describe the full conductor extension or parent mathematical obligation as closed by this unit alone.
