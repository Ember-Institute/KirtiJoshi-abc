# Source ledger

Pinned upstream checkout: `heights-721496ca4c158e511d25d8ccf6bfe8503eda73c1`.
All four original files are copied byte-for-byte under `reference/`; SHA-256 values appear
in `INPUT_MANIFEST.json` and `SHA256SUMS`. The copyright/license headers are retained.
Mathlib pin: `0df444a360eaa60ab8c11dca51a86af692955474`; Lean: `v4.33.1`.

| Producer or obligation | Exact source | Fidelity and actual consumer |
| --- | --- | --- |
| `ConductorExtensionSource.primeBelow`, `diffContrib`, nonnegativity and prime-fiber membership | `NumberField.lean:158–182` | Same comap, `differentIdeal`, multiplicity, `primesOverFinset`, and `[L:ℚ]`. Nonnegativity uses the direct Mathlib `Real.log_natCast_nonneg` rather than a one-line upstream alias. Used by the two child types, restriction adapters and finite-subsum bound. |
| Norm, pole transport and finite-place extension carriers | Dependency-closed subset of `Places.lean:45–220` | Same retained statements and proof bodies in the adaptation namespace; the norm positivity alias is replaced by the exact Mathlib theorem. `PlaceLiesOver` is actual ideal lies-over. `placesOver` is proved finite and converted to a finset. Pole transport and unique restriction are used in `finiteSetLogCond_le_of_local_and_accounting`. The log-norm/degree-counting helpers, inverse prime-to-place construction, and unused restriction equivalences are excluded from the integration file. |
| `meets`, finite support, `meetsFinset`, membership | `Conductor.lean:43–66` | Exact definitions and proofs. Used to express both existing conductors as finite sums and to construct the disjoint union of lifted pole sets. |
| `finiteSetLogCond_eq_sum` | `Conductor.lean:76–87` | Reuses the existing `finiteSetLogCond`, with a definitional change to the source `placeNorm` wrapper. No new conductor definition. Used by the finite-place composer. |
| `BelyiActualFieldLocalConductorComparison` / theorem | `Conductor.lean:104–136` | Exact local inequality restricted to the actual fields/inclusion. Open with `by sorry`; consumed by the actual-field composer. No finite set, conductor, height or arbitrary correction model appears in this child. |
| `BelyiActualFieldDifferentAccounting` / theorem | `NumberField.lean:228–271` | Exact normalized grouped identity AND support finiteness on actual base primes. Open with `by sorry`; both conjuncts are consumed by `sum_diffContrib_le_of_accounting`. |
| `sum_diffContrib_le_of_accounting` | `Conductor.lean:149–165` | Complete source finite-subsum proof, now conditional on the two explicit accounting facts. It adds the finite support to the finite set before replacing `finsum`; it uses actual nonnegative ideal-multiplicity summands. |
| `finiteSetLogCond_le_of_local_and_accounting` | `Conductor.lean:170–195` | Complete source finite-sum proof; local inequality and accounting are explicit premises. All S/T quantifiers, map containment, disjointness, and both normalizing degrees are preserved. |
| `belyiActualFieldConductorExtension_of_local_and_accounting` | Existing actual-field child carrier plus preceding source proof | Installs precisely the original inclusion algebra; applies local/global premises; unfolds only `belyiRelativeLogDifferent` and `QbarPoint.degree`. Returns the unchanged parent proposition. |
| Replacement parent theorem | Existing `belyiActualFieldConductorExtension` | Same name and type, concrete application of the conditional composer. Existing `belyiDifferentConductorComparison_of_exact_children` is its downstream consumer. |

## Lower-only implementation route for the open local child

The full proof of `Conductor.lean:104` is present in `reference/Conductor.lean`.
The present integration file contains only the dependency closure needed by the child statements
and the complete finite-set composer. The later local proof also needs the helpers retained in
`reference/FutureFinitePlaceArithmetic.lean`; that file is outside the integration import graph
and none of its declarations are counted as present consumers:

1. `sum_placesOver_mul_eq_finrank` and `Module.finrank_mul_finrank` distribute the F-normalized
   prime norm among places above it with weights `e*f`.
2. `log_placeNorm_eq` splits each weighted term into `log N(w)` and `(e−1)*f*log N(u)`.
3. `sum_placesOver_eq` changes the lower-error sum to the actual prime-ideal fiber.
4. The needed lower bound is only `Bounds.lean:169–173`, then the weighted sum in
   `Bounds.lean:252–261`. This uses Mathlib `pow_sub_one_dvd_differentIdeal`, not Serre's
   upper bound. Its short support lemmas are `NumberField.lean:80–88` (finite multiplicity and
   powers/divisibility), `Bounds.lean:150–162` (nonzero prime, norm transport, mapped-power
   divisibility), and `Bounds.lean:240–249` (rewrite the contribution using inertia degree).

The draft intentionally leaves this arithmetic child open. Do not import the entire upstream
`Bounds.lean`, since it also imports the unrelated Serre upper-bound development.

## Existing Mathlib definitions and facts checked before adding wrappers

| Existing Mathlib API | Pinned source path | Use |
| --- | --- | --- |
| `FinitePlace.equivHeightOneSpectrum`, `maximalIdeal_injective`, `hasFiniteMulSupport` | `Mathlib/NumberTheory/NumberField/Completion/FinitePlace.lean:403,410,434` | Actual finite places and finite pole support; no replacement place model. |
| `HeightOneSpectrum.valuation_liesOver` | `Mathlib/NumberTheory/RamificationInertia/Valuation.lean:57` | Exact valuation restriction in the completed pole-transport proof. |
| `Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver` | `Mathlib/NumberTheory/RamificationInertia/Inertia.lean:157` | Exact norm transport. |
| `Ideal.sum_ramification_inertia` | `Mathlib/NumberTheory/RamificationInertia/Basic.lean:614` | Future local degree counting, used only in the non-integration reference helper. |
| `Ideal.finite_factors`, `Ideal.finprod_heightOneSpectrum_pow_multiplicity` | `Mathlib/RingTheory/DedekindDomain/Factorization.lean:84,891` | Existing prime support and ideal factorization for the future accounting proof. |
| `pow_sub_one_dvd_differentIdeal` | `Mathlib/RingTheory/DedekindDomain/Different.lean:740` | Existing lower different-exponent bound. |
| `differentIdeal`, `differentIdeal_ne_bot` and the number-field instances | `Mathlib/NumberTheory/NumberField/Discriminant/Different.lean` and its imports | Actual relative different; the original child already imports this module. |

The text search found a separate `placesOver` only for infinite places, not an existing
finite-place fiber wrapper. The adaptation therefore keeps the source's short finite-place
wrappers around Mathlib's existing ideal functions.

## Closed proof dependency closure

The integrated finite-place carrier has these consumer chains:

- `placeNorm → one_lt_placeNorm → log_placeNorm_pos → log_placeNorm_nonneg →` finite-set composer.
- `primeBelow → placeBelow → placeBelow_maximalIdeal → eq_placeBelow →` disjointness in the composer.
- `mem_primesOverFinset_iff' → mem_primesOverFinset_of_placeLiesOver → finite_placeLiesOver → placesOver → mem_placesOver →` the two child statements and the composer.
- `placeRamIdx`/`placeInertiaDeg` and their nonzero lemmas, `finitePlace_apply_eq`, the two `toNNReal` helpers and `placeNorm_eq_pow → apply_algebraMap_eq_pow → one_lt_apply_algebraMap_iff →` containment of the lifted pole set in the composer.
- `diffContrib → diffContrib_nonneg → sum_diffContrib_le_of_accounting →` the composer; the exact contribution also occurs in both child statements.

The removed helpers are `log_placeNorm_eq`, `sum_placesOver_eq`,
`sum_placesOver_mul_eq_finrank`, the three `placeOfPrimeOver` construction lemmas,
`placeLiesOver_iff`, `placeLiesOver_placeBelow`, and `placeLiesOver_iff_eq_placeBelow`.
Their adapted source bodies remain in the non-integration reference file. Ledger prose about
future implementation is not treated as consumption by a proof.

## Scope and axiom accounting

The two arithmetic `by sorry` declarations are the only active open proofs in this draft.
No global field law, height field, new axiom, renamed target or weakened statement is added.
The accounting child exposes the exact ideal expression, so it cannot absorb a conductor
comparison into a freely chosen numerical correction. Expected `sorryAx` propagation is
recorded explicitly in the Checks module. No Lean or axiom audit has run in this subtask.
