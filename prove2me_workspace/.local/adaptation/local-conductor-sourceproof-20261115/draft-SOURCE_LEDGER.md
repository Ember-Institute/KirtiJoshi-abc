# Source ledger: lower-only local conductor proof

Pinned source: `heights-721496ca4c158e511d25d8ccf6bfe8503eda73c1`.
Pinned platform Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
Lean toolchain inherited read-only from the project: `leanprover/lean4:v4.33.1`.
Full original proof files are preserved under `reference/` and excluded from the import graph.
Their hashes, archive hashes and baseline hashes are recorded in `INPUT_MANIFEST.json`.

Every producer below has a concrete proof consumer. A future route description, theorem name
or `#print axioms` invocation is not treated as consumption.

| New producer | Exact pinned source | Fidelity/change | Actual statement/proof consumer |
| --- | --- | --- | --- |
| `finiteMultiplicity_of_isPrime` | `NumberField.lean:80–82` | Exact statement and proof; namespace changed only | `pow_dvd_iff_le_multiplicity` |
| `pow_dvd_iff_le_multiplicity` | `NumberField.lean:85–88` | Exact statement and proof | `ramificationIdx'_sub_one_le_multiplicity` |
| `ne_bot_of_liesOver` | `Bounds.lean:150` | Exact one-line Mathlib specialization | `ramificationIdx'_sub_one_le_multiplicity` |
| `log_absNorm_eq_inertiaDeg_mul` | `Bounds.lean:154–157` | Exact proof of the actual ideal norm relation | `diffContrib_eq` |
| `pow_ramificationIdx'_dvd` | `Bounds.lean:160–162` | Exact actual mapped-prime-power divisibility | `ramificationIdx'_sub_one_le_multiplicity` |
| `ramificationIdx'_sub_one_le_multiplicity` | `Bounds.lean:169–173` | Exact lower bound, with the source's local FractionRing algebra instances | `sum_le_diffContrib` |
| `diffContrib_eq` | `Bounds.lean:243–249` | Exact statement and proof; unfolds the existing actual contribution | `sum_le_diffContrib` |
| `sum_le_diffContrib` | `Bounds.lean:252–261` | Same normalized lower inequality and proof. The source `log_absNorm_nonneg` alias is replaced by the exact Mathlib `Real.log_natCast_nonneg` theorem | `log_placeNorm_div_le` |
| `log_placeNorm_eq` | `Places.lean:126–128` | Exact source log-norm transport; now genuinely activated | `log_placeNorm_div_le` |
| `placeOfPrimeOver` | `Places.lean:181–187` | Exact construction using the actual prime ideal and lies-over proof | `placeOfPrimeOver_maximalIdeal`, `placeLiesOver_placeOfPrimeOver`, `sum_placesOver_eq` |
| `placeOfPrimeOver_maximalIdeal` | `Places.lean:189–193` | Exact source proof | `placeLiesOver_placeOfPrimeOver`, `sum_placesOver_eq` |
| `placeLiesOver_placeOfPrimeOver` | `Places.lean:222–228` | Exact source proof | `sum_placesOver_eq` |
| `sum_placesOver_eq` | `Places.lean:232–243` | Exact bijection proof, using existing finite-place carriers | `sum_placesOver_mul_eq_finrank`, `log_placeNorm_div_le` |
| `sum_placesOver_mul_eq_finrank` | `Places.lean:246–251` | Exact source proof of `∑e*f=[L:F]` | `log_placeNorm_div_le` |
| `finrank_ℚ_pos` | `Bounds.lean:239–240` | Exact source positivity proof | `log_placeNorm_div_le` |
| `log_placeNorm_div_le` | `Conductor.lean:104–136` | Complete source proof unchanged except surrounding imports/namespace | `belyiActualFieldLocalConductorComparison` |
| `belyiActualFieldLocalConductorComparison` | Existing exact child proposition plus `Conductor.lean:104` | Concrete wrapper installs the exact prescribed inclusion and applies the complete local theorem. Original theorem name/type retained | Existing `belyiActualFieldConductorExtension` composition unit |

The four source modules contain only this active dependency closure. The old
`placeLiesOver_iff`, `placeLiesOver_placeBelow`, and
`placeLiesOver_iff_eq_placeBelow` helpers are not copied into the new integration.
No upstream `Bounds`, `SerreBound`, `Places` or `Conductor` module is imported.
The complete `Bounds.lean` file is retained only as a reference witness.

## Mathematical proof chain

At an actual base prime `𝔭` and each prime `P` above it, actual mapped-prime-power
factorization gives `P^e ∣ map(𝔭)`. Mathlib's `pow_sub_one_dvd_differentIdeal` then gives
`P^(e−1) ∣ 𝔇`. Nonzero prime and different ideals make prime multiplicity finite, so
`e−1 ≤ multiplicity P 𝔇`. This is the lower bound only; no tame/wild equality or Serre
upper bound is used.

The norm identity `N(P)=N(𝔭)^f` rewrites the existing `diffContrib` as a sum of
`ord_P(𝔇)*f*log N(𝔭)/[L:ℚ]`. Each weight is nonnegative. The pointwise lower bound
therefore yields the full weighted lower contribution inequality.

The finite-place/prime-ideal bijection transports that sum to the actual places over `u`.
The fundamental degree relation `∑e*f=[L:F]` and the rational degree tower identity rewrite
`log N(u)/[F:ℚ]` as the weighted sum on L. Split `e = 1+(e−1)`, replace the inertia-weighted
logarithm by `log N(w)`, and bound the remaining lower error by `diffContrib`. This is the
complete local inequality with the original denominators and correction.

## Checked Mathlib API witnesses

| API | Pinned file and line | Required role |
| --- | --- | --- |
| `FiniteMultiplicity.of_prime_left` | `Mathlib/RingTheory/UniqueFactorizationDomain/Multiplicity.lean:49` | Finite multiplicity from a nonzero prime in a well-founded divisibility monoid |
| `FiniteMultiplicity.pow_dvd_iff_le_multiplicity` | `Mathlib/RingTheory/Multiplicity.lean:262` | Prime-power divisibility conversion |
| `Ideal.ne_bot_of_liesOver_of_ne_bot` | `Mathlib/RingTheory/Ideal/Over.lean:270` | Nonzero prime above a nonzero base prime |
| `Ideal.le_pow_ramificationIdx'` | `Mathlib/NumberTheory/RamificationInertia/Ramification.lean:145` | Mapped prime lies in the e-th prime power |
| `pow_sub_one_dvd_differentIdeal` | `Mathlib/RingTheory/DedekindDomain/Different.lean:740–748` | Exactly `P^(e−1) ∣ differentIdeal A B` |
| `differentIdeal_ne_bot` | `Mathlib/RingTheory/DedekindDomain/Different.lean:540` | The different is nonzero for the number-field extension |
| `FractionRing.liftAlgebra`, `FractionRing.isScalarTower_liftAlgebra` | `Mathlib/RingTheory/Localization/FractionRing.lean:752,758` | Source-local fraction-ring algebra/compatibility instances for the lower bound |
| `Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver` | `Mathlib/NumberTheory/RamificationInertia/Inertia.lean:157–161` | Exact norm/inertia relation |
| `Ideal.sum_ramification_inertia` | `Mathlib/NumberTheory/RamificationInertia/Basic.lean:614` | Exact existing source sum over `primesOverFinset` equals field degree |
| `FinitePlace.maximalIdeal_mk`, `maximalIdeal_inj` | `Mathlib/NumberTheory/NumberField/Completion/FinitePlace.lean` | Existing inverse finite-place construction and injection |

The source's `Ideal.sum_ramification_inertia` symbol is still present in this pinned
Mathlib, with a deprecation attribute. This draft preserves that exact supported proof
route rather than adding an unrelated migration to the newer prime-spectrum API. It adds
no deprecation to any project declaration.

No missing API was found in this static source comparison. Elaborator instance synthesis,
proof checking, resource use and axiom output remain unmeasured until the main agent runs
MCP-CI. This draft makes no compilation or completed-axiom-audit claim.

## Existing exact inputs

The carrier remains the accepted/reviewed finite-place carrier of the two-child split:
`diffContrib`, `placeNorm`, `placeRamIdx`, `placeInertiaDeg`, finite `placesOver`, and their
closed structural facts. The child proposition remains byte-identical to its main-workspace
baseline at drafting time. No field, number-field structure, algebra, geometric datum or
height assumption is supplied freely by the new theorem wrapper.
