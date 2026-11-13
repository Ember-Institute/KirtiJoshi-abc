# Elementary composition: three actual source boundaries

This task-only draft replaces the one Open `noncriticalElementaryCompositionRamification` node with three smaller mathematical leaves and the pinned source assembly. The original parent target type is copied exactly, including its actual field, full algebraic points and embeddings, transcendence, actual values, and actual ramification product. No repository/cache edit, compiler, MCP-CI submission, network request, or publication was performed.

Pinned source: Belyi `9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8`. Reference copies come from the parent draft and the earlier pinned elementary-map copy; hashes are in `source-consumer.json`.

## Open mathematical leaves

1. `noncriticalPolynomialOrderAtRegularPoint`: source `NoncriticalBasic.ord_aeval_eq`. For every regular transcendental function and nonzero rational polynomial, the actual normalized order is the actual ramification index times root multiplicity at the actual residue embedding.
2. `noncriticalPolynomialOrderAtPole`: source `NoncriticalElem.ord_aeval_of_notMem`. At every pole, the actual normalized order of a polynomial evaluation is its degree times the order of the function.
3. `noncriticalInverseRamification`: the precise second conjunct of source `NoncriticalElem.inv_spec`: the actual ramification indices of the function and its inverse agree. All zero, unit, and pole cases remain inside this exact child.

These have `sorry`. No arbitrary map, law record, selected embedding, hidden global input, or additional mathematical assumption replaces the source statements. `letI M.isCurveField` in the order targets selects the existing canonical order instance and adds no hypothesis.

## Source proof assembly

`Definitions/Def_FermatNoncriticalElementarySource.lean` contains source point-evaluation helpers, the actual elementary-map computation lemmas, separable-composition root multiplicity, polynomial transcendence, degree-one unramifiedness, affine and inverse Möbius decompositions, and the value proof for inversion.

The inversion helper `inv_spec_of_ramIdx` takes the **exact actual inverse-index equality** as its explicit child premise. Its value proof is projected from source `inv_spec`, with all three order cases retained. This makes it possible to keep Definitions free of Open theorem imports. It has an immediate actual consumer: the non-affine branch of `mob_spec` supplies `noncriticalInverseRamification` for the genuine affine intermediate function.

The existing zero-evaluation producer now has a real source consumer: `noncritical_eval_zero` is used in the zero-function branch of `noncritical_eval_inv`; that helper is used in the unit branch of `inv_spec_of_ramIdx`; that result is used in `mob_spec`; `mob_spec` is used in the parent constructor split. No dummy call or unused helper is added.

The replacement parent theorem module contains source `poly_spec`, source `mob_spec`, and source `applyK_spec` constructor assembly. Regular polynomial ramification uses the actual full residue-field minimal polynomial and the copied separable-composition multiplicity theorem. Pole ramification uses the pole-order child. Möbius transformations are handled in both `c = 0` and `c ≠ 0` branches; the latter is the genuine affine/inverse/affine composition. Every intermediate function retains the source transcendence proof.

## Integration and validation

The draft depends on `Definitions.Def_FermatNoncriticalRamificationPositive` from `/tmp/p2m-noncritical-composition-next-20261114`. Integrate that previous completed source candidate first, then this Definitions candidate, the three Open leaf modules, and the replacement elementary parent. The existing list-composition parent can keep consuming its unchanged type.

Only exact Mathlib modules are imported; no runtime Belyi source, full Mathlib import, derivative carrier, Scene2, Act2, Prologue or Obligations module is introduced. The polynomial derivative module is used solely by the source degree-one root-multiplicity calculation.

`static-review.json` records textual target equality, three Open leaves, no `sorry` or Theorems import in Definitions, source-consumer links, and file hashes. These are static checks. No compilation, kernel validation, axiom audit, memory or timing result is claimed. The main agent must validate via MCP-CI and complete its normal acceptance checks.
