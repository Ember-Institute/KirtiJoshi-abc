This draft gives a complete source-proof candidate for `Proper.functionZeroPoleDegrees`.
It adds no open child theorem. It preserves the parent theorem's exact type.

The three Lean files contain no `sorry` or new axiom declaration.
They were not compiled. Only the main agent can submit the integration to MCP-CI.

The source is pinned at `9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8`.
Each file preserves the Apache 2.0 notice and adds the source pin.
The files import local Definitions and pinned Mathlib modules. They do not import Belyi.

The candidate reuses the existing Model, chartRing, Place, residue field, normalized ord, and divisors.
In particular, `chartRing t` remains the actual integral closure of ℚ[t] in the function field.

The proof has this chain:

1. Normalize the actual prime-adic valuation against the existing Place.ord.
2. Identify the actual chart residue quotient with the existing Place.ResidueField.
3. Identify primes over the coordinate ideal `(t)` with all places where `ord(t)>0`.
4. Identify actual ramification indices with normalized orders.
5. Identify actual inertia degrees with residue degrees over ℚ.
6. Apply Mathlib's actual `Ideal.sum_ramification_inertia` identity.
7. Transfer the finite sum to the existing zero divisor.
8. Apply the zero result to `t⁻¹` for the pole divisor.

The last step includes all places over infinity. No affine restriction remains in the theorem.
The nonconstant hypothesis remains `Transcendental ℚ f`.
The constant field can be larger than ℚ. Every residue degree is still taken over ℚ.
No free degree, ramification number, residue degree, or proposition parameter is added.

`Def_FermatCurveFieldDegree.lean` mechanically adapts the complete Degree.lean proof body.
Its changes are the namespace, local imports, and `Place.deg` to `Place.degree`.
The header adds provenance and explicitly sets `autoImplicit false`.
A Python comparison confirmed exact proof-body equality after these identifier changes.

`Def_FermatFunctionFiberDegrees.lean` adapts Divisor.lean:85-87 and 190-213.
It expands the actual finitely supported degrees, using `ord_eq_placeOrd` at the existing model boundary.
The replacement theorem joins the two resulting identities.

Integrate in this order:

1. Add `Definitions/Def_FermatCurveFieldDegree.lean`.
2. Add `Definitions/Def_FermatFunctionFiberDegrees.lean`.
3. Replace `Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_functionZeroPoleDegrees.lean`.
4. Add the new Definitions imports to the repository's required import audit, if needed.
5. Run MCP-CI leaf checks and the required Checks/Axioms, ImportAudit, Act1Scene1, and AxiomAudit gates.
6. Read actual axiom output and run `git diff --check`.

The pinned Mathlib exposes the same ramification and inertia interfaces as the source.
The NumberTheory API has deprecation notices. This draft retains it to keep the source proof unchanged.

`source-consumer.json` records each producer, its exact source, and its actual consumers.
It also records source hashes, integration order, preserved conditions, and the uncompiled status.
