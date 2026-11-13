This draft gives complete source-proof candidates for two existing open children.
The parent theorem signatures are unchanged. No new open child theorem is added.

The four Lean files contain no `sorry` or new axiom declaration.
The candidates were not compiled or read back after writing.
The main workspace remains unchanged. Only the main agent can submit MCP-CI checks.

The source is Belyi/CurveField/Riemann.lean at:
`9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8`.
All files preserve the Apache 2.0 notice and state the source pin.
No Belyi runtime import is added.

The approximation definition adapts Riemann.lean:54-158.
It uses the actual minimal polynomial of the actual residue at each regular place.
At a pole, the existing polar divisor already contains the place.
Natural induction handles each positive multiplicity. Finsupp induction handles the actual integer divisor.
The constructed output is an actual nonzero rational function and an actual pointwise divisor inequality.

One helper transports the existing `Place.ord_div` law to `functionDivisor`.
Its source is Divisor.lean's `div_div` theorem.
This helper is proved directly. It introduces no mathematical assumption.

The basis definition adapts the source proof inside Riemann.lean:164-213.
It uses the existing `functionBasis M`, which is the actual `Module.finBasis` over ℚ(M.u).
Its correction divisor is the existing actual sum `basisPoleCorrection`.
The actual functions M.u^k*b_i lie in the target Riemann–Roch space.
The actual polynomial monomial basis gives independence of powers by injective polynomial evaluation.
The scalar-tower independence theorem then gives independence of M.u^k*b_i over ℚ.
The unchanged `hFinite` parameter supplies finiteness for the actual target space.
The dimension comparison counts exactly `(l+1)*N`, by the existing `Model.degree_u`.

These two definitions do not depend on the fiber-degree draft.
They add no cycle with the finite-dimensionality theorem.
The parent eventual-linearity proof supplies its existing finite-dimensionality result to the unchanged basis theorem.

All statements concern the existing Model, Place, normalized ord, function divisors, and Riemann–Roch spaces.
Every divisor inequality quantifies over all proper places, including places at infinity.
The source's nonconstant hypothesis remains the existing `Model.transcendental_u`.
The constant field can be larger than ℚ. No constant-field equality is assumed.

Integrate both Definitions files before the two theorem replacements.
Then update the required import audit, if necessary.
Run MCP-CI leaf checks and the required Checks/Axioms, ImportAudit, Act1Scene1, and AxiomAudit gates.
Inspect the actual axiom output. Run `git diff --check`.

`source-consumer.json` records each producer, its source, and its actual consumers.
It also records the unchanged signatures, preserved conditions, integration order, and uncompiled status.
