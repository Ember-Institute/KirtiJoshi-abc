# Three existing order/index children: complete source proof drafts

The four Lean files contain complete proof drafts from pinned Belyi sources.
The draft preserves each existing theorem target byte for byte.
The draft introduces no new mathematical Open node and no additional hypothesis.
Kernel validation remains pending. This subagent ran no compiler or MCP-CI job.

Source commit: `9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8`.
Workspace input HEAD: `fe86dfab501fe261e59c72a99129677a211d6c68`.

| Draft | Complete source proof | Direct consumer |
| --- | --- | --- |
| `Definitions/Def_FermatNoncriticalOrderSource.lean` | `Place.ord_eq_zero_of_residue_ne_zero`; `Place.residue_eq_zero_of_ord_pos` | Regular nondivisible branch; pole reverse-polynomial residue and order |
| `noncriticalPolynomialOrderAtRegularPoint` | `NoncriticalBasic.ord_aeval_eq` | Existing polynomial regular branch; inverse multiple helper |
| `noncriticalPolynomialOrderAtPole` | `NoncriticalElem.ord_aeval_of_notMem` | Existing polynomial pole branch |
| `noncriticalInverseRamification` | `exists_ramIdx_eq_mul_inv`; every index case of `inv_spec` | Existing Möbius inversion step |

The regular proof keeps the complete strong induction on polynomial degree.
The divisible branch factors the actual residue minpoly and uses characteristic-zero separability.
The nondivisible branch uses the actual residue embedding and the source order-zero helper.

The pole proof keeps the source reverse-polynomial argument.
Its positive-order residue helper has an immediate consumer in that proof.
The second Definitions helper therefore serves the pole child, not an unused future branch.

The inverse multiple helper remains private in the inverse theorem file.
It uses the regular-order theorem once, at the actual inverse and actual reverse minpoly.
The inverse unit branch uses the helper twice and copies the source positivity arithmetic.
The other two branches use existing zero/pole index formulas through `ord_eq_placeOrd`.

Each proof retains the full residue field and every `QbarPoint` embedding.
No proof substitutes rational residue values, a primitive element, or a selected point.
The existing elementary and list-composition tower remains the downstream consumer.

`source-consumer.json` records source spans, source hashes, adaptations, and all producer consumers.
`static-review.json` records exact target hashes and the local import closure.
`SHA256SUMS` records all deliverable file hashes except its own hash.

The local import check found no `CurveDeriv`, Act2, Scene2, Prologue, or Obligations import.
The new Definitions module imports no theorem module.
All four Lean drafts contain no `sorry`, `admit`, `axiom`, or `unsafe` declaration.
These static checks do not establish Lean elaboration or allowed axiom dependencies.

For integration, add the new Definitions file and replace the three existing theorem files.
Keep their current theorem names and targets.
Check the regular child before the inverse child.
Then validate the existing elementary and composition consumers with the required project audits.
Use MCP-CI for every Lean check.
For a first leaf attempt, use `60s` and `16GiB` as required by AGENTS.md.
Use recorded job history for any later attempt.

All writes stayed in `/tmp/p2m-elementary-order-sourceproof-next-20261114`.
No workspace source, dependency, compiler cache, credential, or external application changed.
