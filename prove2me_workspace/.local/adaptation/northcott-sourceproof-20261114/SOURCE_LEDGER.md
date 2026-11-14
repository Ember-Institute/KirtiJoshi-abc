The source revision and content hashes are in `SOURCE_MANIFEST.json`.
The exact local reference file is `refer/iut/Iut/Tripod/Northcott.lean`.
The three substantial estimates now each have a separate Theorems module.
The witness imports all three modules. Definitions import no Theorems.
All listed adaptations preserve the source statements and proofs under the existing concrete carrier.
The only proof tactic change replaces `linarith` with the direct order proof stated in the manifest.

| Candidate declaration | Source declaration or lines | Actual consumer | Fidelity |
| --- | --- | --- | --- |
| `Northcott.norm_embedding_le_mulHeight₁` | same source name, 44-69 | `northcottPolynomialWitness`, estimate of every embedding of n*x | Closed source proof; direct replacement for final additive inequality |
| `Northcott.heightBound` | same source name, 73 | `heightBound_pos`, `mulHeight₁_gen_le`, `coeffBound`, witness, finite quotient composer | Exact formula |
| `Northcott.heightBound_pos` | same source name, 75 | `northcottPolynomialWitness`, conjugate multiplication bound | Exact proof |
| `Northcott.mulHeight₁_gen_le` | same source name, 79-86 | `northcottPolynomialWitness`, actual generator bound | Exact proof and point-height normalization |
| `Northcott.natDegree_minpoly_int_le` | same source name, 90-94 | `northcottPolynomialWitness`, polynomial membership | Exact proof |
| `Northcott.coeffBoundOf` | same source name, 98 | `coeff_minpoly_int_mem_Icc`, `coeffBound` | Exact formula |
| `Northcott.coeff_minpoly_int_mem_Icc` | same source name, 103-123 | `northcottPolynomialWitness`, all coefficient bounds | Exact proof, all embeddings retained |
| `Northcott.eval₂_minpoly_int_algebraMap` | same source name, 128-131 | `northcottPolynomialWitness`, actual n*x root relation | Exact proof, actual field map retained |
| `Northcott.coeffBound` | same source name, 136-137 | `polySet`; witness coefficient bound unfolds to this value | Exact formula |
| `Northcott.polySet` | same source name, 140-141 | both exact child predicates and both proofs; finite quotient composer | Exact degree and all-coefficient conditions |
| `Northcott.FiniteRoots` | universal closure of `finite_roots_polySet`, 150-152 | `northcottFiniteRoots` and finite quotient composer | Exact child type |
| `Northcott.PolynomialWitness` | universal closure of `exists_nat_mem_polySet`, 157-179 | `northcottPolynomialWitness` and finite quotient composer | Exact child type |
| `northcottFiniteRoots` | `finite_roots_polySet`, 150-152 | `boundedDegreeFiniteness` via composer | Source proof applied for each d,H |
| `northcottPolynomialWitness` | `exists_nat_mem_polySet`, 157-179 | `boundedDegreeFiniteness` via composer | Source proof body retained |
| `boundedDegreeFiniteness_of_northcott_children` | `northcottHyp`, 183-199 | `boundedDegreeFiniteness` | Exact source finite-set argument; explicit child inputs |
| `boundedDegreeFiniteness` | existing platform target | existing `Solutions/Sol_TripodStatementII.lean:9`, then `statementII_of_children` | Exact original name and full type; concrete source-backed proof term |

The unused source helper `mem_polySet` adds no needed input and is omitted.
The existing `Def_AbcTripod` supplies `Qbar`, `Pt`, `fieldOf`, `gen`, degree, and canonical height.
Its `deg_eq_finrank` and `deg_mul_htCan` statements match the source proof's expected types by definition.
This ledger records static source fidelity only.
Lean elaboration and axiom output require a later main-agent MCP-CI receipt.
