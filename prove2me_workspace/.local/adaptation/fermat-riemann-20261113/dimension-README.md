# Riemann dimension decomposition

This directory contains an uncompiled Act1 candidate.
It depends on the definitions in `/tmp/p2m-fermat-riemann-next-design-20261113/`.
No compiler, MCP-CI job, main workspace edit, or read-back step ran.
The fixed Belyi revision is `9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8`.
The machine ledger records source hashes and actual consumers.

The candidate replaces the three previous dimension leaves with proof compositions.
It leaves three new, mathematically distinct open children:

| Open child | Exact mathematical content | Source |
| --- | --- | --- |
| `functionZeroPoleDegrees` | Both fibers of a nonconstant function have degree `[K:ℚ(f)]` | `Degree.lean:248,308`; `Divisor.lean:190-213` |
| `riemannPolarApproximation` | For each divisor A, an actual z≠0 and l satisfy `A+div(z)≤l*(u)∞` | `Riemann.lean:94-158` |
| `riemannBasisPowerLowerBound` | `dim L(l*(u)∞+C)≥(l+1)*N` for the actual basis pole correction C | `Riemann.lean:169-223` |

All three types use the actual function field, normalized orders, residue degrees, divisors, and vector spaces.
There is no freely specified dimension function or abstract law field.
The last child receives actual finite-dimensionality proofs explicitly.
Its caller obtains them from the first child, so the dependency graph has no cycle.

`functionZeroDivisor`, `functionPoleDivisor`, and `functionDivisor` are genuine finite divisors.
Their coefficients are `max(0,ord_P f)`, `max(0,-ord_P f)`, and `ord_P f`.
Finite support follows from the already ported zero/pole theorem.
They preserve the source convention `div(0)=0`.
`functionDivisor_eq_zero_sub_pole` proves the exact coefficient identity.
The first open child therefore gives principal degree zero by subtraction.
For constants, the proof uses their actual zero order at every place.
It does not assume that all constants are rational.

The remaining local work is a complete source proof adaptation, not a new open child.
`Def_FermatRiemannLocalDimension.lean` defines the actual linear map

```
residueMap A P π : L(A+P) -> κ(P)
f |-> residue_P(π^(A(P)+1)*f),     ord_P(π)=1.
```

The file proves that every scaled function belongs to the actual valuation ring.
It proves linearity over ℚ using the actual residue homomorphism.
It proves

```
f belongs to kernel(residueMap A P π) <-> f belongs to L(A).
```

Thus its kernel is the image of `L(A)` inside `L(A+P)`.
The existing finite residue field gives the one-place estimate

```
FiniteDimensional ℚ L(A) ->
FiniteDimensional ℚ L(A+P) and ell(A+P) <= ell(A)+degree(P).
```

The proof uses the actual kernel equivalence and rank-nullity.
It does not replace the residue map by a free linear map or an exactness assumption.
Explicit local instances retain finite-dimensionality during the induction.

The first parent follows from principal degree zero:

1. If `degree(A)<0`, then a nonzero element of `L(A)` would make `A+div(f)` effective.
2. Its nonnegative degree contradicts principal degree zero.
3. Choose an actual place P0 and enough copies of P0 to make the degree negative.
4. Add those copies back with the proved one-place estimate.

This gives `riemannRochFiniteDimensional` with a proof body that contains no `sorry`.
The word “actual” here refers to the proper valuative place carrier.
It does not refer to an archimedean real place.

For the second parent, the file defines multiplication by z as an explicit linear equivalence

```
L(A+div(z)) ≃ₗ[ℚ] L(A),       z≠0.
```

It uses multiplication by `z⁻¹` as the inverse.
A nonzero element of `L(A)` makes `A+div(z)` effective.
The effective-divisor dimension estimate and principal degree zero then prove

```
ell(A) <= max(0, degree(A)+ell(0)).
```

The value `ell(0)` is the actual constant-space dimension.
It is never replaced by 1.
The replacement `riemannRochDimensionUpperBound` also contains no `sorry`.

For the third parent, define the actual basis

```
b = Module.finBasis ℚ(u) M.K
C = sum_i functionPoleDivisor(b_i).
```

`Model.finite_u` supplies the finite extension, and `Model.degree_u` gives its dimension N.
The source proves membership and independence of the functions `u^k*b_i` for `0≤k≤l`.
That proof remains the third open child.
The first child also gives `degree((u)∞)=N`.
The one-place estimate then bounds `degree(l*(u)∞)-ell(l*(u)∞)` uniformly in l.
The approximation child transfers this bound to every actual divisor.

`Def_FermatRiemannDimensionComposition.lean` defines the integer supremum of the actual defects

```
sSup {degree(A)-ell(A) | A is an actual divisor}.
```

The proof establishes boundedness from the preceding inputs.
The integer supremum is attained by an actual divisor A0.
The source argument then proves eventual equality from that maximum.
The replacement `riemannRochEventuallyLinear` contains no `sorry`.
It consumes the three new open children through this proof.

The candidate has three definition modules and six theorem modules.
The three replacement modules keep the previous platform theorem names and signatures.
The other three modules use full platform names for the new open children.
Definitions import no theorem modules.
The only three `sorry` terms occur in the three new open leaves.

The exact remaining proof costs are:

- Fiber degrees: the integral-closure prime decomposition and the actual ramification/residue-degree sum.
- Approximation: the minimal polynomial of the actual residue of u at regular places, followed by divisor induction.
- Basis bound: order bounds for `u^k*b_i`, polynomial monomial independence, and the finite-rank lower bound.

The source files for all these steps are in `reference/`.
These are concrete proof tasks from the fixed source, not restatements of any dimension parent.
The kernel, principal-degree consequence, finite-dimensional induction, multiplication equivalence, and integer-supremum composition are already written as candidate proof bodies.

The old draft now says “an actual place” in its proof comment, README, and machine ledger.
`Model.fg_top` from that draft currently has no consumer in this chain and can be omitted.
The actual curve-field witness uses `M.u`, `M.transcendental_u`, and `M.finite_u` directly.
Neither this draft nor its source requires an extra constant-field or geometric-integrality hypothesis.
No Act2 statement occurs here.
