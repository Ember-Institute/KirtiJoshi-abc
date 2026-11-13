# Curve-field and Riemann candidate

This directory contains an uncompiled Act1 candidate. It changes no main workspace file.
No compiler, MCP-CI job, or read-back step ran.

The fixed reference is Belyi commit `9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8`.
The `reference/` directory contains the exact downloaded files. The machine ledger records their SHA-256 hashes.

The source class has exactly one field:

```lean
class IsCurveField (K : Type*) [Field K] [CharZero K] : Prop where
  exists_finite : ∃ t : K, Transcendental ℚ t ∧ FiniteDimensional ℚ⟮t⟯ K
```

`Def_FermatCurveFieldBasic.lean` preserves this type and the source proofs for its basic consequences.
`Model.isCurveField` closes its only field with `(M.u, M.transcendental_u, M.finite_u)`.
`Model.fg_top` proves field finite generation from the actual two-element set `{M.u, M.v}`.
This is `IntermediateField.FG`, not `Algebra.FiniteType ℚ M.K`.
The rational function field is not a finite type algebra over `ℚ`.

The source class does not require the constant field to equal `ℚ`.
It does not require a separate geometric integrality field.
These conditions do not enter the source proofs below, so this candidate adds no such obligation.
In particular, it never replaces the dimension of the constant field by `1`.

The candidate ports the following concrete chain:

| File | Concrete object or proof | Source use |
| --- | --- | --- |
| `Def_FermatCurveFieldBasic` | The source class and its exact Model witness | `Basic.lean` |
| `Def_FermatCurveFieldChart` | Integral closure of `ℚ[t]` inside the actual field | `Chart.lean` |
| `Def_FermatCurveFieldPlace` | Chart primes, Dedekind localizations, normalized valuations | `Place.lean` |
| `Def_FermatCurveFieldResidue` | Actual residue-field finiteness and Model adapters | `Residue.lean` |
| `Def_FermatCurveFieldZerosPoles` | Existence and finite support of actual zeros and poles | `ZerosPoles.lean` |
| `Def_FermatRiemannSpaces` | The actual `L(A)` subspace, its dimension, and divisor arithmetic | `RiemannRochSpace.lean` |
| `Def_FermatRiemannComposition` | Exact polar realization and positive-part construction | `Riemann.lean` |

The chart ring is `integralClosure (Algebra.adjoin ℚ {t}) K`.
For transcendental `t`, its base ring is isomorphic to `ℚ[X]`.
The source proves that the chart ring is Dedekind, finite over `ℚ[t]`, and of finite type over `ℚ`.
Its fraction field is the actual `K`.
These are proved instances, not new fields of a freely supplied chart structure.

Every proper valuation ring contains a transcendental coordinate `t` or its inverse.
It equals a localization of that chart ring at the prime below it.
Dedekind localization gives the DVR instance.
The chart residue map is surjective onto the existing proper residue field.
The finite type quotient is then finite over `ℚ` by Zariski's lemma.

The existing proper carriers are reused:

- `Place K` remains the existing subtype of actual valuation subrings.
- `Place.ResidueField` remains the existing local-ring residue field.
- `ord_eq_placeOrd` identifies the existing explicit `hDVR` order with the source order by proof irrelevance.
- No new place, residue field, or order is supplied as arbitrary data.

Two files are candidate replacements for existing open leaves:

```
Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_placesDiscrete.lean
Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_residuesFinite.lean
```

Their original signatures stay intact. Their proof bodies call `model_placesDiscrete` and `model_residuesFinite`.
No `sorry` occurs in these replacements or in their definition dependencies.
They are proof candidates until the main agent runs MCP-CI.

For the next Riemann layer, the candidate defines the actual subspace

```
L(A) = { f : M.K | f = 0 or forall P, -A(P) <= ord_P(f) }
ell(A) = Module.finrank Rat L(A)
```

The separate zero branch is necessary because the normalized source order has `ord(0)=0`.
The submodule proof uses the source valuation sum, multiplication, and rational-constant laws.
The finite positive part is `max(A(P),0)` at each actual proper place.

Three explicit open children remain:

| Child | Exact content | Source proof |
| --- | --- | --- |
| `riemannRochFiniteDimensional` | `FiniteDimensional ℚ L(A)` for every actual divisor | `RiemannRochSpace.lean:283` |
| `riemannRochDimensionUpperBound` | `ell(A) <= max(0, degree(A)+ell(0))` | `RiemannRochSpace.lean:330` |
| `riemannRochEventuallyLinear` | `ell(A)=degree(A)-g0` for all sufficiently large degrees | `Riemann.lean:280` |

Each child has a full platform module name under `Theorems/`.
Definitions import none of these open children.
The three propositions refer to actual subspaces and their actual dimensions.
They contain no height theory, free dimension function, or genus label.

`largeEffectivePolarRealization_of_riemannChildren` adapts the source proof from those children.
It makes every `L(A-P)` a proper subspace of `L(A)` when `degree(A)` is large.
A finite union of proper subspaces cannot cover a rational vector space.
A function outside that union has exactly the prescribed polar divisor.
The dimension argument takes actual finite-dimensionality proofs before it compares finite ranks.

`polarPresentation_of_largeEffectivePolarRealization` then adapts the source positive-part proof.
It picks an actual place `P0`, with positive degree from its actual finite residue field.
It constructs `E = max(N1,0) * P0` with enough degree.
It realizes `positivePart(D)+E` and `positivePart(-D)+E` as the polar divisors of actual functions `f,g`.
Subtracting their coefficients produces the exact existing `PolarPresentation M hDVR D`.

The candidate replacement for `polarPresentationExists` keeps its original signature.
Its body consumes the three dimension children through that proof chain.
The former residue-finiteness parameter stays in the signature; the fixed Model now proves that fact directly.
This is an actual construction of the required functions, rather than a renamed copy of the parent assertion.

The next proof costs are concrete and source-backed:

- Finite-dimensionality needs the residue map `L(A+P) -> κ(P)`, its exact kernel, and principal degree zero.
- The dimension upper bound needs one-place induction and invariance under multiplication by a nonzero rational function.
- Eventual linearity needs a finite basis over `ℚ(u)` and independence of the actual functions `u^k*b_i`.
- It also needs finite polar divisors, principal degree zero, and reduction to multiples of the polar divisor of `u`.
- The source then uses the bounded integer set `{degree(A)-ell(A)}` and its attained maximum.

The pinned proofs for these steps remain in `reference/`.
This candidate does not claim to port them already.
It does not add a Fermat constant-field theorem, geometric integrality assumption, or Act2 input.
