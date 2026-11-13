# Noncritical Belyi next layer

This directory contains an uncompiled Act1 candidate.
It reads the current proper carrier and local Belyi definitions without changing them.
It depends on the two Riemann drafts that the main agent is integrating.
No compiler, MCP-CI job, main workspace edit, or read-back step ran.

The fixed Belyi source revision is `9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8`.
It matches the Belyi dependency in `refer/iut/lake-manifest.json`.
The machine ledger records the reference files and their SHA-256 hashes.

`cuspsFinite` has a direct source proof candidate.
For every actual function φ, its cusps lie in the union

```
{P | ord_P(φ) != 0} union {P | 0 < ord_P(φ-1)}.
```

Both sets are finite by the already ported zero/pole support proofs.
`model_cuspsFinite` constructs that proof directly.
The replacement theorem keeps the existing `hRF` and Belyi inputs for signature compatibility.
Its proof works for every φ, including constants, and contains no `sorry`.
This is the exact proof in `Belyi/CurveField/BelyiRelation.lean:35`.

For noncritical selection, the source uses four mathematical steps:

1. Construct an actual function ψ with simple zeros at a finite set T' containing the requested set T.
2. Form the finite Galois-stable set S of all branch values of ψ, together with infinity.
3. Construct an actual rational elementary composite H on P¹ that sends S to `{0,1,infinity}` and keeps H(0) outside it.
4. Define the actual curve function `φ = H(ψ)` and use the ramification chain rule at every place.

The candidate writes the complete combination of those steps.
It does not replace them with a free Belyi theory or a predicate field.

`Def_FermatNoncriticalFunctions.lean` defines the exact source P¹ objects:

```
Pt = Option ℚbar                      -- none means infinity
ElemMap.mob a b c d (a*d-b*c != 0)    -- rational Möbius map
ElemMap.poly p (0 < p.natDegree)      -- rational polynomial
evalComp hs z                        -- actual point evaluation of the list
ramIdxComp hs z                      -- actual product of root multiplicities
compK hs ψ                           -- actual rational expression in ψ
```

Polynomial ramification at a finite z uses the root multiplicity of `p-p(z)`.
At infinity, it uses the polynomial degree.
A Möbius map has ramification index 1.
The field expression uses actual polynomial evaluation and rational division.
No arbitrary map `Pt -> Pt` is supplied.

`noncriticalValue M x ψ` uses the full residue embedding stored in x.
It is the actual finite value when ψ is regular, and infinity at a pole.
The candidate proves its cusp criterion, its Galois action, and the zero-value criterion.
It also proves that a zero's ramification index equals its actual order.

The branch set retains all residue embeddings.
The proof `noncritical_finite_setOf_mem` uses the finite type

```
sum_{P in finite ramification locus} (ResidueField(P) ->+* ℚbar).
```

It includes every ring embedding of every full residue field.
It does not choose one conjugate to represent a place.
Galois transport changes the residue embedding and preserves the underlying place.
Every place carries a point through an actual embedding of its finite residue field into ℚbar.
Those two facts are direct adaptations of `CurveField/Point.lean:172-191`.

`Def_FermatNoncriticalSimpleZeros.lean` proves that the actual proper place carrier is infinite.
It uses zeros of the distinct functions `u-q`, for rational q, exactly as the source does.
It defines `SimpleZeroFunction M hDVR T` with actual data:

```
ψ : M.K, transcendental over ℚ
T' : Finset (Place M.K), containing T and nonempty
ord_P(ψ)=1 for every P in T'
ord_P(ψ)<=0 for every P outside T'
```

The existing Riemann children supply exact realization of every effective divisor of large degree.
The source proof enlarges T to T' so that the reduced divisor `sum_{P in T'} P` has enough degree.
Every residue degree is positive, which gives the degree estimate.
If that divisor is the polar divisor of f, set `ψ=f⁻¹`.
The candidate proves the two order properties and transcendence of ψ.
No extra open simple-zero existence theorem is introduced.

Three new open children remain:

| Child | Exact content | Source |
| --- | --- | --- |
| `noncriticalRamificationFinite` | The actual set `{P | 1 < ramIdx(ψ,P)}` is finite | `CurveField/NoncriticalFinite.lean:181-188` |
| `noncriticalCompositionRamification` | Positive actual indices and the all-point value/ramification chain rule for elementary composites | `NoncriticalBasic.lean:126-141`; `NoncriticalElem.lean:310-344` |
| `noncriticalP1Zero` | An actual list of rational elementary maps sends a finite Galois-stable S to `{0,1,infinity}`, avoids them at zero, and is unramified away from them | `NoncriticalP1/Main.lean:112-169`, specialized at zero |

Each child states concrete mathematics that differs from the selection parent.
None asserts the existence of a curve Belyi function avoiding an arbitrary set of curve places.
The parent construction still has to build that function and prove both required properties.
All new theorem modules use their complete platform theorem names.
Definitions import no open theorem modules.

`Def_FermatNoncriticalComposition.lean` forms S from all actual branch values.
The simple-zero order properties prove that zero does not belong to S.
It obtains H from the P¹ child and sets `φ=compK hs ψ`.
At every place P, choose an actual algebraic point over P.
If ψ ramifies at P, its value lies in S and H sends it to a cusp value.
Otherwise positivity gives ramification index 1 for ψ, so ramification of φ comes from H.
The P¹ unramified property then gives the cusp condition.
For P in T, the value of ψ is zero, so H's avoidance at zero proves that P is not a cusp of φ.

The replacement `noncriticalSelection` keeps the complete existing signature.
Its body consumes the existing three Riemann children and the three new children.
It contains no `sorry`.
The replacement `cuspsFinite` also contains no `sorry`.
The only three `sorry` terms in this candidate occur in the three new open nodes.

The source proof costs remain explicit:

- Finite ramification uses the actual derivation `d/dψ`, local uniformizers, and finite chart module generators.
- The chain rule uses root multiplicities over the full residue field, polynomial composition, inversion, and Möbius decomposition.
- The P¹ theorem uses the source normalization, rational case, and minimal-polynomial degree reduction from Mochizuki's Lemmas 2.1–2.4.

The candidate does not claim that those source proofs already compile in this workspace.
It also does not add an Act2 result to obtain them.
It leaves the current local compactness interface intact:

```
degree(x_n) <= d
forall embeddings ℚ(x_n) -> ℂ, both logarithmic bounds hold
forall embeddings ℚ(x_n) -> PadicAlgCl 2, both logarithmic bounds hold.
```

The selected φ still satisfies avoidance at every place in the finite limit set T.
The current `AvoidanceRegularity` and `LocalCompactness` consumers therefore retain all their inputs.
This draft never replaces the full point field by `ℚ(φ(x))` for local bounds.
The image-field degree estimate remains the existing exact field inclusion theorem.

`Model.fg_top` has no new consumer here and may remain omitted.
The source class uses `M.u`, `M.transcendental_u`, and `M.finite_u` directly.
