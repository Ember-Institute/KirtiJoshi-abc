This revision separates existing proof reuse from the new Fermat pole identity.
It contains one independent finite-support unit and one conditional canonical-degree decomposition.
The two existing parent theorem signatures remain unchanged.

The finite-support unit has two files:

- `Definitions/Def_FermatInfinityDivisorFiniteSupport.lean`.
- `Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_infinityDivisorExists.lean`.

This unit contains no `sorry` and imports no new Open theorem.
It reuses the existing finite coordinate support theorem and the existing Finsupp construction.
The actual max(pole_u,pole_v) coefficient has support in the union of those finite sets.
It needs no Fermat pole-order calculation, degree theorem, or adjunction input.

The conditional decomposition has three files:

- `Definitions/Def_FermatCanonicalCoordinatePoleComposition.lean`.
- `Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_coordinatePoleMultiplicity_eq.lean`.
- `Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_canonicalDivisorDegree.lean`.

The new Open child states one concrete identity:
for N>0, the actual u and v pole multiplicities agree at every actual proper place.
It includes regular places, zero-coordinate cases, and places at infinity.
It does not mention canonical degree, adjunction, or any height estimate.
No pinned source is claimed to contain a proof of this Fermat identity.

The Definitions file imports no Theorems module.
Its conditional theorems explicitly receive the exact all-place coordinate-pole equality.
They identify the supplied H with polar(u), then apply the existing actual fiber-degree theorem to obtain deg(H)=N.
The final conditional theorem sums the original actual J.coefficient relation.
It uses the existing actual principal-degree-zero proof and the proved conditional value of deg(H).

The unchanged `canonicalDivisorDegree` signature consumes the concrete Open child and its original actual J input.
Its body has no `sorry`, but it depends on that one Open child.
The only `sorry` in this revised deliverable is the precise coordinate-pole child.
The original `canonicalDivisorExists` and `planeAdjunctionExists` remain Open and unchanged.

The earlier novel common-pole proof stays only in:
`/tmp/p2m-fermat-canonical-divisor-next-20261114/Definitions/Def_FermatInfinityDivisor.lean`.
That research file is outside this deliverable. It is not copied, imported, or presented as existing source reuse.

The pinned sources are Belyi at `9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8`
and Heights at `721496ca4c158e511d25d8ccf6bfe8503eda73c1`.
The source-adaptation files preserve the relevant Apache notice and state their source scope.
The new Open Fermat file has its own project notice and explicitly denies a pinned proof attribution.
No upstream runtime dependency is added.

The actual Model, u, v, normalized ord, ramIdx, divisors, and degrees remain fixed.
There are no arbitrary law fields, free degree values, or constant-field-equals-ℚ assumption.
No Act2 file or new Fermat proof is added.

The candidates were not compiled or read back after writing.
No CI task ran. The main workspace and earlier temporary drafts remain unchanged.
The parent signatures and one-Open-child boundary were checked in memory before writing.

The main agent can integrate and validate the independent infinity unit first.
The canonical decomposition is a separate Open-child unit for review and later work.
Run the repository's MCP-CI checks and actual axiom audit before acceptance.
The canonical decomposition must retain its expected Open-child `sorryAx` status until that child has an authorized proof.

`source-consumer.json` records the producer chain, exact child type, source scope, and separate integration units.
