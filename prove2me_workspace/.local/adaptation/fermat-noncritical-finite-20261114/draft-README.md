# Finite ramification: concrete source decomposition draft

This directory contains three small Definitions modules, two Open source children, and the original parent with the source finite-union proof. The parent statement is unchanged. No compiler, Lake, or MCP-CI task was run; no repository, cache, or platform was modified.

Pinned source: Belyi `9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8`, from `refer/iut/lake-manifest.json`. Both included reference files match fresh pinned upstream downloads. Source notices, paths, hashes, and producer/consumer mappings are recorded in Lean headers and `source-consumer.json`.

The actual derivative is built in three layers:

- `Def_FermatCurveDerivationEtale.lean` (33 lines): the actual Kaehler differential construction extending a derivation along a formally étale algebra.
- `Def_FermatCurveDerivationPolynomial.lean` (61 lines): the actual polynomial derivative on ℚ[ψ], its two needed evaluation-equivalence helpers, and the proved formally-étale adjoin fact.
- `Def_FermatCurveDerivationBasic.lean` (32 lines): exactly the source `derivAlong`, extending that polynomial derivative when ψ is transcendental and K is algebraic over ℚ(ψ), with the same zero fallback otherwise.

Every helper has a concrete consumer in the current construction. No arbitrary map, supplied derivation, law record, extra assumption, unused chain-rule interface, or full Mathlib import is added. Definitions contain no Open Theorem imports and no `sorry`.

The two Open children are the source's distinct statements:

- `noncriticalRegularRamifiedDerivNotMem`: at a regular ramified place, the actual derivative of some regular local element is not regular.
- `noncriticalDerivativeBadPlacesFinite`: the actual derivative fails to preserve only finitely many local rings containing ψ.

The parent uses the completed source argument: a ramified place is either a pole or a regular derivative-failure place, and the union of these two finite loci is finite. The pole locus and all valuative places, including places at infinity, are retained. The two child proofs remain `sorry`; no mathematical debt has been filled with a new argument.

Static readback compared the actual constructor/proof bodies against source and the parent type against the existing target. It checked exactly two `sorry` bodies, no `sorry` in Definitions or parent, and no forbidden local import. See `static-review.json`. These checks do not constitute Lean acceptance or an axiom audit. The main session must validate through MCP-CI. First leaf estimates must remain 60s/16GiB; no measured resource claim is made.
