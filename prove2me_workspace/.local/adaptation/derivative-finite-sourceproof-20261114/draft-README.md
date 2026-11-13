# Actual derivative: finite bad places, complete source-proof candidate

This draft fills the existing `noncriticalDerivativeBadPlacesFinite` with the complete pinned source proof, factored into small source lemmas. The exact parent statement is unchanged. There are zero new Open obligations and no `sorry`, `admit`, or new `axiom` in the candidate Lean files. This is source-proof reuse, not a new Act2 mathematical argument.

Everything written by this agent is under this directory. No compiler, Lake build, MCP-CI job, cache mutation, main workspace edit, platform publication, or Git mutation was performed. Static validation does not establish Lean acceptance or an axiom audit.

## Files to integrate

- `Definitions/Def_FermatCurveDerivationAdjoin.lean`: six short source lemmas about the actual formally étale extension, actual polynomial derivative, evaluation, and valuation-subring membership.
- `Definitions/Def_FermatCurveDerivationLocalization.lean`: the source's chart span-induction block and actual-localization block, extracted as two fully proved lemmas.
- `Theorems/Thm_AbcAdaptation_Tripod_Fermat_Proper_noncriticalDerivativeBadPlacesFinite.lean`: replacement of the existing Open proof by the finite-union source assembly.
- `Solutions/Checks_FermatDerivativeFiniteLocalization.lean`: `#print axioms` for all eight helpers and the parent.

Existing `Definitions` modules are imported directly, with no upstream `Belyi` import or full `Mathlib` import. The new Definitions modules import no Theorems modules. No existing constructor or actual derivative is replaced. The temporary scripts can regenerate and statically inspect the draft; they are not proposed project artifacts.

## Concrete source facts and consumers

The source `Belyi/CurveField/NoncriticalFinite.lean::finite_setOf_derivAlong_notMem` does the following:

1. Obtain `G : Finset (chartRing ψ)` and `hG : Submodule.span (Algebra.adjoin ℚ {ψ}) (G : Set (chartRing ψ)) = ⊤` from the existing actual `Module.Finite` instance via `Module.Finite.fg_top`.
2. Form the finite union, over this actual `G`, of pole sets `{P | CurveDeriv.derivAlong ψ (g : M.K) ∉ P.1}`. Each member is finite by the existing `Place.finite_setOf_notMem`.
3. For a place containing ψ and outside that union, extend membership from `G` to the actual chart ring by `derivAlong_mem_chartRing_of_generators`. Its scalar case uses the actual `CurveDeriv.derivAlong` and the source `derivAlong_mem_of_mem_adjoin`.
4. Use `derivAlong_mem_place_of_chartRing` to pass to every element of the actual local ring. This follows `Place.ofChart_toChart`, unfolds `Place.ofChart_val`, extracts the actual chart numerator and denominator, and uses `Place.mem_toChart_iff` and `ValuationSubring.mem_nonunits_iff_or` to prove the denominator inverse belongs to `P.1`. The actual derivation's quotient rule then finishes.
5. Apply this result to the local witness `s` to contradict derivative nonmembership.

The full place carrier, actual field `M.K`, actual chart integral closure, actual finite-module generator set, actual valuation subring, and actual localization prime are retained. The conclusion ranges over all `Place M.K`; neither finite place coverage nor derivative regularity is supplied as a hypothesis. The only supplied generator membership in an internal helper is obtained by negating the actual finite union. It is not an extra assumption in the parent.

Every producer has a concrete consumer. `extendOfFormallyEtale_algebraMap` and `polyDeriv_apply` feed `derivAlong_aeval`; that feeds `derivAlong_mem_of_mem_adjoin`. `aeval_mem` feeds both adjoin-membership lemmas. Both adjoin-membership lemmas feed chart span induction. Chart span induction and actual localization feed the finite parent. The existing consumer of the parent remains `noncriticalRamificationFinite`. The complete mapping, source identities, and SHA-256 hashes are in `source-consumer.json`.

## Sources and fidelity

Pinned Belyi commit: `9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8`, upstream `https://github.com/lana-agents/belyi`.

- `Belyi/CurveDeriv/Basic.lean`: `cf1b11adab96fbd7d7bb5114e7215dcbf8b8cda1a8eda573e9759ac5316f40b2`.
- `Belyi/CurveDeriv/Local.lean`: `cb930e45cba81a1377ab8281264d938868ae7834d32c480a9af9d29012eb1aae`.
- `Belyi/CurveField/NoncriticalFinite.lean`: `97605e681191f8a923c7de80df284e327550f708a884b5deb135e469b6a2bbf8`.

Reference source copies are in `reference/`. Basic and Local were fetched from the pinned raw URLs; NoncriticalFinite was copied from the pinned reference delivered with the previous decomposition. Every candidate source file preserves the upstream Apache-2.0 notice and source pin; new files list source path and hash. `LICENSE` contains the standard Apache-2.0 text from `/usr/share/common-licenses/Apache-2.0`.

Changes to the source proofs are limited to the independent namespace, the existing local extension function spelling, extraction of the chart and localization blocks as reusable lemmas, the existing `M.isCurveField` adapter, the parent function variable ψ, and explicit casts. There is no arbitrary derivation argument or law record replacing `d/dψ`. The extension lemma has the source's generic derivation parameter because it proves the existing actual construction evaluates correctly; its consumer applies it to `polyDeriv` inside the existing definition.

## Validation and integration

`static-review.json` records textual checks: the parent theorem type is byte-for-byte identical; five theorem texts match source modulo the extension namespace; no proof hole, new axiom, forbidden import, or Definitions-to-Theorems import occurs; the actual generator, finite-pole, and localization APIs are present. `source-consumer.json` records hashes of the existing base inputs used for this draft, so the main agent can detect concurrent integration changes.

The main agent must integrate and validate through MCP-CI. New leaf modules use the first-attempt 60s/16GiB estimates. Check the new leaves, their Checks/axiom output, and the required containing import and project audits. No kernel, CPU-time, wall-time, memory, or whole-project success is claimed here.
