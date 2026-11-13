# Concrete P¹ noncritical-at-zero decomposition draft

This directory contains a source-backed replacement of the current `noncriticalP1Zero` Open parent by three Open source reduction steps and a completed source combination proof. All drafts stay in this task directory. No repository, cache, platform, or build process was changed.

Pinned source: `lana-agents/belyi` commit `9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8`, as recorded in `refer/iut/lake-manifest.json`. The reference copies retain Apache-2.0 notices. Exact SHA-256 values, source declarations, and consumers are recorded in `source-consumer.json` and Lean notices.

Proposed additions:

- `Definitions/Def_FermatNoncriticalP1Reduction.lean`: actual rational-point inclusion, source degree, full Galois-stability predicate, branch set including infinity, an actual complex embedding, and the transparent conjunction of the three concrete source noncritical-Belyi conditions. All helper theorem bodies are proved; it imports no Open Theorems.
- `Theorems/..._noncriticalP1Normalize.lean`: source `Reduction.normalize_step`, with unit-disc normalization, all degree/count bounds, and exact source precomposition continuation.
- `Theorems/..._noncriticalP1Rational.lean`: source `Reduction.rational_step`, restricted to degree ≤ 1 branch points in the unit disc, at rational point 9.
- `Theorems/..._noncriticalP1Minpoly.lean`: source `Reduction.minpoly_step`, preserving Galois stability and rational-point exclusion while strictly decreasing the top-degree count.
- Replacement `Theorems/..._noncriticalP1Zero.lean`: source `Main.core_key` double induction, source `withInf` endpoint, and source `eraseNone` adapter specialized to zero. This file contains no `sorry`.

The only `sorry` declarations are the three mathematical source steps. Their statements were independently compared with the pinned source after namespace and whitespace normalization. The exact current parent statement was also compared and is unchanged. `ElemMap`, `evalComp`, `ramIdxComp`, and the underlying concrete evaluation/ramification definitions are reused unchanged from the current repository. No arbitrary point function, law record, or extra hypothesis is introduced.

The source continuation contracts are theorem conclusions about actual `ElemMap` lists. They preserve all three concrete conditions, including every ramified-point image. They are not free law fields. The normalization contract also retains degree bounds and top-degree cardinality; the minpoly contract retains the new rational point and its exclusion from the new full Galois-stable set.

No Lean, Lake, compiler, or MCP-CI task was run. These are uncompiled drafts, not accepted proofs. Integration requires the parent session's MCP-CI validation. The existing unrelated topological/u/v parents remain outside this draft. No source proof debt was filled with a new mathematical argument.
