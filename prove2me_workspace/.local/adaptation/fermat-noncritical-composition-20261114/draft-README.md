# Actual composition and ramification: minimal source decomposition

This draft preserves the exact existing `noncriticalCompositionRamification` statement. It adds one completed source positivity helper module, one concrete Open elementary-map child, and the source list-induction proof of the original parent. No Lean/compiler/Lake/MCP-CI execution, repository/cache edit, old Definitions edit, or publication was performed.

Pinned Belyi source: `9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8` (`refer/iut/lake-manifest.json`). All six reference copies match fresh pinned upstream downloads. The JSON ledger records exact source paths/hashes, adaptations, and consumers.

- `Definitions/Def_FermatNoncriticalRamificationPositive.lean`: four completed source residue/polynomial helpers and source `ramIdx_pos`, reparameterized to the existing model/order definitions. The regular branch uses the actual full residue-field minpoly; the pole branch uses the actual normalized negative order. All helpers have actual consumers; there is no `sorry` or Open Theorem import.
- `Theorems/..._noncriticalElementaryCompositionRamification.lean`: one Open source `applyK_spec`, for the existing genuine rational elementary map constructor, all actual residue embeddings, actual value, and actual ramification index. It has no free map or law parameter.
- Replacement `Theorems/..._noncriticalCompositionRamification.lean`: actual source list induction generalizing the input function, with positivity as its first conjunct. It has no `sorry` and keeps the exact parent type.

No derivative carrier/module is imported. Polynomial membership borrows only the completed elementary sum proof from `CurveDeriv.Local.aeval_mem`; it uses no derivative fact.

The existing unused `noncritical_eval_zero` has a genuine next source consumer: `Point.eval_inv` uses `eval_zero` in its zero-function branch, then `NoncriticalElem.inv_spec` uses `eval_inv`, then `mob_spec`, then `applyK_spec`. This minimal draft keeps that deeper math inside the single Open child, so it does not add an unused `eval_inv` or a forced zero-evaluation reference. The exact future source route is recorded; the unused-producer debt is not claimed closed.

`static-review.json` records parent-type equality, helper proof comparison, one-Open-child count, and import closure checks. These are static checks only. Root must validate through MCP-CI; no compilation, axiom, or resource pass is claimed.
