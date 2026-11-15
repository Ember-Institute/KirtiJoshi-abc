Prepared only in `/tmp/p2m-tate-theta-inventory-v5-20261115`. Planned main directory: `/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/reference-tate-theta-carriers-20261115`. No main workspace writes, compiler, MCP-CI, API, network, or Git writes were performed. Read-only Git blob/tree/commit/origin queries establish exact upstream provenance.

Exact modules in dependency order:

1. `TateCurvesTheta.TateCurve.JInvariant`: 11 originals / 2 selected / 1 source root candidate.
2. `TateCurvesTheta.TateCurve.Parametrization`: 23 / 5 / 4.
3. `Iut.Cor312.ThetaData.AdmissiblePrime`: 38 / 37 / 6.
4. `Iut.Cor312.ThetaData.TateStructure`: 45 / 34 / 9.

Totals: 117 original declarations, 78 selected, 20 complete source-command candidates. No selected missing owner, no additional source module, no missing prerequisite, no source override. The accepted dependency inventory has 339 actual named identities: foundation 110, packet/field 131, volume/Tate 98. Exactly 42 are needed here: foundation 2, packet/field 14, volume/Tate 26, from six installed source bundles. Four genuine proof-value resolutions remain separate and none is required as a named dependency. `accepted-prior-identity-map.json` pins actual acceptance evidence, including volume job `ci-013964-cce30c9e`; it asserts no current-unit acceptance.

`inventory.json`, `dependency-closure.json`, `unit-config.json`, `parser-config.json`, `export-config.json`, `imports.json`, `frozen-sources/`, `source-provenance-audit.json`, `source-bytes-manifest.json`, and the source ledger are ready for main integration. Configuration output paths intentionally refer to the planned main directory. Upstream sources were compared with exact fixed commit blobs and the accepted graph source receipt. Apache headers are retained; Tate has no standalone upstream LICENSE/COPYING/NOTICE. Distributed Apache text is from pinned iut.

`QueryNextCarrierParserRanges.lean` is an UNCOMPILED candidate. It retains the AST of every command, all source contexts and proof bodies. It resolves unique actual compiler Names from the environment, serializes str/num components, and never reconstructs declaration Names from dotted text. All-original Parametrization includes six unselected private Names with numeric component 0. `export-config.json` therefore deliberately uses `nameExpr: null` for all source candidates; the Expr exporter supplied by the tooling agent must resolve actual Names and emit their true components. Null is not an accepted Name. Do not run the old exporter that requires configured structural Names.

Retain all 15 fields of AdmissiblePrimeData and all six TateStructure fields. Keep `galPointMap_torsionBy` and `TateStructure.ofUnit_mul/ofUnit_one/ofUnit_inv` as exact inline helper proofs inside their carriers. Do not infer convergence, discriminant/norm estimates, periodicity, optional ofTateParameter construction, or parent Theorem110/C22 completion from this signature-carrier work.

`source-context-review.json` records lexical context candidates only. The actual parser AST must establish scopes. JInvariant and Parametrization open anonymous noncomputable sections before their namespaces; their namespace endings leave the anonymous section to implicit EOF closure. TateStructure has an explicit anonymous-section `end`. The source wrapper must preserve and correctly close scopes when concatenating.

Static verification passed: 656 graph/config/closure checks, 126 source/provenance/import-path checks, 113 supplier/scope checks (895 total). These are static checks, not current source compiler acceptance. Remaining main tasks: integrate tooling/exporter/auditor, compile parser through exclusive MCP-CI, validate exact parser command ownership and original Names, export actual Exprs, generate/compile small sources, strict audit (including axioms and proof-value separation), and ordinary project acceptance/delivery.

Reproduce the local static preparation, in this order:

```sh
python3 /tmp/p2m-tate-theta-inventory-v5-20261115/prepare_inventory.py
python3 /tmp/p2m-tate-theta-inventory-v5-20261115/finalize_inventory.py
python3 /tmp/p2m-tate-theta-inventory-v5-20261115/audit_static.py
python3 /tmp/p2m-tate-theta-inventory-v5-20261115/audit_provenance.py
python3 /tmp/p2m-tate-theta-inventory-v5-20261115/prepare_review.py
```

`draft-manifest.json` contains per-artifact hashes. No source candidate is labelled accepted and no new receipt is fabricated.
