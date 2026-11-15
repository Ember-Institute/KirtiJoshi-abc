Offline tooling draft for the five volume/Tate carriers. All subagent writes are
inside this directory. No Lean/compiler process, CI job, API/network call, or Git
operation was performed. Main integration owns all actual compilation.

Copy carrier_contract.py, prepare_unit.py, subtract_carriers.py, select_small.py,
wrap_carriers.py, bind_small_oracles.py into the stable task directory B:
`prove2me_workspace/.local/adaptation/reference-volume-tate-carriers-20261115`.
The runtime driver is an exact copy of the accepted B0 driver. Keep root's already
installed identical driver. The exporter here is only the accepted B0 cached
baseline; integrate the current kernel agent's exporter with expanded structure
metadata instead of replacing it with this baseline.

The exact modules are Iut.Cor312.ContainerHull, Iut.Cor312.LogVolume,
TateCurvesTheta.QParameter.PrimeToOrder, TateCurvesTheta.TateCurve.Weierstrass,
and TateCurvesTheta.QParameter.NormalizedOrder. Existing foundation-* report
basenames/schemas are retained for compatibility. They do not define unit scope.

1. Integrate the inventory agent's final config, source-provenance audit, and
   source-overrides/LogVolume.patch. Preserve their hashes and planned B paths.
2. Run prepare_unit.py with --inventory-unit B/unit-config.json,
   --dependency-closure B/dependency-closure.json,
   --foundation-ci-result <foundation>/kernel-audit-v2-result.json,
   --packet-field-correspondence <B0>/accepted-compiler-correspondence.json,
   --provenance-audit B/source-provenance-audit.json,
   --out B/bound-unit-config.json. Optional --packet-field-typed-map selects
   the raw B0 provenance map; the default is B0/generated-wrapped/typed-original-source-wrapped-map.json.
   This revalidates both successful scheduler receipts, exact installed bundle
   bytes, and prior kernel outputs. Foundation contributes 110 named constants;
   packet-field contributes 131 actual named constants from ci-013658-36534ff1.
   The 62 needed pairs must agree with the inventory closure. All 241 actual
   named pairs remain available metadata, but the import plan controls imports.
   No proof-value resolver or unrelated GlobalField import is introduced.
3. Review reviewed-imports.template.json against the final imports.json and
   mark reviewed only after review. Save as precise-import-review.json and
   rebind importsCandidateSha256 if the inventory changes. Exact Lean tactic
   imports permitted on platform are Lean.Elab.Tactic.NormCast and
   Lean.Elab.Tactic.Omega. No broad Mathlib/Lean fallback is permitted.
4. After a successful parser job, run select_small.py (or subtract_carriers.py)
   with --parser-acceptance, --parser-ci-result, --parser-config, --parser-query,
   --graph, --imports, --reviewed-imports, --unit-config, and --out B/generated.
   Complete original retained command and context bytes are copied in order.
   Only excluded declaration commands and the AST-bound import header change.
5. Run bind_small_oracles.py --small-source-report
   B/generated/foundation-small-source-report.json --out B. This writes exactly
   one configured source per oracle config. Root submits the accepted Lean-only
   runtime driver once per config, sequentially, through MCP-CI. Never batch
   multiple source frontend lifetimes in one process. Runtime acceptance remains
   terminal successful receipt plus process-tree physical peak RSS <=16 GiB.
6. After all five genuine single-source oracle outputs are accepted, run
   wrap_carriers.py with --small-source-report, --parser-acceptance,
   --original-exprs, --original-exprs-acceptance, --original-exprs-ci-result,
   --imports, --reviewed-imports, --unit-config, --oracle-driver-acceptance,
   --oracle-driver-ci-result, five paired --oracle-receipt / --oracle-ci-result,
   and --out B/generated-wrapped. The unchanged receipt validators accept
   authentic raw single-source reference-stage2-index-v1 indexes, bind every
   config/source/output SHA, and bind runtime requests to the accepted driver.
7. Pass generated-wrapped/foundation-wrapper-report.json to the kernel agent's
   config builder. It reports exact direct imports and complete source-to-wrapper
   command/body byte provenance. Platform leaf/artifact and kernel/axiom audit
   must pass before delivery.

The dependency checker preserves strict prior type, computation-shape, instance,
and BinderInfo checks. Only packet-field's pinned accepted audit permits the
recorded old proof3 -> target proof2 BinderInfo implementation difference: all
8 exposed Pi binders/domains, all 3 mathematical argument binders, and all 3
closed SMul data instance type/value equalities must hold. The one casesOn
computational pair additionally requires the accepted exact full-value
propositional equality proof (12 arguments, 6 constructor fields, standard axioms).
These exceptions do not apply to any new proof or other prior pair.

The raw B0 namespace map is candidate provenance. Actual audit target names
replace its target candidates in the effective prior constants. Original
solvableClosure._proof_2 and _proof_4 are exported proof-value resolutions with
no standalone target identity; neither enters the named dependency map. Current
unit prefix names also remain candidates until actual compiler-name discovery
and kernel audit establish correspondence.

LogVolume uses the reviewed effective compiler source, not the raw upstream
blob. Its provenance retains sourceGitBlobMatches=false. The checker verifies
upstream blob/SHA, effective compiler-source SHA, exact complete unified patch,
and the graph receipt's source-build-plan hash and exact LogVolume entry. The
wrapper's adaptation-authored notice records this override, its accepted graph
job, and patch/effective-source hashes, while preserving original notices.

Production wrappers preserve full original command/proof bytes inside
AbcAdaptation.Reference and retain author/license notices. Blind packets remove
license and adaptation notices plus every parser-recorded nested/module doc.
All comments in these five inspected source files are such notices/docs; no
ordinary comment removal heuristic was added. No semantic source token is
rewritten. Any new ordinary comments require explicit reviewed range evidence.

Offline validation covers Python syntax, exact B0 runtime-driver bytes, both
prior audit units (241 named identities), the required 62 actual pairs, the
reviewed override patch and graph-source chain, and precise import graph checks.
The offline-bound-unit-config.json uses scratch-only patch path replacements
and is an example, not an integration config: rerun prepare_unit.py at B.
No new source isolate/wrapper or new compiler result is fabricated here.
