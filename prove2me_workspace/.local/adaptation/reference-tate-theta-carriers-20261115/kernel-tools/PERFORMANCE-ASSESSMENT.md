The actual original export succeeded in `ci-014041-0f843e16`: root-reported wall time211.31s and peak physical RSS12.49GiB. This is below the16GiB leaf threshold. The first180s timeout supplies only a duration lower bound; no OOM conclusion follows from it.

The raw accepted artifact is958,393,501bytes (914.0MiB). A lossless compact view is202,135,430bytes (192.8MiB), a78.91% reduction. The view retains every one of117 original records,78 selected records, all proof/data bodies, actual Name components, BinderInfo, and metadata. Verification compared all75,231,873 JSON lexical tokens for exact equality. Only insignificant whitespace outside string literals changed. The source JSON was already parsed and accepted by `original-exprs-acceptance.json`; identical complete lexical token streams give the same parsed JSON. No pair of full parsed Expr trees was allocated for this check.

| Module | All / selected | Raw bytes | Compact bytes |
| --- | ---: | ---: | ---: |
| JInvariant |11 /2 |10,804,877 |3,985,539 |
| Parametrization |23 /5 |201,168,348 |55,098,705 |
| AdmissiblePrime |38 /37 |253,564,667 |36,921,153 |
| TateStructure |45 /34 |492,842,545 |106,118,661 |

These module sizes are the sum of record object spans. They exclude the small common top-level envelope. The largest raw record is the unselected `Yterm_q_smul` (114,525,373bytes), which becomes30,948,629bytes. The largest selected record is `TateStructure.mk.injEq`:112,479,346bytes raw and15,419,351bytes compact. These record sizes describe serialization, not physical compiler memory.

The configuration generator currently parses the complete JSON into Python objects. Compact input avoids retaining the original914MiB text during that parse, but the parsed nested object tree has the same contents and essentially the same representation. The generator needs actual structural Names and metadata to bind its153 relocation rows. It does not need to retain Expr bodies in its output configuration. No physical RSS estimate can be inferred reliably from file bytes alone. No full `json.loads` profiling run was added while the main agent handles acceptance.

The Lean auditor also parses the complete original JSON and retains all records. It decodes every actually compared type and checks all selected names, owners, instances, axiom closures, structure metadata, and recursor rules. It decodes computational bodies for data declarations. The78 selected records comprise31 propositions and47 data declarations; their serialized `valueExpr` field spans total53,581,509bytes and26,007,492bytes respectively in compact JSON. Proof bodies remain in the record evidence; the established audit compares proof declaration types and axiom closures. Optional missing declarations remain reported. Compact serialization changes none of these rules.

The narrow next step is to use the full compact input and serialize the full audit output with `Json.compress`. Platform Lean4.33.1 `Lean/Data/Json/Printer.lean` defines `pretty` by first constructing a `Format` tree; `compress` uses an explicit work queue to construct the output String. Removing deep pretty-print indentation therefore avoids the expanded output and its Format tree. This does not reduce the parsed JSON tree or justify a claim that kernel checking will stay below16GiB. The actual MCP-CI receipt must decide that.

`prepare_audit_config.py` now supports `--original-view-evidence` to hash-bind the raw artifact, compact artifact, token-equivalence report, accepted source export, and its actual compiler receipt. It also supports `--compact-output`; this changes exactly the final audit JSON serializer from `.pretty` to `.compress`. Every check and output field remains present. File hashing uses1MiB chunks. These generator changes are uncompiled draft tooling; no current kernel comparison or acceptance is asserted.

No audit batching architecture is prepared or recommended before actual performance evidence requires it. The four source modules supply a natural complete partition if later splitting is necessary, but that would require a new, explicit coverage-and-aggregation design rather than dropping unselected records or metadata.
