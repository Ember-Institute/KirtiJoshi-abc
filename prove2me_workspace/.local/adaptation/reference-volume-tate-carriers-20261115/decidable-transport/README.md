Draft tools for the five volume/Tate carrier modules. The parent agent must integrate and submit all Lean checks through MCP-CI; these drafts have not been compiled.

`QueryNextCarrierParserRanges.lean` parses source command ASTs under the five original imports. It uses `FOUNDATION_PARSER_CONFIG`. It preserves the accepted parser algorithm and `RestrictedProduct` scope, without importing the unrelated C22 root.

`QueryNextCarrierOriginalExprs.lean` uses `NEXT_CARRIER_EXPORT_CONFIG`. It derives declarations and counts from `export-config.json`, exports actual compiler expressions and confirms the complete module-owned constant set. It preserves the accepted packet-field exporter's cached `collectAxioms` and indexed `env.header.modules` owner lookup. Structure metadata now also includes structural field Names, projection identities, subobject identities, field BinderInfo, parent order/identities, and optional autoParam expressions. The Lean 4.35.0-rc3 and 4.33.1 installed `Lean/Structure.lean` definitions were inspected; these APIs agree. Their compatibility still requires main-agent CI.

Generate the platform audit config and its exact imports after integration:

```sh
python3 prepare_audit_config.py --inventory-dir . \
  --original-exprs "$PWD/original-exprs.json" \
  --audit-output "$PWD/kernel-audit" \
  --wrapper-report "$PWD/wrapped/wrapper-report.json"
```

Use the actual wrapper-report path. Omitting `--wrapper-report` produces an explicitly marked candidate import plan for inspection. The script writes `audit-config.json`, `AuditNextCarriers.lean`, `accepted-prior-identity-map.json`, and `source-axiom-inventory.json` alongside itself. `AuditNextCarriers.template.lean` must remain alongside the generator. The auditor uses `NEXT_CARRIER_AUDIT_CONFIG`.

Counts derive from the current inventory: 147 source records, 100 selected records, five current modules, 62 required accepted prior identities, and 209 total relocation entries. The independent prior identity map includes all 241 actual named identities (foundation110 plus packet-field131), with no candidate-only names or proof-value elisions. Only six required prior Def owners are imported: RationalPlace, Procession, PacketPresentation, Container, HolomorphicHull, and QParameter.Basic.

The strict audit checks exact selected types through the kernel, full type BinderInfo sequence and placement, universe parameters/permutations, constructor/recursor shapes and rules, structure metadata and autoParams, computational values, instance registration, owner/import closure, and standard axiom closures. Missing unselected declarations and target-only compiler declarations are reported for explicit review. No generated-name difference is waived, and no old GlobalField helper resolver is included. Only `TateCurvesTheta.IsUniformizer.casesOn` and `.recOn` may use a full-value equality proof if kernel definitional equality fails. That path requires the exact three-parameter, three-proof-field shape, proves the complete equation by primitive recursion and function extensionality, and kernel-checks its exact type, allowed dependency owners, and standard axiom closure. It reports definitional equality as false and propositional equality as true; public type and binder checks remain strict. A generated-name mismatch must be diagnosed from actual source and target compiler evidence.

LogVolume retains its graph-pinned effective source override. Its current SHA256 is `002f44da071e858c1fe48f3608da4e75f1179d3cd6c3007444bc5453440b7ef0`; provenance separately records upstream source SHA256 `79f0f12f1c82d6a0b6b83a42197527542fa946e9a5bb8dd4fd3572fd88edaf15` and Git blob `0415c756966155e5286911d75f26fbd0c8f0366c`. The generator verifies effective source hashes and preserves the supplied provenance.

Static validation is recorded in `static-validation.json`. It is not a Lean compilation receipt.
