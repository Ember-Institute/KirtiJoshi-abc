Frozen runnable candidate and configuration:

- `AuditNextCarriers.Decidable435Transport.lean`
- `audit-config.decidable435-transport.json`
- `decidable-transport-final-freeze.json`

Root can copy the candidate to the actual unit's `AuditNextCarriers.lean`, copy the generated config to the unit's `audit-config.json`, and submit the auditor through MCP-CI. Set only `NEXT_CARRIER_AUDIT_CONFIG` to the integrated config path. Earlier `DECIDABLE_STANDARD_FACTS_INPUT` instructions are superseded: all fact paths and contents are bound in the generated config.

The config binds the exact contents and SHA256 of three genuine successful query receipts and their outputs: source core query `ci-013901-2c932c62`, platform query `ci-013907-b9f0843a`, and 250-constant source support closure query `ci-013924-3a1c20d9`. The auditor reads these files, compares each with its bound contents, and checks each receipt's job, status, exit code, and exclusive workspace mode. The config generator independently verifies every hash and receipt before writing. These files, the actual original Expr export, and the generated config must be included in root's stable CI inputs.

The source has 100 mandatory selections. The new config has 98 mandatory named selections and two genuine proof-value resolutions; it removes the two nonexistent source proof target identities from the relocation map. All 147 original source records remain exported and checked. The two source helpers are proposition-valued theorems. The two actual target `_aux_1` declarations are data-valued definitions that forward the decision procedure. The config never maps one to the other. It binds the actual target auxiliary records as provenance, requires exactly those two target-only compiler names, and retains the normal owner, type/value closure, and axiom audit for both.

The standard transport inlines the exact exported `Bool.Reflects` body. Only absent definition/proof bodies actually reached from the exact missing matcher and coprimality-proof roots are expanded. Their genuine exported universe parameters are instantiated at each occurrence. Existing native API references remain native and are kernel-checked inside every expanded proof/type. Unknown constructors, inductives, recursors, cycles, missing genuine bodies, or incompatible API types fail closed. The 250-record source closure is evidence; it is not a blanket replacement map.

The constructor bridge preserves the original Boolean and reflection proof, using primitive Boolean elimination into the old `isFalse`/`isTrue` constructors. The kernel checks its exact source constructor type, complete type BinderInfo, and the symbolic equation `decide (transport p b h) = b`. It does not choose another decision algorithm or rename the missing constructor.

The two original helper proofs are expanded from their actual exported values, through `Nat.instDecidableCoprime._proof_1` and `Nat.decEq._proof_1` as needed. Each genuine value must inhabit its exact original transported proposition. Each source record, raw BinderInfo inventory, expanded type/value, dependency owner, and axiom closure remains recorded. Each resolution has `standaloneTargetIdentity: null`.

Both original and target parent data values must inhabit their exact common public types. If definitional equality fails, only the two named decidability instances may use a constructive pointwise `Decidable p` subsingleton equality followed by function extensionality. The kernel checks the complete value equation and source/target decision-bit equality. Neither source proof resolution is accepted unless its complete parent value has a kernel-checked equality. The existing narrow IsUniformizer full-value proof and all public type, BinderInfo placement, field/parent/constructor/recursor metadata, instance registry, import, owner, and axiom checks remain intact.

Regenerate these drafts in the task directory:

```sh
python3 prepare_decidable_transport_patch.py \
  --support-closure /home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/reference-volume-tate-carriers-20261115/decidable-standard-source-closure.json \
  --support-receipt /home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/reference-volume-tate-carriers-20261115/decidable-standard-closure-v2-result.json
```

Python AST parsing, actual evidence hashes, config dimensions, exact source/target helper kinds, parent-equality guards, standard support scope, and preservation of the public checks were checked statically. The subagent did not compile, call CI, edit the main workspace, or write to Git/network APIs. Root must run the new exclusive audit before accepting this candidate.
