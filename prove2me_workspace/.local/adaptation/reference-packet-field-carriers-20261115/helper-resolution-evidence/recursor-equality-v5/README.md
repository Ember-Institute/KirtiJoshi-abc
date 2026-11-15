# Generated eliminator equality draft

`AuditNextCarriers.lean` is based on main auditor SHA256 `f10be8b95fa42d7d03090878979e98c190777ca4945c788b7cd20001f2cd2ea1`. It retains the already accepted narrow internal-proof resolution and all original type, BinderInfo, proposition, instance, structure, computation-shape, recursor-rule, axiom and owner checks.

The exact allowlist contains only `Iut.IsInitialThetaGlobalData.casesOn` and `.recOn`. Definitional value equality is still attempted first. If it is false for either allowed name, the draft constructs a proof of equality of the complete actual source and target values. Other names fail immediately.

The proof builder requires the actual major-premise type to be the exact initial-theta structure applied to its nine parameters, with one constructor, six proposition-valued fields, no indices or nested inductives, and the expected safe primitive recursor. It constructs the motive `fun major => ∀ minor, sourceApplied = targetApplied`, proves its constructor branch by reflexivity over all six symbolic fields, applies the actual primitive recursor, and uses function extensionality for all twelve function arguments. `Kernel.check` must accept the resulting closed proof, and its inferred type must be kernel-convertible to the exact full-value equation. No theorem or definition is added to the environment. Standard axiom and dependency-owner checks also apply to the equality proof.

The report distinguishes the relations. `kernelValueEqual` reports definitional equality and is false on this fallback. `kernelPropositionalValueEquality` is then true, and `propositionalValueEqualityEvidence` contains the exact equation, complete kernel-checked proof, primitive recursor, constructor and axiom closure. `computationalValueEqualityChecked` records that one of these complete value checks succeeded. The existing owner-coverage requirement for `solvableClosure` still requires definitional equality and is unchanged.

`audit-config.json` changes only the old baseline config evidence path to `attempts/kernel-audit-v1/audit-config.json`; its authenticated SHA256 is unchanged. `prepare_patch.py` reproduces the draft and this config adjustment. It writes only in this task directory.

`casesOn-diagnosis.json` records exact original/actual expression fingerprints and shapes: source casesOn applies its minor argument to projections0–5 of the major proof; actual target casesOn calls the primitive recursor. Source recOn is a casesOn alias; target recOn calls the recursor. The earlier failure is `ci-013631-b87620ef`; the actual target facts came from `ci-013599-61a18ec4`.

Source/config files are frozen at the hashes in `draft-manifest.json`. This task did not compile, submit CI, edit main or production files, or make API/Git writes. Root must review and submit the audit through MCP-CI.
