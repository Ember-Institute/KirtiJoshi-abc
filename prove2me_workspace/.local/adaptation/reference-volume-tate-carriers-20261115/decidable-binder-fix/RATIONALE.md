# Exact constructor type annotation draft

The failing receipt is `ci-013943-12fe9ec4` (`kernel-audit-v2-result.json`). The diagnostic receipt is `ci-013946-ec7e3984` (`kernel-audit-v3-diagnostic-result.json`). Both pass the kernel equality of the constructor bridge type with the translated genuine source type and stop at the syntactic `binderPlacement` comparison. The public constructor telescope retains `implicit/default/default`; the mismatch concerns internal lambda positions in the inlined reflection domain.

The normalization is not in `forallTelescope`. In the installed Lean 4.33.1 source:

- `Lean/Meta/Basic.lean:1468` instantiates each forall domain with `instantiateRevRange`; the nonreducing telescope does not reduce the domain.
- `Lean/MetavarContext.lean:1319` (`MkBinding.mkBinding.handleCDecl`) executes `let type := type.headBeta` before creating each lambda or forall binder. `mkLambdaFVars` uses that function.
- `Lean/Meta/InferType.lean:188` (`inferLambdaType`) opens the lambda with `lambdaLetTelescope` and rebuilds its type with `mkForallFVars`. Thus raw hand-built lambdas alone cannot make their inferred type retain the domain syntax.
- `Lean/LocalContext.lean:554` (`LocalContext.mkBinding`) abstracts the domains without `headBeta`. Its `mkLambda` and `mkForall` wrappers therefore preserve the exact decoded domain tree.

The draft first uses `LocalContext.mkLambda` for the three public constructor arguments. It opens those raw lambda annotations without normalization, reconstructs their public forall type using `LocalContext.mkForall`, and compares the complete `encodeExpr` result with the exact genuine source `introType`. This checks names, BinderInfo, all domain subtrees, and the inferred result type. The raw bridge must be closed and independently pass `Kernel.check` and `kernelTypeEq` against that source type.

The draft then uses the explicit expression `let exactConstructor : introType := rawIntroBridge; exactConstructor`. This is a kernel-checked local type annotation, with no environment declaration or additional hypothesis. It is definitionally the same Boolean eliminator. `Meta.inferType` of the local constant reads its declared exact type. `mkForallFVars` removes the let binding because the closed result type does not depend on the let variable; this path does not rebuild the constructor's internal forall domains. The existing full `binderPlacement introType == binderPlacement (inferType introBridge)` assertion is unchanged, and the annotated expression is independently kernel-checked.

The decision-bit proof, whole parent-value equality proofs, axiom checks, owner checks, and selected declaration comparisons are unchanged. Evidence adds the raw inferred BinderInfo paths, exact source BinderInfo paths, and explicit raw-annotation/type-check facts. The final inline transport includes the complete let annotation, making the exact public type reviewable.

No Lean compiler, MCP-CI, API, or Git operation was used by the subagent. All writes are in this task directory. The candidate is uncompiled and requires root's exclusive MCP-CI audit.
