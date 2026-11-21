# Field of moduli degree for CurveInputs

The four declarations below retain the source statements and proof bodies. The adaptation uses existing local imports, including `FieldIdentification` for the membership of $j$ in the Legendre point field and the algebra equivalence on that field. The line numbers refer to `refer/iut/Iut/Tripod/CurveFacts.lean` at reference revision `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`. Its local SHA-256 is `99c2785fdfdfb7a7e9d5f584a6d19ad15ee8a21d25e45e6ca26e125b946857fb`. The source is Apache-2.0. [License](../foundation-reference-carriers-20261115/LICENSE.iut.Apache-2.0)

| Declaration in `AbcAdaptation.Tripod` | Source line | Direct use |
| --- | --- | --- |
| `fieldOfModuli_le` | 179 | Supplies the field inclusion for `dmod_le`. |
| `isIntegral_genC` | 184 | Supplies the algebraicity for finite dimensionality in `dmod_le`. |
| `finrank_adjoin_genC` | 203 | Identifies the dimension of the containing field in `dmod_le`. |
| `dmod_le` | 207 | Bounds the field of moduli for the curve used in `curveInputs_dmod_le`. |
| `curveInputs_dmod_le` | 507 | Proves the field type at `Iut/Concrete/Existence.lean:406` using the same provider's torsion finiteness proofs and the degree locus restriction. |

The source constructor at `Iut/Tripod/Main.lean:123` consumes this field for the same curve to bound the moduli degree of the initial theta data. `Iut/Concrete/Main.lean:68` carries the bound into `ThetaDataExistence`. `Iut/Implication/Corollary22.lean:536`–`541` uses it in the coefficient estimates for `c2`.

The field bound is $[F_{\mathrm{mod}}:\mathbb Q]\leq d$. The local 21-field constructor uses `curveInputs_dmod_le P K d` for the curve `P.curve x`. The existence of a complete `CurveProviders` value remains open. [Constructor](../../../Solutions/Source_TripodCurveInputs.lean#L39)

The trilingual readbacks cover the four source declarations and the field proof. They use 模域 for `field of moduli` and 紧致有界子集 for the paper's `compactly bounded subset`. The field proof uses the reference code's inequalities at the specified places. [Four source declarations](readbacks/dmod-bound.md) · [Field proof](readbacks/curve-inputs-dmod-field.md) · [Mochizuki paper context](readbacks/paper-context.md)

## MCP-CI acceptance

Both versions used Lean `v4.33.1`, Mathlib `0df444a` and worktree HEAD `8547c768`. Version 268 adds source notices to the two Lean files and retains the commands checked in version 267. Each receipt records the exact input hashes and command. All jobs used the live exclusive workspace with a null snapshot ID and exited zero. The bound leaf and its artifact compilation report the source tactic's `Try this` suggestion.

| Job | Check | Wall time (s) | CPU total (user + system, s) | Peak RSS (GiB) |
| --- | --- | ---: | ---: | ---: |
| `ci-019833-20c22b3f` | v267 bound leaf | 45.92 | 45.05 (2.46 + 42.59) | 3.97 |
| `ci-019834-19167416` | v267 bound artifact | 40.43 | 40.32 (3.29 + 37.03) | 4.08 |
| `ci-019836-2cb1ea34` | v267 field leaf | 46.97 | 46.19 (2.54 + 43.65) | 3.96 |
| `ci-019838-eac25972` | v267 field artifact | 40.31 | 40.30 (2.76 + 37.54) | 4.08 |
| `ci-019839-fa56a203` | v267 aggregate and axiom review | 322.64 | 322.46 (230.82 + 91.64) | 8.54 |
| `ci-019846-dd240a6f` | v268 bound leaf | 49.85 | 49.32 (2.65 + 46.67) | 4.07 |
| `ci-019848-93dd946e` | v268 bound artifact | 45.40 | 45.44 (3.18 + 42.26) | 4.08 |
| `ci-019849-9fe8484f` | v268 field leaf | 42.84 | 42.18 (2.53 + 39.65) | 3.98 |
| `ci-019850-a74e615c` | v268 field artifact | 45.92 | 45.21 (2.87 + 42.34) | 4.03 |
| `ci-019852-9e4947ad` | v268 aggregate and axiom review | 356.00 | 354.64 (246.64 + 108.00) | 8.54 |

Memory figures are the MCP-CI process tree RSS. PSS is unavailable. Host availability came from `degraded:linux_proc`. The final review checked the project Checks, ImportAudit, Act1Scene1 aggregate and AxiomAudit imports, and verified all five declarations owned by the two new modules. It returned no diagnostics and reported `propext`, `Classical.choice` and `Quot.sound` as their only axioms. [Audit input](RequiredDmodGates.lean) · [Final receipt](../main-chain-open-20261116/b1-dmod-audit-review-v268-result.json)

## Private Prove2Me acceptance

The private solution in submission `c7e58163-7fc3-407f-a833-29f8c9f141bb` received `ACCEPTED`. Node `da29ead8-b30e-404f-9323-dc7d554cc83e` returned `Proved` under Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The returned statement, preamble, natural-language statement and source match the publication packet. The submission receipt contains the SHA-256 of the archived solution. [Packet](platform/dmod_le.problem.json) · [Solution](platform/solution.lean) · [Submission verdict](platform/receipts/dmod_le/verification-result.json) · [Node readback](platform/receipts/dmod_le/final-item.json)

MCP-CI `ci-026188-40e6e1db` checked the exact solution at the published type in the exclusive worktree. It exited zero after 279.44 s wall time and 274.29 s CPU time (3.48 s user and 270.81 s system), with 4.07 GiB peak process-tree RSS. PSS is unavailable. Both declarations use only `propext`, `Classical.choice`, and `Quot.sound`. The review reports a linter suggestion on the source proof's `haveI`. [Review receipt](platform/ci-026188-40e6e1db.result.json)

## Cross-version correspondence

The source runner uses Lean `4.35.0-rc3` to replay the four source commands and the constructor assignment at line 507 with the supplied curve as its expected type. The Lean `4.33.1` review checks full kernel types and both proof terms for all five records. The public binders agree. Three records differ in the binders inside elaborated library instances and their types are definitionally equal. The source field proof infers the torsion finiteness witnesses used by `P.curve`, and the target field proof passes the two witnesses explicitly. Both proof terms check at the full target type. The review also inspects the compiled record constructor and checks the selected field argument at that type. All five comparisons and the field argument use only `propext`, `Classical.choice`, and `Quot.sound`. [Comparison summary](cross-version/cross-version-result.json) · [Source expressions](cross-version/source-facts.jsonl.gz) · [Kernel evidence](cross-version/cross-version-expressions.jsonl.gz)

Both jobs used exclusive workspace HEAD `3da69dc8`, null snapshot IDs and the source paths in the respective receipts. Memory is the MCP-CI process-tree RSS. PSS and the degraded flag are unavailable.

| Job | Exit | Wall (s) | CPU total (user + system, s) | Peak RSS (GiB) | Diagnostic |
| --- | ---: | ---: | ---: | ---: | --- |
| [`ci-026214-82831d8e`](cross-version/ci-026214-82831d8e.result.json) | 0 | 202.61 | 200.66 (8.60 + 192.06) | 8.22 | The source `haveI` linter suggestion |
| [`ci-026233-130a078f`](cross-version/ci-026233-130a078f.result.json) | 0 | 68.40 | 68.38 (5.93 + 62.45) | 4.81 | Five comparisons and the constructor field passed |
