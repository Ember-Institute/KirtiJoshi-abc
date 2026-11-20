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

The bound is $[F_{\mathrm{mod}}:\mathbb Q]\leq d$. The separate bound $[F_\lambda:\mathbb Q]\leq 552960d$, a complete `CurveProviders` value, and the remaining fields of the `CurveInputs` constructor are open.

The trilingual readbacks cover [the four source declarations](readbacks/dmod-bound.md) and [the field proof](readbacks/curve-inputs-dmod-field.md). The field readback uses 紧致有界子集 for `compactly bounded subset`. [Mochizuki paper context](readbacks/paper-context.md)

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

Cross-version expression correspondence, private Prove2Me acceptance and assembly of the full input record remain open.
