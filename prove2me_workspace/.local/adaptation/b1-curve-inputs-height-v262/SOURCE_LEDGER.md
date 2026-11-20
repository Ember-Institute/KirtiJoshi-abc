# Actual height fields for CurveInputs

Source: `lana-agents/iut` at `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`, Apache 2.0; Genl at `ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf`, Apache 2.0. The target uses Lean 4.33.1 and Mathlib `0df444a`. The frozen Genl source and numbered source matches are recorded in the producer and consumer trace. This ledger describes the target integration; the adjacent JSON trace preserves the earlier draft analysis.

| Target | Source and consumer |
| --- | --- |
| `DiscrepancyEquiv.ge` | Genl `Genl/Mathlib/Order/BoundedDiscrepancy.lean:141`. The proof selects the bound that puts the Weil height on the left. |
| `NorthcottHyp`, `northcott`, `northcott_of_equiv` | `Iut/Tripod/Basic.lean:425,451,457`. The source statements and proof bodies are retained, with imports and namespaces adapted. The closed `northcottHyp` uses the existing concrete `boundedDegreeFiniteness` proof. |
| `curveInputs_height_eq` | `Iut/Tripod/CurveFacts.lean:503`. The same provider's curve, arithmetic and Tate data compute the prescribed height. `Existence.lean:477` forwards it to `c2` (`Corollary22.lean:404`). |
| `curveInputs_htCan_equiv` | `CurveFacts.lean:508` uses `legendreHeight P K` with the original scale of one sixth. This proof applies to the entire set, independent of the degree bound. `Corollary23.lean:100` uses the comparison to recover the bound for Weil height. |
| `curveInputs_northcott` | `CurveFacts.lean:509` combines the same comparison with Northcott. `Corollary23.lean:76` uses it to show that the low height part of the exceptional set is finite. |

The latter three declarations give the exact field values for `h := P.h`; the full `curveInputs` structure and the actual supplier's existence remain open. The trilingual readbacks cover the exact local height, Weil height comparison, and Northcott field declarations. [Trilingual readbacks](readbacks/) Source text matches, target builds and the axiom review do not constitute a cross-version kernel correspondence or acceptance on Prove2Me.

| Job | Outcome | Wall time | CPU total (user + system) | Peak RSS |
| --- | --- | ---: | ---: | ---: |
| `ci-019720-f1c2784d` | Discrepancy leaf | 18.02 s | 17.05 s (1.04 + 16.01) | 1.76 GiB |
| `ci-019723-db46e85f` | Discrepancy artifact | 20.23 s | 20.08 s (1.15 + 18.93) | 1.88 GiB |
| `ci-019724-4b56afd4` | Northcott leaf | 39.37 s | 39.14 s (2.85 + 36.29) | 4.04 GiB |
| `ci-019727-a490ca8f` | Northcott artifact | 42.13 s | 41.22 s (2.18 + 39.04) | 3.93 GiB |
| `ci-019729-336c4d0d` | Height fields leaf | 50.53 s | 49.29 s (1.87 + 47.42) | 3.96 GiB |
| `ci-019735-118f44c3` | Height fields artifact | 51.80 s | 51.07 s (2.53 + 48.54) | 4.08 GiB |
| `ci-019738-613bb893` | Review failed: unknown identifier `when` in the audit script | 141.78 s | 140.30 s (5.45 + 134.85) | 8.38 GiB |
| `ci-019746-6abe9a47` | Review passed after using the existing `unless` style | 477.10 s | 475.30 s (345.48 + 129.82) | 8.55 GiB |

Requests and results are in `../main-chain-open-20261116/` as `b1-curve-inputs-height-*.json`. They record input hashes against `c8656b99` and the exclusive Prove2Me worktree with no snapshot. The successful review exited zero with `review.passed = true`, no diagnostics, and eight owned declarations audited. The five printed theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. Memory figures are the scheduler's process tree RSS; PSS was unavailable.
