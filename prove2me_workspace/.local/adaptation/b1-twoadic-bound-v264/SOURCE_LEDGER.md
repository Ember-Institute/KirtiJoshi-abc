# Height contribution at the prime 2

Source: `lana-agents/iut` at `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`, Apache 2.0. The target is Lean 4.33.1 and Mathlib `0df444a`. The adjacent draft ledger records the original source selections and consumer edges.

| Target | Source and use |
| --- | --- |
| `TwoAdicBoundHyp` | `Iut/Tripod/CurveFacts.lean:409`; the bound on the actual provider's height contribution at 2. |
| `TwoAdicLegendreValuation` | `Iut/Tripod/TwoAdic.lean:195,206,222,239`; bounds the valuation of the Legendre $j$ in terms of the parameter and its difference from 1. |
| `FinitePlaceResidueTransport`, `TripodalPlaceTransport` | `Iut/Concrete/CurveArithmeticProved.lean:48` and `Iut/Tripod/TwoAdic.lean:95,410,412,426,434,437,442,448`; carry the residue characteristic and values of the generators across the actual field isomorphism. |
| `TripodalCompactValuation`, `TwoAdicLocalTerm` | `Iut/Implication/PrimeSelection.lean:61` and `Iut/Tripod/TwoAdic.lean:476,501,516`; bound each Tate summand by $4c$ times its local degree. |
| `twoAdicBound'`, `twoAdicBound` | `Iut/Tripod/TwoAdic.lean:568,595`; sum over all multiplicative places over 2, divide by the degree of the curve's field, and take the nonnegative bound. |
| `curveInputs_B_nonneg`, `curveInputs_heightEq_two_le` | `Iut/Tripod/CurveFacts.lean:510–512`; supply the exact field values for the future `curveInputs` constructor. `Iut/Concrete/Existence.lean:481–483` passes them to the Corollary 2.2 input. |

The target imports the valuation and group modules explicitly. In `twoAdicBound'` the final inequality uses `Nat.cast_sum` and `Nat.cast_le` directly in place of the source's inferred cast. The summation set, degree bound, statement, and final `twoAdicBound` proof are unchanged. The provider remains an input. The code bounds the unscaled contribution, whereas the paper's constant in the proof of Corollary 2.2(ii) bounds a contribution already divided by six.

| Job | Outcome | Wall time | CPU total (user + system) | Peak process tree RSS |
| --- | --- | ---: | ---: | ---: |
| `ci-019773-445b7dd9` | Hypothesis leaf | 43.13 s | 42.26 s (2.01 + 40.25) | 3.97 GiB |
| `ci-019775-92c611aa` | Hypothesis artifact | 38.76 s | 38.15 s (2.39 + 35.76) | 3.98 GiB |
| `ci-019776-913b01d7` | Valuation leaf failed: missing valuation and logarithm imports | 31.94 s | 31.15 s (1.45 + 29.70) | 2.71 GiB |
| `ci-019781-2962721c` | Valuation leaf with explicit imports | 38.17 s | 37.10 s (1.79 + 35.31) | 2.73 GiB |
| `ci-019783-f4238aa1` | Valuation artifact | 31.17 s | 30.15 s (1.62 + 28.53) | 2.73 GiB |
| `ci-019785-bf8f9df6` | Residue characteristic transport leaf | 51.82 s | 51.20 s (2.81 + 48.39) | 4.04 GiB |
| `ci-019788-1f757832` | Residue characteristic transport artifact | 53.94 s | 53.13 s (2.96 + 50.17) | 4.05 GiB |
| `ci-019790-da363b64` | Tripodal place transport leaf | 57.05 s | 56.03 s (3.07 + 52.96) | 4.08 GiB |
| `ci-019791-c3e426ea` | Tripodal place transport artifact | 52.15 s | 51.22 s (3.21 + 48.01) | 4.08 GiB |
| `ci-019795-b16ce940` | Compact subset valuation leaf | 53.91 s | 53.69 s (3.37 + 50.32) | 4.10 GiB |
| `ci-019798-526f9cf7` | Compact subset valuation artifact | 60.95 s | 60.77 s (3.68 + 57.09) | 4.11 GiB |
| `ci-019800-2dcb588c` | Local bound leaf | 48.32 s | 47.59 s (3.64 + 43.95) | 4.11 GiB |
| `ci-019805-75e84459` | Local bound artifact | 55.20 s | 54.81 s (4.17 + 50.64) | 4.11 GiB |
| `ci-019807-70ca5459` | Sum leaf failed: cast was not inferred | 54.09 s | 53.16 s (2.60 + 50.56) | 4.03 GiB |
| `ci-019810-efeece53` | Sum leaf failed: rewrite did not match under tactic transparency | 48.54 s | 48.18 s (2.75 + 45.43) | 4.10 GiB |
| `ci-019815-0cb7c262` | Sum leaf with direct cast proof | 53.56 s | 53.16 s (3.46 + 49.70) | 4.10 GiB |
| `ci-019816-348f47de` | Sum artifact | 42.42 s | 41.70 s (2.50 + 39.20) | 4.04 GiB |
| `ci-019817-876a9f76` | Field leaf | 38.12 s | 37.24 s (1.89 + 35.35) | 3.97 GiB |
| `ci-019818-bdc247cd` | Field artifact | 41.48 s | 41.20 s (2.95 + 38.25) | 4.09 GiB |
| `ci-019820-2863f9f0` | Project and axiom review passed (28 owned declarations) | 1097.46 s | 1092.24 s (961.62 + 130.62) | 8.54 GiB |

Requests and results are in `../main-chain-open-20261116/` as `b1-twoadic-*.json`; the input versions are recorded against `c8656b99` with worktree hashes. All successful leaf and artifact receipts used the live exclusive worktree, no snapshot, and exit code zero. Memory figures are the scheduler's process tree RSS; PSS was unavailable.

The review used the same exclusive workspace with no snapshot. It exited zero with `review.passed = true` and no diagnostics. Each of the three printed theorem axiom sets was `[propext, Classical.choice, Quot.sound]`. The audit checked newly generated declarations as well as the source declarations.

The independent trilingual drafts are in `readbacks/`. Cross-version kernel correspondence, the pending Chinese term, private Prove2Me acceptance, and insertion into the full `CurveInputs` constructor remain open.
