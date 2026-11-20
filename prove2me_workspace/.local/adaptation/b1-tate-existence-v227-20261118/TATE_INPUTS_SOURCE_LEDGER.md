# Local Tate inputs and provider height

Source revision: `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8` (`lana-agents/iut`).

| Reference | Target declarations |
| --- | --- |
| `refer/iut/Iut/Cor312/ThetaData/ReductionNorm.lean:50,56,72,81,107,114,173,177` | Valuation ring comparison, and the norm bounds on $c_4$ and the discriminant |
| `refer/iut/Iut/Cor312/ThetaData/PlaceUnder.lean:58,68,75,86,96,101` | Transport the two bounds to the number field and deduce the strict valuation bound on $j$ |
| `refer/iut/Iut/Cor312/ThetaData/ValuationTransfer.lean:43` | `norm_emb_le_one_iff` |
| `refer/iut/Iut/Cor312/ThetaData/BadPlaceNorm.lean:49` | `twelve_ne_zero` |
| `refer/iut/Iut/Concrete/TateInputsConstruct.lean:84,90,94,102` | `EllipticCurveData.one_lt_norm_j`, `tateParameter`, `tateParameter_tateJ`, `tateInputs` |
| `refer/iut/Iut/Tripod/CurveFacts.lean:388,391,395` | `CurveProviders.tate`, `localData`, `h` |

`TateInputsSupply` uses `JExistence` for `tate` and `tateJ_eq`, and `UniformizerSupply` for `unif` and `unif_isUniformizer`. `CurveProviderHeight.tate` consumes that four-field definition. `localData` supplies the selected curve's arithmetic and Tate inputs to `LocalHeightDataAssembly`; `h` projects the result's `height`. These definitions retain the source inputs. The provider itself still has to be supplied.

The source consumers at `refer/iut/Iut/Tripod/Height.lean:558,572,582,603` compare the actual local height with the finite contribution to the height of the $j$-invariant. Their target checks are recorded below.

Target `TateInputsSupply`: leaf `ci-019516-a68e11cb`, artifact `ci-019518-c67cdc9e`, project and axiom audit `ci-019519-ea3321b8` (29 owned declarations).

Bridge results at `8a0a41da` plus the worktree changes recorded in the receipts (Lean 4.33.1, Mathlib `0df444a`, exclusive worktree, no snapshot, exit 0):

| Job | Wall time | CPU total (user + system) | Peak process tree RSS |
| --- | ---: | ---: | ---: |
| Leaf `ci-019525-0a562449` | 39.93 s | 39.19 s (2.12 + 37.07) | 3.97 GiB |
| Artifact `ci-019526-e9b9f33b` | 53.77 s | 53.12 s (2.39 + 50.73) | 4.00 GiB |
| Project and axiom audit `ci-019528-cb516fca` | 107.84 s | 107.55 s (6.34 + 101.21) | 8.53 GiB |

Scheduler RSS is reported above; PSS was unavailable. The bridge project and axiom audit returned `review.passed = true` and found only `propext`, `Classical.choice`, and `Quot.sound` in all three declarations. Complete cross-version kernel correspondence and private platform acceptance are still pending.

## Finite place contributions

`TatePoleOrder` uses the norm formula from `TateCurvesTheta/TateCurve/JInvariant.lean:108`, the natural power form of the normalized order from `TateCurvesTheta/QParameter/NormalizedOrder.lean:168`, the valuation comparisons from `Iut/Concrete/ThetaLocalConstruct/Ordp.lean:286,323`, and the pole order identity from `Iut/Tripod/TwoAdic.lean:352`. The consumer `posLog_j_eq_of_mem_badAll` is from `Iut/Tripod/Height.lean:558`. The target uses the existing `Tripod` finite place arithmetic declarations and fixes the base of the outer integer power explicitly for the target elaborator.

`GoodReductionHeight` uses `Iut/Cor312/ThetaData/ReductionNorm.lean:121,162` for the integral norm bounds and `Iut/Concrete/CurveArithmeticProved.lean:80,95` for the stable reduction comparison. Their consumer is `posLog_j_eq_zero_of_not_mem_badAll`, from `Iut/Tripod/Height.lean:572`. Both local formulas feed the finite sum identity at `Height.lean:582`.

All runs below use the exclusive target worktree at `8a0a41da` plus manifest inputs. Complete source hashes, diagnostics, arguments, and resource records are in the corresponding `main-chain-open-20261116` receipts.

| Job | Outcome | Wall time | CPU total (user + system) | Peak process tree RSS |
| --- | --- | ---: | ---: | ---: |
| `ci-019539-bd6f0b18` | Leaf failed: residue characteristic ambiguity and missing order power lemma | 63.07 s | 62.36 s (2.60 + 59.76) | 4.04 GiB |
| `ci-019542-d8b833fe` | Leaf failed: rewrite selected the inner power | 43.92 s | 43.29 s (2.42 + 40.87) | 4.02 GiB |
| `ci-019545-ca3c98db` | Tate pole order leaf passed | 43.10 s | 42.23 s (2.48 + 39.75) | 4.00 GiB |
| `ci-019548-b30800a3` | Good reduction height leaf passed | 40.97 s | 40.18 s (2.51 + 37.67) | 4.02 GiB |
| `ci-019551-fbd5f56e` | Tate pole order artifact passed | 42.97 s | 42.22 s (2.76 + 39.46) | 4.07 GiB |
| `ci-019552-dd8360db` | Good reduction height artifact passed | 42.77 s | 42.38 s (2.95 + 39.43) | 4.09 GiB |
| `ci-019553-a38c784e` | Project and axiom audit passed (10 + 5 owned declarations) | 331.41 s | 330.74 s (230.98 + 99.76) | 8.54 GiB |

The aggregate review exited with code 0, returned `review.passed = true`, used the live worktree without a snapshot, and reported no diagnostics. Peak physical memory is scheduler RSS; PSS was unavailable. Cross-version correspondence and platform acceptance remain pending.

## Finite height sum

`FiniteHeightSum` uses `Iut/Implication/PrimeSelection.lean:187` to clear the field-degree denominator in the assembled local height, then uses `Iut/Tripod/Height.lean:582` to identify the sum with `finHeight (P.curve x).E.j`. Both previously adapted local formulas are consumed directly. The next consumer is `Iut/Tripod/Height.lean:603`.

| Job | Outcome | Wall time | CPU total (user + system) | Peak process tree RSS |
| --- | --- | ---: | ---: | ---: |
| `ci-019565-ab7fd8e4` | Leaf passed | 40.72 s | 40.29 s (2.76 + 37.53) | 4.09 GiB |
| `ci-019567-3b9e0ec7` | Artifact passed | 44.55 s | 44.21 s (2.95 + 41.26) | 4.10 GiB |
| `ci-019571-421f1ca2` | Project and axiom audit passed (10 owned declarations) | 222.55 s | 215.23 s (118.25 + 96.98) | 8.54 GiB |

All three receipts record the live exclusive worktree with no snapshot and exit code zero. The aggregate review returned `review.passed = true` without diagnostics. Physical memory figures are scheduler RSS; PSS was unavailable. Source correspondence across toolchain versions and platform acceptance are pending.

## Finite height under a field isomorphism

`FiniteHeightMapEquiv` uses the ideal comap and valuation lemmas from `Iut/Cor312/ThetaData/GalCompletion.lean:179,188,209,331` to prove the finite place bijection and transport identities from `Iut/Tripod/TwoAdic.lean:48,57,64,72,85`. The final consumer is `Iut/Tripod/Height.lean:110`; it reindexes the sum using the existing `finHeight` definition. The normalization theorem at `Height.lean:603` uses this equality to transport from the tripodal field to the parameter field. The finite extension formula at `Height.lean:199` remains a separate dependency.

| Job | Outcome | Wall time | CPU total (user + system) | Peak process tree RSS |
| --- | --- | ---: | ---: | ---: |
| `ci-019580-7e1afb67` | Leaf passed | 38.52 s | 38.10 s (2.70 + 35.40) | 4.03 GiB |
| `ci-019581-466eeaf8` | Artifact passed | 38.07 s | 37.14 s (2.39 + 34.75) | 3.93 GiB |
| `ci-019582-8d08ff0e` | Project and axiom audit passed (14 owned declarations) | 209.94 s | 209.09 s (118.00 + 91.09) | 8.54 GiB |

These jobs used the live exclusive worktree, with no snapshot and exit code zero. The aggregate review returned `review.passed = true` with no diagnostics. The final theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. Memory figures are the scheduler's process tree RSS; PSS was unavailable. The three-language draft and source locations are recorded; cross-version correspondence and private platform acceptance remain pending.

## Relative places and valuations

`Source_TripodPlaceUnder` ports `Iut/Cor312/ThetaData/PlaceUnder.lean:30–50` and `Iut/Tripod/Height.lean:141–148`. The contraction of the prime defines the place below and is used in the finite place partition of `Height.lean:199`.

`Source_TripodRelativeValuation` ports `Iut/Concrete/ThetaLocalConstruct/EmbedCompletion.lean:161–163`, `Iut/Concrete/ThetaLocalConstruct/Ordp.lean:168–169,188–190`, and `Iut/Cor312/ThetaData/ValuationTransfer.lean:65–77`. The relative indices are consumed by the tower identities and the valuation equality feeds the local absolute value formula. The target explicitly marks the two abbreviations `noncomputable`; their bodies and the proof bodies are unchanged.

| Job | Outcome | Wall time | CPU total (user + system) | Peak process tree RSS |
| --- | --- | ---: | ---: | ---: |
| `ci-019588-7aa6d194` | Place below leaf passed | 37.72 s | 37.16 s (2.26 + 34.90) | 3.83 GiB |
| `ci-019590-01d28061` | Relative valuation leaf failed: missing `noncomputable` on both abbreviations | 37.25 s | 36.16 s (1.81 + 34.35) | 3.92 GiB |
| `ci-019591-c3dfcd9f` | Relative valuation leaf passed with explicit modifiers | 41.80 s | 41.22 s (2.62 + 38.60) | 3.97 GiB |
| `ci-019594-8287c320` | Place below artifact passed | 36.92 s | 36.12 s (2.09 + 34.03) | 3.82 GiB |
| `ci-019596-8784af6c` | Relative valuation artifact passed | 41.03 s | 40.17 s (2.35 + 37.82) | 3.91 GiB |
| `ci-019597-37260aa0` | Project and axiom audit passed (9 + 5 owned declarations) | 315.29 s | 314.27 s (226.60 + 87.67) | 8.54 GiB |

The aggregate review used the live exclusive worktree without a snapshot, exited with code zero, and returned `review.passed = true` with no diagnostics. Its process tree memory measurement was RSS; PSS was unavailable. Cross-version correspondence and private platform acceptance remain pending.

## Finite height scaling under an extension

`Source_TripodRelativeDegreeTower` selects `Iut/Concrete/ThetaLocalConstruct/Ordp.lean:155–166,171–186,192–217` and `Iut/Tripod/Height.lean:150–160`. `Source_TripodRelativeDegreeSum` uses `Ordp.lean:243–275` and `Height.lean:187–197`. `Source_TripodRelativeAbsoluteValue` uses `Height.lean:162–185` with the mapped `Tripod.log_apply_eq`. `Source_TripodFiniteHeightExtension` selects `Height.lean:199–237`; the two finite support witnesses have explicit set types for the target elaborator. The statement and the grouping by place below follow the source. The consumer is `Height.lean:603`.

| Job | Outcome | Wall time | CPU total (user + system) | Peak process tree RSS |
| --- | --- | ---: | ---: | ---: |
| `ci-019604-10666b16` | Tower leaf passed | 38.20 s | 38.47 s (3.37 + 35.10) | 4.06 GiB |
| `ci-019608-264a2825` | Tower artifact passed | 43.26 s | 42.16 s (2.31 + 39.85) | 3.92 GiB |
| `ci-019610-3ab8e620` | Degree sum leaf passed | 39.52 s | 39.15 s (2.45 + 36.70) | 4.04 GiB |
| `ci-019613-f8e9ed36` | Degree sum artifact passed | 38.08 s | 37.12 s (2.45 + 34.67) | 3.92 GiB |
| `ci-019615-d3bb0b5f` | Absolute value leaf passed | 40.06 s | 39.16 s (2.32 + 36.84) | 3.91 GiB |
| `ci-019617-c2f92d61` | Absolute value artifact passed | 37.23 s | 37.12 s (2.89 + 34.23) | 4.05 GiB |
| `ci-019620-8ba656ad` | Extension leaf failed: two finite support type rewrites | 42.76 s | 42.10 s (2.53 + 39.57) | 3.99 GiB |
| `ci-019622-5072e1c9` | Extension leaf passed with explicit set types | 35.90 s | 35.15 s (2.42 + 32.73) | 3.94 GiB |
| `ci-019625-c13b8978` | Extension artifact passed | 41.35 s | 41.11 s (2.79 + 38.32) | 4.05 GiB |
| `ci-019627-402f9dc7` | Project and axiom audit passed (7 + 2 + 2 + 1 owned declarations) | 553.51 s | 552.74 s (454.03 + 98.71) | 8.54 GiB |

The aggregate review used the live exclusive worktree without a snapshot, exited with code zero, and returned `review.passed = true` with no diagnostics. Both printed theorem axiom sets were `[propext, Classical.choice, Quot.sound]`. Peak physical memory is the scheduler's process tree RSS; PSS was unavailable. Cross-version correspondence and private platform acceptance remain pending.

## Tripodal field and height normalization

`FieldInvariant` defines the field generated by the rational 2-torsion coordinates and `j` (`Iut/Concrete/Invariants.lean:198–214`). `FieldLegendreFacts` supplies the point equations and invariant formulas (`Iut/Tripod/Legendre.lean:30–190`). `FieldIdentification` proves the generating field is `ℚ(λ)` (`Iut/Tripod/CurveFacts.lean:164–253`). `FieldTransport` supplies the equivalence and degree (`Iut/Tripod/TwoAdic.lean:384–432`); `JTransport` proves the generator and `j` use the same maps (`Iut/Tripod/Height.lean:249–258,540–556`). `HeightNormalization` combines these with the earlier finite height sum and transport lemmas at `Height.lean:603`. Its project consumer is `Source_TripodProviderAuxiliaryHeight`, which identifies `P.h` and `auxiliaryHeight` and preserves the factor `1/6`. The next source consumer is `Height.lean:791`.

| Job | Outcome | Wall time | CPU total (user + system) | Peak process tree RSS |
| --- | --- | ---: | ---: | ---: |
| `ci-019645-62d97604` | Field definition leaf | 27.21 s | 27.09 s (2.31 + 24.78) | 2.88 GiB |
| `ci-019649-1879944b` | Field definition artifact | 26.47 s | 26.10 s (1.64 + 24.46) | 2.87 GiB |
| `ci-019651-e0be0a9a` | Legendre facts leaf | 24.72 s | 24.09 s (1.70 + 22.39) | 2.73 GiB |
| `ci-019652-cd0b9e9f` | Legendre facts artifact | 26.35 s | 26.71 s (2.57 + 24.14) | 2.82 GiB |
| `ci-019654-4d2bd519` | Field identification leaf | 39.21 s | 39.38 s (3.51 + 35.87) | 4.09 GiB |
| `ci-019657-435c2cb1` | Field identification artifact | 42.42 s | 42.50 s (3.75 + 38.75) | 4.09 GiB |
| `ci-019660-3ede38b6` | Field transport leaf | 40.12 s | 39.13 s (2.23 + 36.90) | 3.96 GiB |
| `ci-019661-8b1397e8` | Field transport artifact | 36.45 s | 36.23 s (2.50 + 33.73) | 4.08 GiB |
| `ci-019662-85ee9c7d` | `j` transport leaf | 37.43 s | 37.21 s (2.76 + 34.45) | 4.08 GiB |
| `ci-019667-6e77aa0f` | `j` transport artifact | 40.78 s | 40.18 s (2.76 + 37.42) | 4.07 GiB |
| `ci-019670-6d60724c` | Height normalization leaf | 39.74 s | 39.22 s (3.21 + 36.01) | 4.10 GiB |
| `ci-019672-caec1b27` | Height normalization artifact | 39.26 s | 39.11 s (3.90 + 35.21) | 4.11 GiB |
| `ci-019674-cd6219ef` | Auxiliary height identity leaf | 39.02 s | 38.15 s (2.28 + 35.87) | 3.97 GiB |
| `ci-019676-c29a34ff` | Auxiliary height identity artifact | 40.53 s | 40.15 s (2.39 + 37.76) | 4.08 GiB |

The leaf and artifact receipts use the exclusive worktree, have no snapshot and report exit code zero. Diagnostics are the deprecation of `Set.mem_setOf_eq` and tactic simplification suggestions. The complete requests and results, including input hashes and actual arguments, are stored under `main-chain-open-20261116/` as `b1-tripod-*-v260-*.json`. Memory figures use scheduler process tree RSS; PSS was unavailable. The trilingual readback covers `tripodalFieldOf_eq`, `tpdEquiv_jT`, and `h_eq_finHeight_div`. [Readback](tripod-height-normalization-readback.md)

Aggregate review `ci-019679-3acf973e` passed the project gates and checked 84 owned declarations. It returned exit code zero and `review.passed = true`, with no diagnostics. The four printed axiom sets contain only `propext`, `Classical.choice`, and `Quot.sound`. Worker wall time was 890.63 s; CPU time was 889.68 s (787.78 s user and 101.90 s system); peak RSS was 8.54 GiB. The receipt reports the exclusive worktree and no snapshot.

## Legendre height comparison

`LegendreHeightHyp` follows `Iut/Tripod/CurveFacts.lean:403` with the original two directions of the bounded discrepancy relation. `legendreHeight` retains the statement and proof text from `Iut/Tripod/Height.lean:791` and resolves four numerical inputs to existing project proofs through private aliases. The zero-`j` alias specializes the generic source fact to the actual tripod generator. The bounds retain their original constants, `log 2 / 3` and `c * |V| + c + log 2 / 3`. `canonicalLegendreHeightComparison_of_provider` consumes both via the identity with `auxiliaryHeight`. The original comparison is also an input to `curveInputs`; that constructor and provider existence are separate open obligations.

| Job | Outcome | Wall time | CPU total (user + system) | Peak process tree RSS |
| --- | --- | ---: | ---: | ---: |
| `ci-019692-a0d2bc81` | Hypothesis leaf | 46.33 s | 45.23 s (2.03 + 43.20) | 3.98 GiB |
| `ci-019696-7e1761b8` | Hypothesis artifact | 87.38 s | 86.60 s (2.68 + 83.92) | 4.08 GiB |
| `ci-019697-036dc742` | Comparison leaf | 43.67 s | 43.21 s (3.26 + 39.95) | 4.11 GiB |
| `ci-019699-b8097629` | Comparison artifact | 43.07 s | 42.09 s (2.84 + 39.25) | 4.11 GiB |
| `ci-019701-c6712876` | Canonical consumer leaf | 40.22 s | 39.26 s (2.00 + 37.26) | 3.97 GiB |
| `ci-019703-ab60cb17` | Canonical consumer artifact | 41.42 s | 41.20 s (2.70 + 38.50) | 4.10 GiB |
| `ci-019704-59595fa4` | Project and axiom audit (9 owned declarations) | 454.97 s | 454.38 s (350.35 + 104.03) | 8.55 GiB |

All seven results report the exclusive worktree, no snapshot and exit code zero, with no diagnostics. The aggregate returned `review.passed = true`; both printed axiom sets are `[propext, Classical.choice, Quot.sound]`. Memory figures use scheduler process tree RSS; PSS was unavailable. The three Legendre readbacks use the approved terminology and identify the two source declarations and the canonical consumer. [Trilingual readbacks](legendre-height-readbacks/) Cross-version correspondence and private platform acceptance remain pending.
