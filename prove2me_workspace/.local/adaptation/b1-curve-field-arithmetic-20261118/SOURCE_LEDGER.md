# Tripod curve input adaptation

The source is [lana-agents/iut](https://github.com/lana-agents/iut/tree/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8) at revision `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`, under Apache-2.0.
The target was checked at worktree HEAD `96176c1b` plus the changes listed in each receipt, with Lean `v4.33.1` and Mathlib `0df444a`.

| Reference path | Source range | Source SHA-256 |
| --- | --- | --- |
| `Iut/Tripod/CurveFacts.lean` | 63–80, 255–354, 419–520 | `99c2785fdfdfb7a7e9d5f584a6d19ad15ee8a21d25e45e6ca26e125b946857fb` |
| `Iut/Concrete/Existence.lean` | 95, 390–493 | `7f13d5adf2ed0b72f2b0f78059fd7f1731422ce24c7a66deb3b2902a3ba3b314` |
| `Iut/Concrete/Invariants.lean` | 182, 225 | `adc5100b9cb75abacee2387c5d83696c74a1c8548e4ea44a835edb61cf29ffe7` |
| `Iut/Concrete/CyclicSubgroup.lean` | 27 | `e8bd2657d9d5db53ce1b95193f13942ef247c184b07aa1a54950a1416fb4173b` |
| `Iut/Cor312/ThetaData/Orbicurve.lean` | HasCoreUniversally | `b21404347fe9ea6557bf72421328bfd9e522a66c912b8c97d94dbe09a1259b0b` |
| `Iut/Concrete/ModEllRepGalois.lean` | 147–190 | `33f4605102e7e82c3030e63970c9ac86062395fd865d1344d93e1cf7ebc6123f` |
| `Iut/Concrete/SL2Image.lean` | 229–239 | `fd69ae35a4f7590947b52b39e644b7d3fcb5fe067fbdb50b376c358e4413d317` |

| Target declaration | Direct consumer |
| --- | --- |
| `deg_le`, `curveInputs_deg_le` | `curveInputsOfSL2Image.deg_le`, then `Corollary22Inputs.localData_deg_le` |
| `logDiff_eq`, `curveInputs_logDiff_eq` | `curveInputsOfSL2Image.logDiff_eq`. The reference P7 constructor consumes this field at `Iut/Tripod/Main.lean:123`. |
| `curveInputsOfSL2Image` and `CurveInputs.toCorollary22Inputs` | `Corollary22Inputs`, with all source height, cyclic, image, core and conductor fields carried by the actual curve. The reference root supplies these inputs at `Iut/Tripod/Main.lean:137`. |
| `Sketch_Tripod_sl2Image.solution` | Converts the local height support conditions to the Tate input conditions and invokes the exact open `EllipticCurveData.sl_le_range_of` child. |
| `hasCyclicSubgroup_of_stable_line`, `exists_mulVec_ne_smul_of_not_hasCyclicSubgroup` | The no-invariant-line input in the source proof at `Iut/Concrete/SL2Image.lean:239`. |

The conditional constructor takes `SL2ImageHyp P` as an explicit argument. The reference constructor uses `sl2Image P` at that point. The two open theorem files record the parent and child statements. The sketch uses the child and the closed constructor imports neither open statement.

The [independent read-backs](readbacks/) cover English, Simplified Chinese and Japanese. The Chinese translations of `compactly bounded subset` and `uniformizer` remain pending.

## MCP-CI receipts

Jobs use the live exclusive workspace and a null snapshot ID. The [structured receipts](receipts/) give the full input versions, exact arguments and diagnostics. Memory is process tree RSS, with PSS unavailable. Host availability came from `degraded:linux_proc`.

| Job | Check | Exit | Wall (s) | CPU total (user + system, s) | Peak RSS (GiB) |
| --- | --- | --- | ---: | ---: | ---: |
| `ci-020052-0b04aeb1` | curve-constructor-1 | succeeded (0) | 82.27 | 66.34 (2.25 + 64.09) | 4.03 |
| `ci-020059-9d0b4897` | curve-constructor-artifact | succeeded (0) | 132.00 | 125.93 (2.93 + 123.00) | 4.10 |
| `ci-019993-f2db105f` | curve-facts-1 | failed (1) | 85.93 | 80.77 (4.48 + 76.29) | 4.11 |
| `ci-020004-c19e8916` | curve-facts-2 | succeeded (0) | 88.72 | 88.12 (2.78 + 85.34) | 4.10 |
| `ci-020006-ff04b087` | curve-facts-artifact | succeeded (0) | 87.53 | 86.21 (2.48 + 83.73) | 4.00 |
| `ci-019973-1e0bf149` | curve-inputs-1 | timeout | 180.99 | unknown | unknown |
| `ci-019984-a3028e66` | curve-inputs-2 | succeeded (0) | 81.54 | 77.91 (3.15 + 74.76) | 4.04 |
| `ci-019990-100796fd` | curve-inputs-artifact | succeeded (0) | 65.23 | 65.09 (3.81 + 61.28) | 4.11 |
| `ci-020088-61d7ef79` | curve-inputs-axioms-1 | succeeded (0) | 336.05 | 334.52 (287.40 + 47.12) | 4.72 |
| `ci-020064-06102faa` | curve-inputs-review-1 | timeout | 960.07 | unknown | unknown |
| `ci-019900-66bb0247` | degree-1 | failed (1) | 50.07 | 47.92 (4.92 + 43.00) | 4.09 |
| `ci-019907-b640a66e` | degree-2 | succeeded (0) | 62.55 | 60.18 (7.12 + 53.06) | 4.10 |
| `ci-019913-7500ee55` | degree-artifact | succeeded (0) | 74.95 | 73.24 (6.01 + 67.23) | 4.09 |
| `ci-019901-60c56b16` | different-1 | succeeded (0) | 47.73 | 43.91 (2.81 + 41.10) | 4.07 |
| `ci-019906-daf8fa57` | different-2 | succeeded (0) | 61.23 | 57.50 (3.46 + 54.04) | 4.07 |
| `ci-019914-43739e04` | different-artifact | succeeded (0) | 72.20 | 70.19 (3.29 + 66.90) | 4.08 |
| `ci-019974-4d1d422c` | different-current-artifact | succeeded (0) | 257.35 | 204.46 (4.50 + 199.96) | 4.09 |
| `ci-019953-e476e465` | field-consumers-1 | timeout | 180.08 | unknown | unknown |
| `ci-019964-9fc67d24` | field-consumers-2 | succeeded (0) | 258.03 | 225.89 (4.04 + 221.85) | 4.07 |
| `ci-019985-d228cdc3` | field-current-artifact | succeeded (0) | 79.57 | 76.52 (4.07 + 72.45) | 3.97 |
| `ci-019919-f0b9774c` | invariants-1 | failed (1) | 103.13 | 101.23 (2.78 + 98.45) | 4.00 |
| `ci-019924-34e37122` | invariants-2 | succeeded (0) | 94.62 | 93.02 (3.09 + 89.93) | 4.05 |
| `ci-019963-7432648c` | invariants-artifact | succeeded (0) | 255.46 | 223.26 (3.73 + 219.53) | 3.96 |
| `ci-020087-c48ae3d1` | project-gates-1 | succeeded (0) | 92.28 | 90.41 (4.65 + 85.76) | 7.80 |
| `ci-019994-ba50ff91` | sl2-general-statement-1 | succeeded (0) | 82.59 | 77.57 (2.28 + 75.29) | 3.98 |
| `ci-019999-4005305d` | sl2-general-statement-artifact | succeeded (0) | 102.40 | 98.24 (3.42 + 94.82) | 4.09 |
| `ci-020054-054f693d` | sl2-tripod-sketch-1 | failed (1) | 78.74 | 62.77 (2.48 + 60.29) | 4.10 |
| `ci-020060-c7613467` | sl2-tripod-sketch-2 | succeeded (0) | 128.02 | 122.68 (2.68 + 120.00) | 4.00 |
| `ci-020053-f85db723` | sl2-tripod-statement-1 | succeeded (0) | 78.92 | 64.19 (2.79 + 61.40) | 4.07 |
| `ci-019995-2f1cd4dd` | stable-line-1 | succeeded (0) | 82.53 | 77.65 (2.53 + 75.12) | 4.05 |
| `ci-020000-66ec82d4` | stable-line-artifact | succeeded (0) | 105.79 | 103.63 (3.92 + 99.71) | 4.11 |

The degree and invariant first passes reported missing declarations or imports. The CurveFacts first pass lacked the provider-height import. The first tripod sketch needed a qualified residue-characteristic name. Both initial timeout receipts for the field consumers and CurveInputs lack logs and final CPU or memory measurements.

The combined review timed out without a diagnostic. The project review then passed for Checks, ImportAudit, Act1Scene1 and AxiomAudit. The separate review checked 100 declarations across eight modules, with only `propext`, `Classical.choice` and `Quot.sound` in the reported axiom closures.

Some historical degree and different-degree receipts recorded `[WARNING]` in the source hash field. The final axiom review manifest gives the actual current source hashes for both modules.

Full cross-version correspondence and private platform acceptance remain open. The general SL₂ image proof and the P7 existence constructor remain separate source obligations.
## SL₂ image and torsion degree

| Reference path | Source range | Direct consumer |
| --- | --- | --- |
| `Iut/Tripod/SL2Generation.lean` | Matrix generation | `sl_le_range_of_dvd_card`, used in the reduction of `SL2Image.lean:229` |
| `Iut/Concrete/Existence.lean` and `Iut/Concrete/ModEllRepGalois.lean` | Kernel fixed field, torsion descent and cardinalities | `ramificationIdx'_dvd_card_gal` and `card_torsion_curveKw_ge` in the same torsion field |
| `Iut/Concrete/SL2Image.lean` and `Iut/Cor312/ThetaData/PlacesOver.lean` | Relative ramification, primes above and range cardinality | The reduction of `prime_dvd_card_range` at line 217 to `prime_dvd_ramificationIdx` at line 162 |
| `Iut/Anabelian/TateTorsion.lean` and `Iut/Cor312/ThetaData/TateStructure.lean` | Quotient exponents, finiteness and the root class | `prime_dvd_ramificationIdx_of_tateStructure`, with the valuation comparison of `SL2Image.lean:180–213` |
| `Iut/Tripod/TorsionDegree.lean` | Galois action on coordinates, representation kernel and degree bound | The three- and five-torsion degree bounds of `curveInputsOfSL2Image`. The pointwise basis existence in `TorsionBasis.lean:31` is open. |

The closed SL₂ and torsion-degree helpers use only `propext`, `Classical.choice`, and `Quot.sound`. Review jobs `ci-020226-796c0556` and `ci-020384-0b3d42c8` confirm that the reductions have the parent types and refer directly to their designated child. Lean exited zero in both jobs. The scheduler reported a failed axiom review for both because the open children contribute `sorryAx`. The standalone statements and sketches preserve the open obligations.

The local Tate-structure construction at `Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean:121` still supplies the missing data for the conditional ramification proof. The independent read-backs and their source links are in [readbacks/](readbacks/). The iut source is covered by the archived [Apache 2.0 license](../foundation-reference-carriers-20261115/LICENSE.iut.Apache-2.0). Target compatibility edits include `domRestrict` in the additive monoid homomorphism API and explicit conversion of constructor equality to an iff.

| Job | Check | Status | Exit | Wall (s) | CPU total (user + system, s) | Peak RSS (GiB) |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| `ci-020326-01a0860a` | sl2-arithmetic-axioms-1 | succeeded | 0 | 322.51 | 318.36 (208.01 + 110.35) | 4.69 |
| `ci-020143-c29951fc` | sl2-card-group-1 | succeeded | 0 | 80.42 | 77.51 (3.06 + 74.45) | 4.08 |
| `ci-020147-4f861c9b` | sl2-card-group-artifact | succeeded | 0 | 97.40 | 93.29 (3.14 + 90.15) | 3.99 |
| `ci-020209-86070ff0` | sl2-card-reduction-review-1 | failed | 1 | 301.22 | 270.79 (3.26 + 267.53) | 4.57 |
| `ci-020226-796c0556` | sl2-card-reduction-review-2 | failed | 0 | 355.88 | 316.48 (3.70 + 312.78) | 4.59 |
| `ci-020154-18a44ada` | sl2-card-sketch-1 | succeeded | 0 | 176.41 | 174.74 (2.46 + 172.28) | 3.98 |
| `ci-020180-7cd2e8d9` | sl2-card-sketch-artifact | succeeded | 0 | 206.85 | 190.02 (2.62 + 187.40) | 4.00 |
| `ci-020142-566640de` | sl2-card-statement-1 | succeeded | 0 | 77.93 | 73.84 (2.53 + 71.31) | 3.88 |
| `ci-020146-1e43a451` | sl2-card-statement-artifact | succeeded | 0 | 85.77 | 81.48 (2.98 + 78.50) | 3.92 |
| `ci-020208-353f9848` | sl2-fixed-field-1 | timeout | unknown | 210.80 | unknown | unknown |
| `ci-020217-feb82ffd` | sl2-fixed-field-2 | succeeded | 0 | 305.11 | 236.15 (3.15 + 233.00) | 3.86 |
| `ci-020230-f22647a2` | sl2-fixed-field-artifact | succeeded | 0 | 334.53 | 275.94 (3.71 + 272.23) | 3.95 |
| `ci-020248-e269eafa` | sl2-fixed-field-galois-1 | timeout | unknown | 181.84 | unknown | unknown |
| `ci-020257-42f1c750` | sl2-fixed-field-galois-2 | succeeded | 0 | 230.95 | 209.52 (2.87 + 206.65) | 3.92 |
| `ci-020280-f21e20d7` | sl2-fixed-field-galois-artifact | succeeded | 0 | 212.97 | 202.82 (5.34 + 197.48) | 3.98 |
| `ci-020124-51a808e0` | sl2-generation-1 | succeeded | 0 | 79.27 | 79.56 (4.78 + 74.78) | 2.74 |
| `ci-020131-305d5684` | sl2-generation-artifact | succeeded | 0 | 101.03 | 101.43 (4.34 + 97.09) | 2.73 |
| `ci-020170-ce5e5fc5` | sl2-group-axioms-1 | succeeded | 0 | 365.74 | 350.27 (96.59 + 253.68) | 4.69 |
| `ci-020312-3fea6f2f` | sl2-local-torsion-1 | failed | 1 | 105.77 | 103.72 (3.93 + 99.79) | 4.11 |
| `ci-020325-75aa30a7` | sl2-local-torsion-2 | failed | 1 | 98.91 | 95.26 (3.76 + 91.50) | 4.11 |
| `ci-020346-56749d5d` | sl2-local-torsion-3 | succeeded | 0 | 84.52 | 82.05 (3.84 + 78.21) | 4.11 |
| `ci-020375-bda5cd72` | sl2-local-torsion-artifact | succeeded | 0 | 68.44 | 66.16 (4.34 + 61.82) | 4.11 |
| `ci-020383-fae75878` | sl2-local-torsion-axioms | succeeded | 0 | 62.27 | 59.14 (2.85 + 56.29) | 4.03 |
| `ci-020258-d6f2f323` | sl2-local-valuation-1 | timeout | unknown | 180.11 | unknown | unknown |
| `ci-020273-5fd6231a` | sl2-local-valuation-2 | succeeded | 0 | 217.94 | 193.84 (4.17 + 189.67) | 4.11 |
| `ci-020286-e154fa52` | sl2-local-valuation-artifact | succeeded | 0 | 150.11 | 144.24 (4.95 + 139.29) | 4.12 |
| `ci-020358-3e3f7e00` | sl2-project-gates | succeeded | 0 | 259.74 | 252.64 (6.32 + 246.32) | 8.03 |
| `ci-020311-b2af812b` | sl2-ramification-statement-1 | succeeded | 0 | 102.05 | 97.35 (2.32 + 95.03) | 3.83 |
| `ci-020324-46bde962` | sl2-ramification-statement-artifact | succeeded | 0 | 108.92 | 106.21 (3.03 + 103.18) | 3.91 |
| `ci-020292-84cd46ef` | sl2-range-cardinality-1 | succeeded | 0 | 150.43 | 144.78 (2.57 + 142.21) | 3.85 |
| `ci-020310-8776357a` | sl2-range-cardinality-artifact | succeeded | 0 | 108.00 | 103.21 (2.65 + 100.56) | 3.85 |
| `ci-020384-0b3d42c8` | sl2-range-reduction-review | failed | 0 | 71.18 | 69.24 (3.20 + 66.04) | 4.55 |
| `ci-020348-5fd9b2d6` | sl2-range-sketch-1 | succeeded | 0 | 99.04 | 96.93 (2.84 + 94.09) | 3.96 |
| `ci-020377-299f5e09` | sl2-range-sketch-artifact | succeeded | 0 | 58.05 | 54.92 (2.75 + 52.17) | 3.85 |
| `ci-020260-164f83ea` | sl2-tate-torsion-1 | succeeded | 0 | 173.19 | 151.68 (2.67 + 149.01) | 3.11 |
| `ci-020272-a3ed7ec6` | sl2-tate-torsion-artifact | succeeded | 0 | 193.78 | 174.12 (4.12 + 170.00) | 3.14 |
| `ci-020313-6616878c` | tripod-torsion-action-1 | failed | 1 | 123.82 | 121.96 (3.65 + 118.31) | 4.06 |
| `ci-020331-f865464b` | tripod-torsion-action-2 | failed | 1 | 96.41 | 94.07 (2.90 + 91.17) | 4.06 |
| `ci-020347-174280ae` | tripod-torsion-action-3 | failed | 1 | 80.05 | 77.82 (3.45 + 74.37) | 4.06 |
| `ci-020376-20bb9828` | tripod-torsion-action-4 | succeeded | 0 | 62.23 | 59.05 (2.79 + 56.26) | 4.06 |
| `ci-020385-be5e534d` | tripod-torsion-action-artifact | succeeded | 0 | 62.22 | 60.01 (4.01 + 56.00) | 4.08 |
| `ci-020414-207ff115` | tripod-torsion-degree-1 | succeeded | 0 | 60.34 | 59.94 (3.87 + 56.07) | 4.08 |
| `ci-020421-b0bd9211` | tripod-torsion-degree-artifact | succeeded | 0 | 78.86 | 77.60 (4.20 + 73.40) | 4.08 |
| `ci-020431-20b6622e` | tripod-torsion-degree-review | succeeded | 0 | 174.74 | 173.83 (108.65 + 65.18) | 4.67 |
| `ci-020399-49b75768` | tripod-torsion-representation-1 | succeeded | 0 | 96.17 | 94.07 (3.59 + 90.48) | 4.07 |
| `ci-020405-8162a0fb` | tripod-torsion-representation-artifact | succeeded | 0 | 103.86 | 103.31 (4.28 + 99.03) | 4.09 |

## Local Tate model and ramification

The local construction follows `Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean:121` at iut revision `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`. It uses the same curve, completion and coordinate series. [Three-language source readback](readbacks/tate-local-ramification-trilingual.md) · [IUT license](../foundation-reference-carriers-20261115/LICENSE.iut.Apache-2.0) · [Tate source notices](../reference-tate-theta-carriers-20261115/LICENSE.Apache-2.0)

| Target declaration | Source and direct consumer |
| --- | --- |
| `exists_sq_eq_of_norm_sq_sub_lt` | `UltrametricSqrt.lean:172`. Used by `exists_variableChange_tateCurve` for the scaling ratio. |
| `vcEquiv`, `ptX`, `ptY`, `pointCongr` | `VariableChangePoint.lean`. Used by `TateStructure.ofVariableChangeWithUniformization` to transport the point group and its two coordinates. |
| `norm_c₄_curveKw`, `norm_Δ_curveKw`, `norm_two_curveKw`, `exists_tangent_root_of_sq` | `BadPlaceNorm.lean`, `SqrtAtBadPlace.lean` and `TateFamilyOfTorsion.lean`. Supply the local model hypotheses at the selected place. |
| `exists_variableChange_tateCurve` | `TateIsomorphism.lean:291`. Gives the Tate model `D • W = t.tateCurve` with the same `j`. Used by `tateStructureOfBadPlace` after choosing the multiplicative model. |
| `TateParameterUniformization.ofTatePoint` | `PointMap.lean`, `GroupLaw.lean` and `TateUniformization.lean`. Constructs the equivalence from the point equation, additivity and surjectivity and proves the two coordinate laws. |
| `tateStructureOfBadPlace` | `TateFamilyOfTorsion.lean:121` and `TateStructureOfIso.lean`. Takes the square-root identity and a uniformization function explicitly. It combines the two changes of variables and preserves the coordinates in the resulting model. |
| `TateParameterUniformization.ofTateParameter` | Uses `tatePoint_mem'`, `tatePoint_mul` and `tatePoint_surjective` from the existing pinned Tate dependency at `ca6c2279d3cea0690cdb01328e727118d5485d68`. Proves equality of the point maps with the same parameter, guard and coordinate series. [Tate dependency closure](readbacks/tate-uniformization-sources.md) |

The six model modules passed the owned-declaration review `ci-020616-336c870c`. Its 191 declarations use only `propext`, `Classical.choice` and `Quot.sound`. The Checks, ImportAudit, Act1Scene1 and AxiomAudit gate `ci-020590-4429ef69` passed. The point-law bridge passed leaf and artifact compilation in `ci-020624-9ee61ed1`. The project and pinned Tate artifacts are used for local verification. The standalone platform package still requires dependency migration and platform acceptance.

MCP-CI originally dropped output flags when the named `parameters.source` was present. The three positional artifact jobs remedied the missing imports. The pinned Mathlib replaces the unavailable additive type-tag rewrite lemmas with definitional conversions. The structure proof was split into model existence and transport after the default heartbeat timeout. The successful split uses the default limit. The point-map additivity bridge shares one `DecidableEq` instance between both presentations. The two first-attempt wall timeouts lack final CPU and RSS data.

| Job | Source | Status | Exit | Wall (s) | CPU total (user + system, s) | Peak RSS (GiB) |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| [`ci-020500-f749b5c5`](receipts/local-tate-ci-020500-f749b5c5-result.json) | `Source_ReferenceIutUltrametricSqrt` | succeeded | 0 | 93.08 | 29.71 (0.73 + 28.98) | 1.61 |
| [`ci-020502-8a3c7cf8`](receipts/local-tate-ci-020502-8a3c7cf8-result.json) | `Source_ReferenceIutVariableChangePoint` | succeeded | 0 | 91.57 | 29.32 (0.67 + 28.65) | 1.60 |
| [`ci-020505-29c4eb8b`](receipts/local-tate-ci-020505-29c4eb8b-result.json) | `Source_ReferenceIutTateLocalModels` | succeeded | 0 | 91.31 | 28.81 (0.85 + 27.96) | 1.62 |
| [`ci-020514-4f1dbd84`](receipts/local-tate-ci-020514-4f1dbd84-result.json) | `Source_ReferenceIutUltrametricSqrt` | succeeded | 0 | 54.65 | 52.26 (1.39 + 50.87) | 2.44 |
| [`ci-020515-136835ff`](receipts/local-tate-ci-020515-136835ff-result.json) | `Source_ReferenceIutTateLocalModels` | succeeded | 0 | 83.92 | 83.97 (5.04 + 78.93) | 4.16 |
| [`ci-020516-93db22ee`](receipts/local-tate-ci-020516-93db22ee-result.json) | `Source_ReferenceIutVariableChangePoint` | succeeded | 0 | 58.29 | 59.49 (6.21 + 53.28) | 2.91 |
| [`ci-020524-c5f3337c`](receipts/local-tate-ci-020524-c5f3337c-result.json) | `Source_ReferenceIutTateIsomorphism` | failed | 1 | 38.79 | 37.49 (1.32 + 36.17) | 2.28 |
| [`ci-020525-065fcaa8`](receipts/local-tate-ci-020525-065fcaa8-result.json) | `Source_ReferenceIutTateUniformization` | failed | 1 | 44.31 | 42.56 (1.35 + 41.21) | 2.48 |
| [`ci-020529-63e5a619`](receipts/local-tate-ci-020529-63e5a619-result.json) | `Source_ReferenceIutUltrametricSqrt` | succeeded | 0 | 43.07 | 41.60 (1.73 + 39.87) | 2.52 |
| [`ci-020530-fda82a58`](receipts/local-tate-ci-020530-fda82a58-result.json) | `Source_ReferenceIutVariableChangePoint` | succeeded | 0 | 45.81 | 46.90 (5.20 + 41.70) | 2.90 |
| [`ci-020531-f7cc4ff1`](receipts/local-tate-ci-020531-f7cc4ff1-result.json) | `Source_ReferenceIutTateLocalModels` | succeeded | 0 | 84.56 | 84.90 (5.84 + 79.06) | 4.15 |
| [`ci-020536-4a9b278c`](receipts/local-tate-ci-020536-4a9b278c-result.json) | `Source_ReferenceIutTateIsomorphism` | succeeded | 0 | 90.32 | 90.12 (4.78 + 85.34) | 4.13 |
| [`ci-020537-daccc80d`](receipts/local-tate-ci-020537-daccc80d-result.json) | `Source_ReferenceIutTateUniformization` | failed | 1 | 59.35 | 57.24 (2.40 + 54.84) | 2.99 |
| [`ci-020545-63c54b65`](receipts/local-tate-ci-020545-63c54b65-result.json) | `Source_ReferenceIutTateIsomorphism` | succeeded | 0 | 132.22 | 132.15 (5.53 + 126.62) | 4.15 |
| [`ci-020546-399cdd86`](receipts/local-tate-ci-020546-399cdd86-result.json) | `Source_ReferenceIutTateUniformization` | succeeded | 0 | 90.77 | 88.38 (2.26 + 86.12) | 2.95 |
| [`ci-020558-a857eaaa`](receipts/local-tate-ci-020558-a857eaaa-result.json) | `Source_ReferenceIutTateStructureOfTorsion` | failed | 1 | 159.50 | 157.29 (20.79 + 136.50) | 4.31 |
| [`ci-020559-2b3e8730`](receipts/local-tate-ci-020559-2b3e8730-result.json) | `Source_ReferenceIutTateUniformizationLaws` | timeout | unknown | 180.09 | unknown | unknown |
| [`ci-020560-8b916670`](receipts/local-tate-ci-020560-8b916670-result.json) | `Source_ReferenceIutSplitSquare` | timeout | unknown | 180.06 | unknown | unknown |
| [`ci-020571-e5f51bd3`](receipts/local-tate-ci-020571-e5f51bd3-result.json) | `Source_ReferenceIutTateUniformizationLaws` | failed | 1 | 385.16 | 377.11 (5.29 + 371.82) | 7.38 |
| [`ci-020576-4d1d273b`](receipts/local-tate-ci-020576-4d1d273b-result.json) | `Source_ReferenceIutTateStructureOfTorsion` | succeeded | 0 | 162.57 | 156.13 (3.32 + 152.81) | 4.10 |
| [`ci-020585-5381da30`](receipts/local-tate-ci-020585-5381da30-result.json) | `Source_ReferenceIutSplitSquare` | failed | 1 | 394.00 | 379.57 (6.65 + 372.92) | 7.49 |
| [`ci-020590-4429ef69`](receipts/local-tate-ci-020590-4429ef69-result.json) | `RequiredProjectGates` | succeeded | 0 | 412.62 | 396.32 (6.48 + 389.84) | 7.87 |
| [`ci-020597-0e754543`](receipts/local-tate-ci-020597-0e754543-result.json) | `Source_ReferenceIutTateUniformizationLaws` | failed | 1 | 448.08 | 435.08 (6.57 + 428.51) | 7.46 |
| [`ci-020599-7476c6c1`](receipts/local-tate-ci-020599-7476c6c1-result.json) | `Source_ReferenceIutTateStructureOfTorsion` | succeeded | 0 | 261.33 | 255.77 (4.98 + 250.79) | 4.12 |
| [`ci-020615-00dfa7b0`](receipts/local-tate-ci-020615-00dfa7b0-result.json) | `Source_ReferenceIutSplitSquare` | failed | 1 | 443.72 | 432.11 (6.96 + 425.15) | 7.49 |
| [`ci-020616-336c870c`](receipts/local-tate-ci-020616-336c870c-result.json) | `ReviewLocalTateModels` | succeeded | 0 | 527.60 | 520.52 (278.17 + 242.35) | 4.69 |
| [`ci-020624-9ee61ed1`](receipts/local-tate-ci-020624-9ee61ed1-result.json) | `Source_ReferenceIutTateUniformizationLaws` | succeeded | 0 | 405.11 | 397.33 (6.51 + 390.82) | 7.46 |

## Torsion-field ramification and tripod curve inputs

| Target declaration | Source and direct consumer |
| --- | --- |
| `exists_sq_eq_neg_c₄_mul_c₆` | `Iut/Cor312/ThetaData/SplitSquare.lean`. The full torsion over the selected torsion field supplies the square root in its completion. The proof reuses the main project's pinned compatibility theorem. |
| `EllipticCurveData.prime_dvd_ramificationIdx_from_source` | `Iut/Concrete/SL2Image.lean:162` and the local split Tate construction of `Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean:121`. It constructs the Tate structure at the specified place of `R.torsionField`. The proof consumes the square root, the point-law bridge and the conditional ramification lemma. Construction of the global Tate family remains a separate obligation. |
| `sl2Image_from_source` | `Iut/Tripod/CurveFacts.lean:442` and `Iut/Concrete/SL2Image.lean:217,229`. It uses the proved ramification divisibility to supply range-cardinality divisibility and the SL₂ inclusion for the original curve provider. |
| `legendre_torsionBasis`, `torsionDegreeBound_three'`, `torsionDegreeBound_five'` | `Iut/Tripod/TorsionBasis.lean:31` and `Iut/Tripod/TorsionDegree.lean:237,243`. They supply the two pointwise degree fields using the main project's torsion-count and basis proofs. |
| `logCondGe`, `logCondLe` | `Iut/Tripod/LogCond.lean:196,206`. Both inequalities use the same tripod field and the same degree normalization. The reverse bound uses the sum of residue degrees over characteristics 2 and ℓ to obtain the error `log (2 * ℓ)`. [Three-language readback](readbacks/tripod-log-cond.md) |
| `curveInputs_from_source` | `Iut/Tripod/CurveFacts.lean:492`. The 21-field constructor consumes the new image proof and the four pointwise arithmetic fields. It retains the curve provider, curve facts including the cyclic estimate, core finiteness and the height-related inputs. `CurveInputs.toCorollary22Inputs` is the next consumer. |

The source revision and licenses are the same as in the local Tate section. The proved ramification and arithmetic fields use the existing main-project and pinned Tate artifacts. Standalone dependency packaging, cross-version comparison and private platform acceptance remain open. The platform theorem mirrors preserve the open statements and their signatures.

The LogCond recheck corrected the finite-set membership lemma invocation and the orientation of addition in the last inequality. The combined audit timed out. The two narrower reviews checked the constructor and image types and six public arithmetic declarations. The three successful reviews below reported no `sorryAx` and only `propext`, `Classical.choice` and `Quot.sound`.

Successful jobs report compiler-process wall time and process-tree RSS from MCP-CI. Timeout rows use the scheduler's elapsed compile time, with unknown compiler exit, CPU time and peak RSS. Source fingerprints are prefixes of the SHA-256 values in the receipts. Each receipt records the exclusive worktree and the exact input hashes.

| Job | Source | SHA-256 prefix | Status | Exit | Wall (s) | CPU total (user + system, s) | Peak RSS (GiB) |
| --- | --- | --- | --- | ---: | ---: | ---: | ---: |
| [`ci-020660-b7ab1074`](receipts/local-tate-ci-020660-b7ab1074-result.json) | `Source_ReferenceIutSplitSquare` | `403ee4bdd751` | succeeded | 0 | 272.12 | 265.38 (9.03 + 256.35) | 7.50 |
| [`ci-020695-d1091a87`](receipts/local-tate-ci-020695-d1091a87-result.json) | `Source_TripodTorsionBasis` | `37a876d7f794` | timeout | unknown | 180.18 | unknown | unknown |
| [`ci-020700-aef88e0e`](receipts/local-tate-ci-020700-aef88e0e-result.json) | `Source_TripodLogCond` | `a45fa3a3e3af` | timeout | unknown | 180.19 | unknown | unknown |
| [`ci-020708-fcc842b3`](receipts/local-tate-ci-020708-fcc842b3-result.json) | `Source_SL2ImageLocalTate` | `8b4ea42b9c8a` | timeout | unknown | 180.14 | unknown | unknown |
| [`ci-020725-a0617c37`](receipts/local-tate-ci-020725-a0617c37-result.json) | `Source_TripodTorsionBasis` | `37a876d7f794` | succeeded | 0 | 124.25 | 121.41 (3.18 + 118.23) | 4.01 |
| [`ci-020733-2f166d61`](receipts/local-tate-ci-020733-2f166d61-result.json) | `Source_TripodLogCond` | `a45fa3a3e3af` | failed | 1 | 149.50 | 149.25 (5.57 + 143.68) | 4.16 |
| [`ci-020747-ee9f7218`](receipts/local-tate-ci-020747-ee9f7218-result.json) | `Source_SL2ImageLocalTate` | `8b4ea42b9c8a` | succeeded | 0 | 305.93 | 303.58 (7.51 + 296.07) | 7.53 |
| [`ci-020761-bad0d871`](receipts/local-tate-ci-020761-bad0d871-result.json) | `Source_TripodLogCond` | `1e068431baf7` | succeeded | 0 | 132.26 | 129.28 (6.35 + 122.93) | 4.17 |
| [`ci-020770-6c86a66e`](receipts/local-tate-ci-020770-6c86a66e-result.json) | `ReviewLocalTateRamification` | `d1b51bbd6d24` | succeeded | 0 | 630.10 | 623.01 (385.56 + 237.45) | 7.97 |
| [`ci-020792-4d2b1792`](receipts/local-tate-ci-020792-4d2b1792-result.json) | `Source_TripodCurveInputsFromSource` | `dc5461b7eaee` | timeout | unknown | 180.50 | unknown | unknown |
| [`ci-020795-7aee1771`](receipts/local-tate-ci-020795-7aee1771-result.json) | `Source_TripodCurveInputsFromSource` | `dc5461b7eaee` | succeeded | 0 | 404.87 | 395.97 (6.10 + 389.87) | 7.55 |
| [`ci-020812-b92bc617`](receipts/local-tate-ci-020812-b92bc617-result.json) | `ReviewTripodCurveInputsFromSource` | `9de2a27beba6` | timeout | unknown | 880.16 | unknown | unknown |
| [`ci-020827-2725d6f7`](receipts/local-tate-ci-020827-2725d6f7-result.json) | `ReviewTripodCurveInputsRoots` | `bd91f9a9fc4a` | succeeded | 0 | 145.05 | 143.32 (5.20 + 138.12) | 7.49 |
| [`ci-020829-26f0c710`](receipts/local-tate-ci-020829-26f0c710-result.json) | `ReviewTripodArithmeticFields` | `c37daf023621` | succeeded | 0 | 60.02 | 58.91 (2.54 + 56.37) | 4.16 |

The current batch's Checks, ImportAudit, Act1Scene1 aggregate and AxiomAudit gate passed in [ci-020844-3d5ac401](receipts/local-tate-ci-020844-3d5ac401-result.json). The exclusive review ran `lean .local/adaptation/b1-curve-field-arithmetic-20261118/RequiredProjectGates.lean` with exit code 0. It used 119.41 seconds of process wall time, 118.29 seconds of CPU (5.12 user and 113.17 system), and 7.83 GiB of peak process-tree RSS.
