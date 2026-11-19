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

The [independent read-backs](readbacks/) cover English, Simplified Chinese and Japanese. The approved translations include 紧致有界子集 for `compactly bounded subset`, 素元 for `uniformizer` and 指定素数 for `distinguished primes`.

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

## Finite exceptional Legendre parameters for the core condition

`Source_TripodCoreFiniteness.lean` adapts the polynomial argument in `Iut/Tripod/Core.lean:31–64,112` at the pinned iut revision. The public lemma `finite_curve_j_preimage` sends the actual provider curve's (j)-invariant to the Legendre value in `Qbar` through the existing field embedding. `coreFiniteness_of_exceptionalJ` consumes that finiteness result and returns the `CoreFinitenessHyp` expected by `curveInputs_from_source` from a finite rational exceptional set and the geometric inclusion for the same `AG` and curves.

The geometric inclusion in `Core.lean:72` still needs the `CanLift` result and compatibility of base change with the once-punctured curve and its sign quotient in the chosen model. The pin uses Pi1 `ca7def953193f861a462aa0831eec8f0a31ff69f` and OrbicurveCores `61616dcd77fbe45c083a8ebfa7cc80728f86e841`. Their source proofs are available in the legacy source checkout. The two direct imports `Pi1.Orbicurve.LefschetzMain` and `OrbicurveCores.U2.Assembly` lack compatible artifacts in the target environment.

The three jobs used the actual exclusive worktree and exited with code 0. The project gate and the three public axiom checks passed. The axiom output lists only `propext`, `Classical.choice` and `Quot.sound`.

| Job | Check | SHA-256 prefix | Wall (s) | CPU total (user + system, s) | Peak RSS (GiB) |
| --- | --- | --- | ---: | ---: | ---: |
| [`ci-020853-fe047d77`](receipts/tripod-core-ci-020853-fe047d77-result.json) | Leaf | `812ca4070774` | 51.84 | 51.37 (2.64 + 48.73) | 4.11 |
| [`ci-020855-99ce0a2e`](receipts/tripod-core-ci-020855-99ce0a2e-result.json) | Import artifact | `812ca4070774` | 58.23 | 57.15 (3.48 + 53.67) | 4.12 |
| [`ci-020859-ae4a0f86`](receipts/tripod-core-ci-020859-ae4a0f86-result.json) | Project gates and axiom review | `[WARNING]` | 145.06 | 141.48 (6.06 + 135.42) | 8.07 |

## Continued P7 fields and conditional cyclic-bound assembly

The P7 field source `Source_ReferenceIutCurveThetaInputs.lean` supplies `mem_badAll_of_mem_badPlacesOver`, `globalData`, and `primeData`. The latter preserves `R.rep`, so the fixed-field torsion carrier remains the same representation carrier. Review `ci-020948-af1d9945` checked both declarations and the equality test after importing the torsion-field carrier. Only `propext`, `Classical.choice`, and `Quot.sound` were reported.

`Source_TripodCyclicBoundOdd.lean` supplies local-height splitting, the odd Tate-family graph-line target, and `cyclicBoundOdd_of_isogeny`. The theorem is conditional on the local graph-line producer and the Vélu main-bound producer. It keeps the archimedean torsion estimate and the local decomposition-group argument as explicit upstream obligations. Its artifact compilation is `ci-020947-cd31bcd2`. The project and axiom review `ci-020957-a44be081` passed and checked five declarations. The first three attempts were `ci-020875-0c641759`, `ci-020880-80942371`, and `ci-020885-6d8cfa49`. Their failures are preserved with diagnostics. The successful artifact uses the same exclusive worktree and exact source hash.

[Initial Θ-data field readback](readbacks/curve-theta-inputs.md) · [Cyclic estimate readback](readbacks/cyclic-bound-odd.md)

| Job | Target | Status | Exit | Wall (s) | CPU total (user + system, s) | Peak RSS (GiB) |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| [`ci-020875-0c641759`](receipts/tripod-cyclic-ci-020875-0c641759-result.json) | `Source_TripodCyclicBoundOdd` | failed | 1 | 99.79 | 97.96 (6.20 + 91.76) | 7.52 |
| [`ci-020880-80942371`](receipts/tripod-cyclic-ci-020880-80942371-result.json) | `Source_TripodCyclicBoundOdd` | failed | 1 | 143.28 | 142.73 (6.78 + 135.95) | 7.52 |
| [`ci-020885-6d8cfa49`](receipts/tripod-cyclic-ci-020885-6d8cfa49-result.json) | `Source_TripodCyclicBoundOdd` | failed | 1 | 167.85 | 168.03 (11.60 + 156.43) | 7.54 |
| [`ci-020939-c4c6d4d1`](receipts/continued-ci-020939-c4c6d4d1-result.json) | `Source_ReferenceIutCurveThetaInputs` | succeeded | 0 | 54.37 | 48.75 (3.21 + 45.54) | 4.08 |
| [`ci-020943-ab68463c`](receipts/continued-ci-020943-ab68463c-result.json) | `Source_ReferenceIutCurveThetaInputs` | succeeded | 0 | 49.21 | 48.10 (2.00 + 46.10) | 3.94 |
| [`ci-020944-96787473`](receipts/continued-ci-020944-96787473-result.json) | `Source_TripodCyclicBoundOdd` | succeeded | 0 | 80.28 | 74.56 (4.60 + 69.96) | 7.50 |
| [`ci-020945-887617e6`](receipts/continued-ci-020945-887617e6-result.json) | `ReviewCurveThetaInputs` | failed | 1 | 95.97 | 94.65 (5.34 + 89.31) | 8.06 |
| [`ci-020947-cd31bcd2`](receipts/continued-ci-020947-cd31bcd2-result.json) | `Source_TripodCyclicBoundOdd` | succeeded | 0 | 129.46 | 128.10 (5.92 + 122.18) | 7.52 |
| [`ci-020948-af1d9945`](receipts/continued-ci-020948-af1d9945-result.json) | `ReviewCurveThetaInputs` | succeeded | 0 | 123.17 | 121.69 (5.21 + 116.48) | 7.96 |
| [`ci-020957-a44be081`](receipts/continued-ci-020957-a44be081-result.json) | `ReviewCyclicBoundOdd` | succeeded | 0 | 85.63 | 85.35 (4.85 + 80.50) | 8.07 |

The cyclic retries addressed the duplicate instance name, field coercions, declaration modifiers and use of the canonical decidable equality in the Tate graph-line carrier. The first P7 audit added the missing direct import in its retry to check the fixed-field equality. The diagnostics and exact input hashes are in the receipts.

## Conditional assembly of initial theta data

`EllipticCurveData.thetaData` adapts `Iut/Concrete/Existence.lean:289,325` at the pinned iut revision. It takes the native Tate family over the fixed field of `R.rep`, the core condition, and the geometry existence interface. It selects `orb` and the local data for that same orbicurve, and passes the same Tate family to the geometry interface. The project review checks the fixed field, the representation, the Tate family and the algebra map from the moduli field. The two public declarations use `propext`, `Classical.choice` and `Quot.sound`. [Independent readback](readbacks/initial-theta-data.md)

The q-pilot uses the residue degree divided by the absolute field degree. Its support consists of exactly the multiplicative places away from 2 and ℓ. The proof of `logQ_eq` uses the same Tate parameter orders as the curve's local height. The three public declarations use only the standard axioms. [Independent q-pilot readback](readbacks/q-pilot.md)

`ModEllRepData.tateFamily` constructs a Tate structure at each place over `VBadOf ℓ` in the fixed field of the original representation. The family keeps the original local structures. `TateFamily.ofStructures` supplies Galois equivariance for the graph line and canonical generators. Review `ci-021096-88b726c0` passed the project gates and standard-axiom checks and verified the family at `primeData.torsionField` and `primeData.ℓ`. The initial review needed the explicit number-field instance for this projection. [Independent readback](readbacks/curve-tate-family.md)

## Cyclic subgroup bound at the chosen torsion constant

The parameterized proof uses `max 1 (Classical.choose harch)`, as in `Iut/Tripod/CyclicIsogeny.lean:1003`. It passes both the lower bound of 1 and the uniform complex Legendre torsion-coordinate bound at `K.c` to the Vélu estimate. The other input is the graph-line property for each odd bad place, including places of residue characteristic ℓ. The conditional proof and its constant have only the three project standard axioms. [Independent readback](readbacks/cyclic-split.md)

The initial graph-line check reached its scheduler timeout without compiler diagnostics. The two extracted leaves were corrected to use the maximal-ideal lies-over relation and the direct Mathlib import for `Nat.card_zmultiples`. This validates the decomposition-group and prime-order subgroup ingredients.

The three open mirrors correspond to `CyclicLocal.lean:515` with its provider wrapper, `CyclicArch.lean:27`, and `CyclicIsogeny.lean:831`. The parent reduction matches the parent signature and its proof term directly references the three child declarations. The review command in `ci-021095-a05fa104` exited with code 0 and found the expected inherited `sorryAx`. The scheduler marks a review with that output as failed. Leaf `ci-021105-c95ca126` passed the same type, direct dependency and axiom assertions for the open reduction. The separate closed conditional proof passed the standard-axiom audit in `ci-021019-7fdc70e3`.

## Pointwise initial theta data and local place fibers

`CurveInputs.exists_initialThetaData` applies the existing point hypotheses to the input curve, then assembles the Tate family, initial data, and q-pilot. It recovers the prime, moduli-degree bound, q-pilot height, different, and both conductor inequalities from the same curve. Review `ci-021114-34799f4b` reports only the three standard axioms. The anabelian existence interface remains an input.

The local-theory port preserves the tensor, integral structure, hull, and volume fields of `Iut/Concrete/LocalTheory.lean`. The place-fiber module proves the finite and infinite fiber identifications, positivity of the normalized weights, and their sum from the corresponding local-degree and infinite multiplicity sums. Review `ci-021113-826459f1` passed the project gates and standard-axiom checks. These statements consume a `LocalTheory` on the specified field.

## Core finiteness in the étale model

`Source_TripodCoreGeometry.lean` ports the geometric inclusion in `Iut/Tripod/Core.lean:73` in the same provider curve. If `E.j` avoids the rational exceptional values, the map on each characteristic-zero extension preserves that avoidance by injectivity and compatibility with rational casts. The base-change identities for the once-punctured curve and sign quotient transfer the core relation to those same base-changed objects. The inclusion supplies `coreFiniteness_of_exceptionalJ`.

`Source_TripodCoreModel.lean` uses `EtalePi1Theory` to construct `modelAG` and supplies the two model base-change identities and the existing `Pi1.hasCore_oncePunctured` field to `coreFiniteness_of_geometry`. The result is the `CoreFinitenessHyp` required by the curve-input constructor for that provider and model. The genuine reference theory in `Iut/Anabelian/GenuineEtale.lean` consumes `AffOrbicurve.CanLift27`. The reference proof in `Iut/Tripod/ClassicalAbcGenuineCanLift.lean:28` applies `AffOrbicurve.canLift27_of_complex` from `pi1` at `ca7def953193f861a462aa0831eec8f0a31ff69f` to `OrbicurveCores.U2.canLift27C` from `orbicurve-cores` at `61616dcd77fbe45c083a8ebfa7cc80728f86e841`. That supply is pending in the target. [Trilingual readback](readbacks/core-geometry-and-model.md)

The independent leaves and their artifacts passed. Review [`ci-021147-606ee1da`](receipts/round-ci-021147-606ee1da-result.json) checked the public result type and eight explicit axiom closures, all limited to `propext`, `Classical.choice`, and `Quot.sound`. Its imports include the project checks, import audit, Scene1 aggregate, and axiom audit.

## The cyclic subgroup at odd bad places

`Source_TripodCyclicLocal.lean` adapts `Iut/Tripod/CyclicLocal.lean:515` and supplies `cyclicLocalGraphLine_from_source`. With the Tate family on the same torsion field, (P2) implies divisibility of the ramification index by ℓ. Cauchy's theorem gives a decomposition-group element of order ℓ. If the two lines differ, they span the ℓ-torsion. Both are stable, so the element acts on each through a group of order ℓ − 1 and fixes all torsion, contradicting faithfulness. This proof applies at odd bad places of residue characteristic ℓ. `curveFacts_of_cyclicMainBound` consumes the resulting graph-line proof and the remaining global isogeny estimate. Leaf [`ci-021188-a24859aa`](receipts/round-ci-021188-a24859aa-result.json), artifact [`ci-021201-c749f731`](receipts/round-ci-021201-c749f731-result.json), and project review [`ci-021208-4b457ebf`](receipts/round-ci-021208-4b457ebf-result.json) passed. All ten axiom closures in the review use standard Lean axioms only.

## The container and tower local facts

`Source_ReferenceIutConcreteContainer.lean` adapts `Iut/Concrete/Container.lean`. It constructs the indexed tensor product regions, proves the finite support of the log-shell away from the infinite place, 2 and the ramified primes, and defines the packet volume by its weighted projections. It proves the product formula when all components are nonempty. Given `LocalTheory K`, the finite and infinite componentwise least-hull laws give the least admissible hull of each admissible product region. [`ci-021174-f7028043`](receipts/round-ci-021174-f7028043-result.json) and [`ci-021187-e20c5b25`](receipts/round-ci-021187-e20c5b25-result.json) passed.

`Source_ReferenceIutTowerLocalFacts.lean` adapts `Iut/Tower/Residual.lean`. It supplies the inclusion of the moduli field into the tripodal field, the degree identity, and the ramification and residue-degree product identities for a place of the same torsion field above the tripodal field. The interface retains the wild bound, the unramified condition away from the bad and exceptional primes, and the bound `e(v/u) ≤ 30ℓ` away from the exceptional primes. [Trilingual readback](readbacks/tower-local-facts-trilingual.md)

Project review [`ci-021200-5a4e6c8b`](receipts/round-ci-021200-5a4e6c8b-result.json) checked both modules and their nineteen axiom closures, which use only `propext`, `Classical.choice` and `Quot.sound`.

## Theta regions, invariants and local arithmetic

`Source_ReferenceIutConcreteThetaRegion.lean` constructs the finite and infinite theta regions of the same `D` and `LT` from `TL`. It proves admissibility and finite support, then combines the resulting right-hand side with `QI.qPilot`. `Source_ReferenceIutConcreteInvariants.lean` constructs the distinguished-prime set and its local different contributions for the same torsion field. Outside that set, the different contribution vanishes. `TowerArithmetic.certificate` uses the prime bound, the support of the same q-pilot, and Steps (ii) and (iii) of that tower. The (R4) field is for the local volume estimate.

`Source_ReferenceIutConcreteLocalArithmetic.lean` supplies the actual local degree and infinite multiplicity sums and the arithmetic of the normalized valuation on the number field's completions. It also proves finite ramification support and vanishing of the different exponent at unramified places. The concrete tensor and measure fields still require their own source constructions.

Project review [`ci-021270-ac3cb671`](receipts/round-ci-021270-ac3cb671-result.json) checked the project and twenty axiom closures, all limited to the three standard Lean axioms.

## CanLift normalization and covering lemmas

`Source_ReferenceIutCanLiftPresentation.lean` uses the existing signed and unsigned normalization rings. The unsigned multiplicity is one, and the signed multiplicity is the ramification multiplicity of the inclusion. It constructs the quotient cover and states Proposition 2.7 for this pair with the four exceptional rational j-values. `normalizationHasCore_oncePunctured` consumes Proposition 2.7 in that form. Sources are Pi1 revision `ca7def953193f861a462aa0831eec8f0a31ff69f` and iut revision `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`, as identified in the module header.

`Source_ReferenceIutCanLiftCoverDescent.lean` descends a cover along a common cover from a supplied factorization through the intermediate Dedekind coordinate ring. Injectivity and integrality descend along the intermediate map. A maximal ideal above each intermediate maximal ideal gives the ramification tower identity. It verifies the covering law by comparing the multiplicities and ramification indices. `Source_ReferenceIutCanLiftPolynomialDegree.lean` uses the sum of polynomial fiber multiplicities and the derivative multiplicity in characteristic zero to prove degree one for the étale polynomial self-cover with multiplicity two at three marked points. The complex coordinate descent, covering uniqueness and Lefschetz argument remain open.

[Project and axiom review](receipts/round-ci-021380-91c6737e-result.json) checks fourteen public declarations. Their axiom closures use only `propext`, `Classical.choice` and `Quot.sound`. It imports the project checks, Scene1 aggregate, import audit and axiom audit. [Independent trilingual readback](readbacks/canlift-foundations-trilingual.md)

## Local estimates for the concrete theta region

`Source_ReferenceIutConcreteLocalEstimate.lean` adapts `Iut/Concrete/LocalEstimate.lean` at revision `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`. It constructs the seven fields of `TowerArithmetic.localEstimate` for `TL.invariants QI` on the same `D` and `LT`. At a distinguished prime, it uses Proposition 1.4(iii) from `LT`, q-degree base change from `TL`, averaging over the same place fibers, and the (R4) field of `TA`. Outside the distinguished primes the container is the integral region. At infinity the bound uses Proposition 1.5 from `LT`. Component monotonicity gives packet monotonicity. The nonempty scaled region for the weighted product formula is proved from the explicit image of the unit.

[Leaf](receipts/round-ci-021338-71910910-result.json) and [artifact](receipts/round-ci-021368-04a24c77-result.json) use the same source hash. [Project review](receipts/round-ci-021405-7008ce12-result.json) checks the type and sixteen axiom closures. The closures use only `propext`, `Classical.choice` and `Quot.sound`. The review also imports the project checks, import audit, Scene1 aggregate and axiom audit.

## Concrete P7 and its consumer in Corollary 2.2

`Source_ReferenceIutConcreteExistence.lean` adapts `Iut/Concrete/Main.lean`. `ConcreteThetaDataExistence` quantifies over every applicable point and prime and preserves (P2), (P3), (P5), (P6) and the six arithmetic identities or bounds. Its conversion uses the same `D`, `LT`, `TL`, `QI` and `TA` to build `IsConcrete`, the Theorem 1.10 certificate and all seven fields of the local estimate.

`Source_ReferenceIutCurveConcreteExistence.lean` matches the provider-based composition in `Iut/Concrete/Existence.lean:499`. It consumes the existing pointwise construction on the same torsion field and the supplied `AnabelianExistence`, `LTp`, `TLp` and `TAp`. The audit applies `Corollary22Inputs.c2` with `P := IsConcrete` and proves the full pointwise conclusion using the universal Corollary 3.12 variant on all concrete data. Actual providers for the local tensor and measure theory, theta data, tower arithmetic and anabelian existence remain open.

[Concrete existence artifact](receipts/round-ci-021390-964c6d68-result.json) · [Curve composition artifact](receipts/round-ci-021418-6ae2447f-result.json) · [Project and axiom review](receipts/round-ci-021440-f6c510e9-result.json). The review checks five declarations, including the application of `c2`. The axiom closures use `propext`, `Classical.choice` and `Quot.sound`.

## Cyclic subgroup archimedean drafts

A subagent wrote thirteen draft files into the shared workspace and submitted seventeen MCP-CI jobs using the main agent identity before integration. The subagent returned to its task directory. The main agent confirmed the terminal status of all seventeen jobs and checked the source hashes against the copies delivered by the subagent. The main agent checked the recorded inputs of the accepted CanLift and P7 reviews against the current files and against the list of paths touched by the subagent. The affected cyclic drafts enter acceptance through a fresh review by the main agent. The inventory links each job ID to its source revision, and the corresponding `preintegration-<job-id>-result.json` files preserve the structured results. [Inventory](cyclic-preintegration-inventory.json)

`Source_TripodCyclicArch.lean` adapts `Iut/Tripod/CyclicArch.lean:27` using the six-power bound of `Heights/TorsionArchimedean.lean:392` at revision `721496ca4c158e511d25d8ccf6bfe8503eda73c1`. The proof specializes the complex bound with its original constant construction. The cyclic subgroup combination continues to use the constant chosen from that same existence statement. The conditional specialization and its premise were checked in [the main-agent project review](receipts/round-ci-021483-ab25526b-result.json). Their axiom closures use only the three standard Lean axioms.

[The open reduction audit](receipts/round-ci-021506-2cdf81e9-result.json) verifies that the sketch has the full parent type and directly uses the Heights node and the conditional specialization. It confirms the transitive `sorryAx` from the open Heights node. [Trilingual readback](readbacks/legendre-torsion-bound-trilingual.md)

## Tensor packet for the concrete local theory

`Source_ReferenceIutConcreteLocalPacket.lean` adapts `Iut/Concrete/LocalConstruct/Packet.lean` at revision `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`. It constructs `LocalTensor.{u,u} K` over all rational places. Each factor over a finite prime is the completion modulo the zero ideal when the place is over the prime, and modulo the unit ideal otherwise. The infinite factors and their real bases reuse the Scene1 archimedean tensors. The finite and infinite coordinate bases give the corresponding topology, including the tensor on the empty index type. `Source_ReferenceIutConcreteLocalPacketEquiv.lean` identifies the finite all-genuine factors with the existing completion tensor and gives both pure-tensor formulas and continuous norm bounds. `Source_ReferenceIutConcreteLocalOrder.lean` supplies the unit-ball criterion and the effect of division by a power of the rational prime on normalized order.

[Project and axiom review](receipts/round-ci-021534-9f07f95d-result.json) checked seventeen declarations. Their axiom closures use the three standard Lean axioms. Integral structures, measures, log-shells and Proposition 1.4 remain in the [producer dependency map](concrete-local-theory-dependencies.md). [Independent trilingual readback](readbacks/p7-local-packets-trilingual.md)

## Tower Step III and normalized different accounting

`Source_ReferenceIutTowerStepIII.lean` adapts `Iut/Tower/StepIII.lean:353`. It treats the four small primes, the residue characteristics of the bad places, and the remaining ramified primes by separate estimates. The last group uses the unramified condition of the torsion tower to descend ramification to the tripodal field. The bounds retain `TowerLocalFacts`, the relative ramification bound at bad places, the Galois instance for the tripodal extension, and the support hypothesis on the distinguished set.

`Source_ReferenceIutConcreteDifferentDegree.lean` adapts `Iut/Tower/LogDK.lean`. The local degree weights cancel the absolute ramification index in each normalized different exponent. The residue degree then identifies each contribution with the logarithm of its ideal norm. Regrouping the same terms by residue characteristic gives `ThetaLocalData.sum_dst_logDK_eq`. [Tower leaf](receipts/round-ci-021535-d9ca78fc-result.json) · [Different accounting leaf](receipts/round-ci-021505-6d16e48c-result.json) · [Project and axiom review](receipts/round-ci-021569-f47bd4e2-result.json)

`Source_ReferenceIutTowerStepIIIForTheta.lean` instantiates the Step (iii) proof on `TL.dst` as in `Iut/Tower/Main.lean`. The witness for a prime of `TL.badChars` lies in the actual `badPlacesOver F E VBad`. The ramified-prime witness lies in the same torsion field as the input to `LocalTheory`. [Leaf](receipts/round-ci-021602-3e104202-result.json) · [Project and axiom review](receipts/round-ci-021616-6e2ea5a0-result.json) · [Independent trilingual readback](readbacks/tower-step-iii-trilingual.md)

`Source_ReferenceIutThetaLocalBadChars.lean` takes the image of the same q-pilot bad places under `residueChar`. It uses the input root on this image and the base point 1 off it, and proves the Step (iii) support condition on the resulting `dst`. The actual curve specialization still requires the bad-place ramification bound and local tower facts. [Leaf](receipts/round-ci-021649-3ffa7c78-result.json) · [Project and axiom review](receipts/round-ci-021667-f7dd1302-result.json)

## Modular j for the complex torsion bound

`Source_ReferenceHeightsLatticeModular.lean` and `Source_ReferenceHeightsModularCusp.lean` adapt `Heights/ModularJ.lean` at revision `721496ca4c158e511d25d8ccf6bfe8503eda73c1`. They identify the discriminant and $j$ invariant of the short lattice curve, prove invariance under the modular group and establish cusp growth. Taking representatives in the fundamental domain still uses the explicit `hsurj` input. The range proof and the two logarithmic comparisons consume the cusp estimates. [Modular leaf](receipts/round-ci-021603-c34a5f2a-result.json) · [Cusp leaf](receipts/round-ci-021604-03622920-result.json) · [Project and axiom review](receipts/round-ci-021617-fb4d9a8a-result.json) · [Independent trilingual readback](readbacks/heights-modular-cusp-trilingual.md)

## CanLift unramified Galois closure

`Source_ReferenceIutCanLiftGaloisAction.lean`, `Source_ReferenceIutCanLiftGaloisRamification.lean` and `Source_ReferenceIutCanLiftUnramifiedClosure.lean` use the normal closure inside the same algebraic closure, its Galois action on the normalized coordinate ring, and multiplicativity of ramification indices. The complex descent theorem consumes `CanLift27ComplexAutomorphismsFixX`. It uses the algebraic closure result to transfer the fixed-element property to the original finite cover. [Leaf](receipts/round-ci-021620-8c518d6c-result.json) · [Project and axiom review](receipts/round-ci-021631-5a00aac0-result.json) · [Independent trilingual readback](readbacks/canlift-closure-trilingual.md)

## Galois structure of the tripodal field

`Source_TripodTpdGalois.lean` adapts `Iut/Tripod/TpdGalois.lean`. The six Legendre parameters above the same $j$ value are rational expressions in the selected parameter. Their splitting field over the field of moduli is the actual tripodal field of `curveOf x h3 h5`. This gives the Galois property and the relative degree bound used in (R4). [Leaf](receipts/round-ci-021635-02f7a659-result.json) · [Project and axiom review](receipts/round-ci-021651-5fdc99f2-result.json) · [Independent trilingual readback](readbacks/relative-galois-serre-trilingual.md)

## The lattice point map and modular j surjectivity

`Source_ReferenceHeightsLatticePointMap.lean` and `Source_ReferenceHeightsLatticePointMapInjectivity.lean` send a lattice point to the point at infinity and use the Weierstrass function and its derivative elsewhere. The fiber criterion uses equality of both coordinates. `Source_ReferenceHeightsModularRange.lean` adapts `Heights/ModularJ.lean:355` by proving the image is nonempty, open and closed, using the cusp bound to control sequences in the fundamental domain. [Point map](receipts/round-ci-021618-bdf4e6c7-result.json) · [Injectivity](receipts/round-ci-021637-da4eea75-result.json) · [Modular range](receipts/round-ci-021638-e2d71441-result.json) · [Project and axiom review](receipts/round-ci-021652-c41c2a60-result.json) · [Independent trilingual readback](readbacks/heights-lattice-point-and-range-trilingual.md)

`Source_ReferenceHeightsModularComparisons.lean` proves the two bounded differences on the fundamental domain. The differences compare the logarithms of the discriminant and $j$ and compare the logarithm of the imaginary part with the double logarithm of $j$, with the original truncations. [Leaf](receipts/round-ci-021655-fb4d46d2-result.json) · [Project and axiom review](receipts/round-ci-021668-80e34e19-result.json) · [Independent trilingual readback](readbacks/heights-modular-comparisons-trilingual.md)

## Serre's local different bound

`Source_ReferenceIutTowerSerreCore.lean` constructs the residue extension generator and proves that the trace in the chosen quotient is nonzero. `Source_ReferenceIutTowerSerreBound.lean` localizes at the prime below and uses the induced trace on the Chinese remainder factors to prove the ideal nondivisibility in `Iut/Tower/SerreBound.lean`. `Source_ReferenceIutTowerDifferentBound.lean` turns it into the placewise exponent bound and applies it to the same tower as `TowerLocalFacts`. [MCP-CI review of five statements](receipts/round-ci-021693-678cb693-result.json) · [Independent trilingual readback](readbacks/relative-galois-serre-trilingual.md)

## Global different bound in Tower Step II

`Source_ReferenceIutTowerDifferent.lean` applies the local different exponent bound, separates the tame and wild contributions and sums over the finite places of the same torsion field. The logarithmic discriminant is normalized by that field's degree over ℚ. The upper bound uses the normalized different and conductor of the tripodal field, with error $2\log\ell+21$. [Leaf](receipts/round-ci-021692-f4cf2515-result.json) · [Project and axiom review](receipts/round-ci-021730-14751bfe-result.json) · [Trilingual readback](readbacks/tower-arithmetic-trilingual.md)

## Tower arithmetic on the selected theta data

`Source_ReferenceIutTowerArithmetic.lean` adapts `Tower/Main.lean:42`. It assembles (R4), (ii), and (iii) in one `TowerArithmetic D LT TL`. The local facts are about the representation in `D.prime`. Both sums are over `TL.dst` and the different sum uses the normalization of the same `LT`. [Leaf](receipts/round-ci-021729-842755bc-result.json) · [Project and axiom review](receipts/round-ci-021742-eb56803e-result.json) · [Independent trilingual readback](readbacks/tower-arithmetic-trilingual.md)

## Pointwise P7 with the selected q-pilot

`PointThetaData` exposes the initial data and the q-pilot chosen for the same point and prime, with the existing six identities and bounds. `concreteThetaDataExistence_of_pointwise` consumes local theory and tower arithmetic for that selected object, including its actual q-pilot bad characteristics. It makes the arithmetic input a condition on those selected data. [Leaf](receipts/round-ci-021734-e798309d-result.json) · [Project and axiom review](receipts/round-ci-021743-f33906a6-result.json)

## Infinite-place local theory

`Source_ReferenceIutConcreteLocalArchimedean.lean` supplies the projective integral unit ball, normalized Haar volume, least radial hull, and the logarithm shell scaled by $\pi^{|I|}$. It proves the invariance and admissibility properties of the factor automorphisms used for Proposition 1.5. [Leaf](receipts/round-ci-021732-661a23a8-result.json) · [Project and axiom review](receipts/round-ci-021744-b251f5a2-result.json)

## Finite-place local theory

`Source_ReferenceIutConcreteLocalHaar.lean` and `Source_ReferenceIutConcreteLocalFiniteHull.lean` give the normalized Haar volume, its precise prime-preimage scaling law, and the least principal hull for admissible regions. The scaling law uses the tuple over the same rational prime. The least-hull theorem also handles the zero-ring packet. These results supply the corresponding fields of `LocalTheory`. The source declarations are in [Haar.lean](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Concrete/LocalConstruct/Haar.lean#L221), [Volume.lean](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Concrete/LocalConstruct/Volume.lean) and [Hull.lean](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Concrete/LocalConstruct/Hull.lean#L159). [Project and axiom review](receipts/round-ci-021756-7f9a2015-result.json)

`Source_ReferenceIutConcreteLocalFiniteIndeterminacy.lean`, `Source_ReferenceIutConcreteLocalFiniteLogShell.lean` and `Source_ReferenceIutConcreteLocalProp14.lean` supply the finite automorphisms, the saturated log-shell, and Proposition 1.4(iii)–(iv). The genuine packet uses the transported Scene1 saturated shell. The other branch uses its integral region. Proposition 1.4(iii) uses the same all-over-prime hypothesis, retains the different and ramification terms, and uses the principal region scaled by the rational prime raised to the floor of the normalized order. [Indeterminacy](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Concrete/LocalConstruct/Indeterminacy.lean) · [LogShell](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Concrete/LocalConstruct/LogShell.lean) · [Proposition 1.4](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Concrete/LocalConstruct/Prop14.lean#L161) · [Project and axiom review](receipts/round-ci-021801-bea652a9-result.json) · [Independent trilingual readback](readbacks/finite-place-tensor-trilingual.md)

`Source_ReferenceIutConcreteLocalTheory.lean` assembles all 41 fields of the local theory on one number field. Its finite branch uses the Haar, hull, indeterminacy and log-shell laws above. Its archimedean branch uses the projective integral unit ball and radial hull. `PointThetaData.localTheory` instantiates this construction on the point's own torsion field. [Pinned Theory.lean](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Concrete/LocalConstruct/Theory.lean) · [Leaf](receipts/round-ci-021818-2b32f85f-result.json) · [Project and axiom review](receipts/round-ci-021840-0b7a0de4-result.json) · [Independent trilingual readback](readbacks/concrete-local-theory-trilingual.md)

## CanLift analytic reduction

The polynomial descent expresses a holomorphic function constant on first-coordinate fibers as a polynomial in that coordinate under the stated growth bound. The lift lemmas give precomposition by the deck action and vanishing from a zero at one point for a continuous lift of an integral element. The invariant-coordinate and complex descent arguments consume these facts. [Pinned FEtLattice.lean](https://github.com/lana-agents/oka/blob/75dcdc3faadd10b986afb9283e89902bcdddecd4/Oka/Uniformization/FEtLattice.lean) · [Pinned FEtTransitive.lean](https://github.com/lana-agents/oka/blob/75dcdc3faadd10b986afb9283e89902bcdddecd4/Oka/Uniformization/FEtTransitive.lean) · [Project and axiom review](receipts/round-ci-021835-440b2a29-result.json) · [Independent trilingual readback](readbacks/canlift-analytic-reduction-trilingual.md)

`fixes_normalization_x` adapts Theorem G to the unsigned normalization at level one. Passing the same evaluation map `ι₀` to `locPres_of_unramified` fixes the two argument mismatches in the preceding leaf. Four `letI` style warnings remain. [Pinned Theorem G](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/U2/TheoremG.lean) · [Failed leaf](receipts/round-ci-021897-2cc87a88-result.json) · [Main agent leaf](receipts/round-ci-021922-e0a843dc-result.json)

A subagent edited FixX and the review materials in the shared workspace and submitted four overlapping jobs with the main agent ID, contrary to `AGENTS.md`. The leaf and artifact jobs for FixX used the same source hash as the main agent's jobs. The main agent's downstream artifact was built after all four jobs reached terminal status and was followed by the independent project and axiom review cited below. [Subagent leaf](receipts/round-ci-021918-abdd1b9d-result.json) · [Subagent artifact](receipts/round-ci-021931-6e6d6b06-result.json) · [Subagent assembly](receipts/round-ci-021940-93a275bd-result.json) · [Subagent review](receipts/round-ci-021941-ad2fc0d6-result.json) · [Main agent downstream artifact](receipts/round-ci-021947-ff1caaa2-result.json)

## Actual local theta data on the selected point

The completion-place comparison transports the Tate parameter and supplies its `2ℓ`-th root when the given curve has rational 2-torsion. The order formula uses the same normalized valuation and the weighted sum uses the actual bad places above each rational prime. `concreteThetaDataExistence_of_localArithmetic` takes the concrete theory and root data for the selected point and uses its own q-pilot. The anabelian existence, rational 2-torsion, and tower arithmetic remain explicit in its interface. [Pinned local data](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Concrete/ThetaLocalConstruct/Data.lean) · [Pointwise source](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/Main.lean#L86) · [Project and axiom review](receipts/round-ci-021884-70058d70-result.json) · [Independent trilingual readback](readbacks/point-local-theta-trilingual.md)

## Step III for the chosen Legendre curve

The Legendre tower is unramified from the actual tripodal field to the torsion field at the good places required by `TowerLocalFacts.relRamIdx_eq_one`. At the specified bad places the ramification index from the field of moduli to the tripodal field is at most two. The consumer `step_iii_of_curve` uses those two results with the actual bad-characteristic set and the tripodal Galois instance. Its remaining tower premises are the wild bound and the bound of `30 * ℓ` away from `{2, 3, 5, ℓ}`. [Unramified source](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/Unramified.lean#L376) · [Tripodal ramification source](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/TpdRamIdx.lean) · [Project and axiom review](receipts/round-ci-021885-759d4e11-result.json) · [Independent trilingual readback](readbacks/tripod-step-iii-trilingual.md)

## The complex six-power torsion bound

The lattice point map is additive and gives the required uniformization of the lattice model. Its combination with modular `j` surjectivity and the two fundamental-domain comparisons proves the general six-power bound for complex elliptic curves. The Legendre specialization supplies the witness used to choose `C₀`. The cyclic subgroup consumer takes the Vélu estimate at the same constant. [General bound and Legendre specialization](../../../Solutions/Source_ReferenceHeightsTorsionBound.lean#L12) · [Cyclic consumer](../../../Solutions/Source_TripodCyclicBoundFromSource.lean#L28) · [Project and axiom review](receipts/round-ci-021929-7709d914-result.json) · [Independent trilingual readback](readbacks/heights-torsion-bound-trilingual.md)

## Complex CanLift with the commensurator condition

For each complex elliptic curve outside the four exceptional `j`-values, the input supplies a uniformization on which every element of the commensurator fixes the first coordinate. The proof uses holomorphic lift transitivity and the commensurator membership of a lift of each covering automorphism. It descends the unchanged first coordinate through the unramified Galois closure, then applies the rigidity and uniqueness of the sign quotient cover. The conclusion is `CanLift27Complex`. The uniformization with the stated commensurator property and both steps of the characteristic-zero Lefschetz descent remain open. [Complex assembly](../../../Solutions/Source_ReferenceIutCanLiftComplexAssembly.lean#L21) · [Project and axiom review](receipts/round-ci-021953-47fff188-result.json) · [Independent trilingual readback](readbacks/canlift-complex-assembly-trilingual.md)

## The archimedean Vélu bound

`translate_torsion` shows that translating a nonzero 2-torsion point and its half by an element of the odd-order subgroup gives nonzero `4ℓ`-torsion points. `arch_bound` applies the same Legendre bound at an infinite place to all translated points. The product identity bounds the norm of the ratio times the coordinate difference by `2 * ℓ * (C₀ * (4 * ℓ)^2)`. This is the archimedean input of the source product-formula argument. The finite-place estimates and descent for the specified pairs remain open. [Source translation](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/CyclicIsogeny.lean#L312) · [Source archimedean bound](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/CyclicIsogeny.lean#L379) · [Leaf](receipts/round-ci-022014-09446e67-result.json) · [Project and axiom review](receipts/round-ci-022033-6796478f-result.json) · [Independent trilingual readback](readbacks/cyclic-velu-arch-trilingual.md)

## Tripodal inertia port

A second subagent wrote the initial slope, difference, unipotence and inertia-transport drafts into the shared workspace and submitted jobs under `p2m-tripod-ramification-01a1f197`. The recorded subagent jobs were terminal when the main agent resumed integration. The main agent rechecked the current slope, difference and unipotence inputs and repaired the transport proof to use the same Mathlib action on the ring of integers throughout. [Subagent difference](receipts/round-ci-021991-7662100c-result.json) · [Subagent unipotence](receipts/round-ci-022001-1fee8709-result.json) · [Subagent transport attempt](receipts/round-ci-022010-a963a37c-result.json) · [Main agent slope](receipts/round-ci-022015-3e3c904e-result.json) · [Main agent difference](receipts/round-ci-022049-e341f915-result.json) · [Main agent unipotence](receipts/round-ci-022051-05edc933-result.json) · [Main agent transport](receipts/round-ci-022044-baf5816d-result.json)

## Legendre torsion-field ramification away from 2 and ℓ

For the Legendre curve selected by `CurveProviders`, the inertia action on the `ℓ`-torsion at a place above `badT` has exponent dividing `ℓ` when the residue characteristic differs from 2 and `ℓ`. The slope and difference lemmas imply the iteration formula on prime-to-residue-characteristic odd torsion. The finite-place proof uses the Legendre changes with parameters `λ`, `1 - λ`, and `λ⁻¹`. At bad places, faithfulness on torsion and the equality of `[K : F]` with the order of the mod-`ℓ` image, which divides `|GL₂(F_ℓ)|`, bound the inertia order by `ℓ`. At good places the existing index-one theorem gives the bound directly. Thus `relRamIdx_torsionField_le` bounds the relative index in `K/F` by `ℓ` at every place in this residue-characteristic range. `TowerFacts` combines it with the remaining bound for `F/F_tpd`. [Source](https://github.com/lana-agents/iut/blob/10e40d2e52a8e7220c2a90ff1595f5b385f987ef/Iut/Tripod/BadRamIdx.lean#L197) · [Leaf](receipts/round-ci-022116-17838ef4-result.json) · [Project and axiom review](receipts/round-ci-022183-c7d6f502-result.json) · [Trilingual readback](readbacks/tripod-bad-ram-idx-trilingual.md)

The first check timed out (ci-022092-641f0296). The second reported a valuation equivalence and a point-type transparency mismatch (ci-022108-55ef14ea). The successful check uses the two explicit directions of the valuation equivalence and a point typed on the base-changed Legendre model. The initial review ci-022125-19cce7ec timed out while scanning all declarations. The replacement prints and checks the transitive axioms of the three mathematical conclusions above.

## The ramification bound over the tripodal field

The representations `repF` on 3- and 5-torsion act on the same Legendre curve over `F`. At a bad place outside residue characteristics 2, 3 and 5, the subgroup `I⁺` fixing the two chosen Legendre square roots has index at most two in inertia. Its two representations are jointly faithful and their elements have orders dividing 3 and 5, respectively. The kernel and image bounds give `|I⁺| ≤ 15`, and hence `e(F/F_tpd) ≤ 30` at those places. Multiplying with the index in `K/F`, and using index one in the good lower branch, proves the `30ℓ` bound over `F_tpd` outside `2, 3, 5, ℓ`. The proof splits the representation powers, joint faithfulness and finite-group count to stay within default heartbeats. [Source inertia argument](https://github.com/lana-agents/iut/blob/04283ddb9192c9fb4d5863ce2cf057741556cbf0/Iut/Tripod/TpdInertia.lean) · [Source tower consumer](https://github.com/lana-agents/iut/blob/2d8f000457da6447fa4df4bfec7365c1a49b6384/Iut/Tripod/TowerFacts.lean#L46) · [Leaf](receipts/round-ci-022222-f3a919cf-result.json) · [Project and axiom review](receipts/round-ci-022255-2c5b55c1-result.json) · [Trilingual readback](readbacks/tripodal-inertia-trilingual.md)

## Two designated Vélu point pairs

The square roots selected over `F` give two distinct nonzero points `T₁,T₂` killed by 2 and points `R₁,R₂` with `2Rᵢ = Tᵢ`. After base change to the actual ℓ-torsion field, the two coordinate differences are the images of `-√λ` and `-√(1-λ)`. The base-change identity identifies these points with the corresponding points in the chosen algebraic closure. The ratio descent will combine them with the chosen odd-order subgroup. [Point definitions and consumers](../../../Solutions/Source_TripodCyclicVeluPoints.lean#L168) · [Leaf](receipts/round-ci-022232-d1190d06-result.json) · [Project and axiom review](receipts/round-ci-022264-0b6cd23c-result.json) · [Trilingual readback](readbacks/cyclic-velu-points-trilingual.md)

## Descent of the designated Vélu ratios

The actual `ℓ`-torsion field contains every point of the geometric subgroup of order `ℓ`. Base change identifies its preimage `HL` with the original subgroup and transports each ratio. The two ratios are nonzero because the subgroup has odd order and the points satisfy the designated doubling formulas. Under Galois stability of the subgroup, their product descends to a nonzero element of `F` and satisfies the logarithmic product formula there. This supplies the product formula required to sum the finite-place and infinite-place estimates. [Source descent](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/CyclicIsogeny.lean#L273) · [Leaf](receipts/round-ci-022337-967b971f-result.json) · [Project and axiom review](receipts/round-ci-022356-38c5d13c-result.json) · [Trilingual readback](readbacks/cyclic-velu-descent-trilingual.md)

## Tame ramification in residue characteristic 2

At a place above 2, the stable model supplied by the Legendre curve has unit discriminant or unit `c₄` after a change of variables over `F`. Integral coordinates for the odd torsion and the tangent-slope calculation imply that an inertia involution acts trivially on that torsion. Its action is faithful, so inertia has odd order by Cauchy's theorem. This gives the characteristic 2 case of tameness for `K/F`. A downstream import detected a name collision between generated local instances. The final artifact gives the instance an explicit name. [Reference](https://github.com/lana-agents/iut/blob/2d8f000457da6447fa4df4bfec7365c1a49b6384/Iut/Tripod/TameTwo.lean#L206) · [Final artifact](receipts/round-ci-022406-aa16afa6-result.json) · [Project and axiom review](receipts/round-ci-022416-8f790241-result.json) · [Trilingual readback](readbacks/tame-two-trilingual.md)

## Wild ramification of the Legendre tower

The action on the signs of the three square roots and on the 3- and 5-torsion proves that the lower degree divides 184320. The upper degree divides the order of the mod-ℓ general linear group. At odd residue characteristic distinct from ℓ, the known good-place index-one and bad-place inertia exponent prove tameness. Multiplicativity of relative indices and the two degree divisibilities give the wild bounds 12, 2, 1 and 1 at residue characteristics 2, 3, 5 and ℓ respectively, and 0 elsewhere. The output is the wild ramification field of `TowerLocalFacts` for the actual Legendre torsion field. [Reference tower bound](https://github.com/lana-agents/iut/blob/2d8f000457da6447fa4df4bfec7365c1a49b6384/Iut/Tripod/WildRamIdx.lean#L183) · [Leaf](receipts/round-ci-022410-f598c120-result.json) · [Project and axiom review](receipts/round-ci-022416-8f790241-result.json) · [Trilingual readback](readbacks/wild-ramification-trilingual.md)

## Local facts on the actual Legendre tower

The admissible prime data uses the same representation as the curve. The wild bound, the unramified assertion over a good tripodal place outside the exceptional characteristics, and the bound 30ℓ form one `TowerLocalFacts` for its torsion field. `step_iii_of_curve_from_source` evaluates the sum over the distinguished primes selected by the same q-pilot and uses the known bound on lower ramification over bad moduli places. [Reference](https://github.com/lana-agents/iut/blob/2d8f000457da6447fa4df4bfec7365c1a49b6384/Iut/Tripod/TowerFacts.lean#L99) · [Leaf](receipts/round-ci-022425-1c8a3663-result.json) · [Project and axiom review](receipts/round-ci-022444-83f19d6e-result.json) · [Trilingual readback](readbacks/tripod-tower-local-facts-trilingual.md)

## Pointwise P7 with tower arithmetic from the Legendre curve

The theorem supplies the concrete local data for each admissible point and prime of the curve inputs built by `curveInputs_from_source`. It uses the Legendre curve's rational 2-torsion and builds (R4), (ii) and (iii) for one local theta datum on the field of the selected initial datum. Its inputs retain the curve providers, the cyclic subgroup estimate in `CF`, core finiteness, Northcott and anabelian existence. [Reference P7](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/Main.lean#L86) · [Leaf](receipts/round-ci-022436-76b5a5d1-result.json) · [Project and axiom review](receipts/round-ci-022444-83f19d6e-result.json) · [Trilingual readback](readbacks/tripod-p7-trilingual.md)

## The Legendre Newton bound and transport of Vélu estimates

For a Legendre curve over a number field, the coordinate change $x=\lambda^2 X$, $y=\lambda^3 Y$ gives an integral model at finite places with $|\lambda|>1$. The weighted Newton estimate after rescaling gives $|n|^2|x|\le\max(1,|\lambda|)^2$ for the given $n$-torsion. The Vélu sum then gives a bound for each ratio on the same torsion field. The two finite bounds descend via the positive power $ef$. At an infinite place the absolute-value equality for restriction transports the two bounds with the original $C_0$. [Newton source](../../../../refer/iut/Iut/Tripod/TorsionNewton.lean#L141) · [Transport source](../../../../refer/iut/Iut/Tripod/CyclicIsogeny.lean#L574) · [Project and axiom review](receipts/round-ci-022561-d4e2ce4d-result.json) · [Trilingual readback](readbacks/cyclic-velu-finite-trilingual.md)

## Countable coefficient model for CanLift

The primitive element of the finite cover, its monic minimal polynomial, the two coordinate expressions, and the curve coefficients determine a countable algebraically closed subfield. The finite lower extension contains both coordinates. Extension of constants recovers the upper extension inside the original ambient field. This is the input for descent of integrality and equality of ramification multiplicities. [Pi1 source](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/LefschetzMain.lean#L129) · [Project and axiom review](receipts/round-ci-022572-9dbbddda-result.json) · [Trilingual readback](readbacks/canlift-countable-cover-field-trilingual.md)

## Reference Corollary 2.2 on the canonical auxiliary height

The reference `I.c2` consumes the fully quantified concrete Legendre P7 family conditional on its curve and geometric inputs. The selected $x$ uses the canonical point, different and conductor. Its provider height agrees with `auxiliaryHeight`. The exceptional set, threshold and additive constant use the same `I` as the proof. The statement retains the cyclic estimate, finiteness of the core exceptions, anabelian existence, prime estimates and the universal `h312` premise. [Reference construction](../../../../refer/iut/Iut/Tripod/Main.lean#L119) · [Project and axiom review](receipts/round-ci-022584-92ffefcd-result.json) · [Trilingual readback](readbacks/tripod-canonical-corollary22-trilingual.md)

## Vélu estimate at odd multiplicative places

The Tate graph-line hypothesis on the torsion field gives the bound for the fourth power of the product of the two designated Vélu ratios. The identification of the Tate and original j-invariants supplies the factor $|j|_w^{ℓ-1}$. The same inequality descends to a finite place of the base field via the positive local degree. The bound also applies when the residue characteristic is $ℓ$. [Reference](../../../../refer/iut/Iut/Tripod/CyclicIsogeny.lean#L425) · [Project and axiom review](receipts/round-ci-022670-0b60f6c5-result.json) · [Trilingual readback](readbacks/cyclic-velu-tate-trilingual.md)

## Integrality under extension of constants for CanLift

For a transcendental parameter $t$, the polynomial ring over $K$ intersects $k(t)$ in $k[t]$. If $k$ is algebraically closed, $k(t)$ is relatively algebraically closed in $K(t)$. Minimal polynomials of elements algebraic over $k(t)$ commute with the change of constants. These identities give descent of integrality and compatible injective maps of normalization rings. [Pi1 descent](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Descent.lean#L96) · [Project and axiom review](receipts/round-ci-022670-0b60f6c5-result.json) · [Trilingual readback](readbacks/canlift-constant-extension-trilingual.md)

## Conditional Lefschetz assembly for CanLift

Every countable field of characteristic zero embeds in the complex numbers. The four exclusions on the j-invariant are preserved and reflected along embeddings. The assembly takes the complex result, descent along a field embedding and determination by countable algebraically closed subfields as explicit inputs to derive `CanLift27.{0}`. [Pi1 assembly](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/LefschetzMain.lean#L280) · [Project and axiom review](receipts/round-ci-022670-0b60f6c5-result.json) · [Trilingual readback](readbacks/canlift-lefschetz-assembly-trilingual.md)

## Placewise logarithmic Vélu estimates

The finite-place estimate separates odd multiplicative places, places of residue characteristic two, and the remaining finite places. At odd multiplicative places the Tate inequality supplies the negative multiple of the logarithm of the local absolute value of the j-invariant. The infinite-place estimate retains the same complex torsion bound and its constant $C_0$. These estimates supply the terms for the global sum. [Reference](../../../../refer/iut/Iut/Tripod/CyclicIsogeny.lean#L662) · [Project and axiom review](receipts/round-ci-022720-25476fb9-result.json) · [Trilingual readback](readbacks/cyclic-velu-log-trilingual.md)

## Galois closure under extension of constants for CanLift

A Galois closure of the lower finite cover extends to a Galois closure containing the compositum over the larger constant field. Restriction gives an injective map on Galois groups and respects the fixed subgroups and inertia under contraction. For algebraically closed lower constants and a transcendental parameter, restriction is also surjective under the compositum hypothesis. Equality of ramification indices requires the subsequent ramification comparison. [Pi1 source](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/BaseChange.lean) · [Project and axiom review](receipts/round-ci-022720-25476fb9-result.json) · [Trilingual readback](readbacks/canlift-constant-extension-galois-trilingual.md)

## Mod-ell representation of the Legendre curve provider

The Legendre curve over the selected field has the original Legendre equation after base change to the algebraic closure. Its torsion basis transports along this equality. The mod-$ℓ$ representation has the required action on geometric torsion and an open kernel. The provider constructor takes the arithmetic of each selected curve as an explicit input. [Reference provider](../../../../refer/iut/Iut/Tripod/Providers.lean) · [Project and axiom review](receipts/round-ci-022720-25476fb9-result.json) · [Trilingual readback](readbacks/tripod-provider-representation-trilingual.md)

## Ramification indices under extension of constants for CanLift

For a finite tower of normalized function fields, choose a maximal ideal of the upper normalization after extending constants. If its contraction to the original upper normalization is nonzero, the relative ramification indices agree at the two ideals. The proof compares inertia in Galois closures and cancels the common positive factor in the tower. [Project and axiom review](receipts/round-ci-022759-424cfbc4-result.json) · [Trilingual readback](readbacks/canlift-constant-extension-ramification-trilingual.md)

## Six-torsion rationality of the selected Legendre curve

The selected field contains the chosen square root of minus one. The coordinates of all geometric two-torsion and three-torsion points descend to that field. For a point killed by six, the difference of its triple and its double equals the original point, so it descends to the same field. [Reference](../../../../refer/iut/Iut/Tripod/CurveFacts.lean#L151) · [Project and axiom review](receipts/round-ci-022759-424cfbc4-result.json) · [Trilingual readback](readbacks/tripod-provider-rationality-trilingual.md)

## Descent of étale maps under extension of constants for CanLift

When the lower constant field is algebraically closed, each closed point of the lower normalization has a closed point above it after extension of constants. By comparing ramification indices and the two prescribed multiplicities at nonzero contractions, the proof descends the étale condition on the map of affine orbicurve presentations. [Project and axiom review](receipts/round-ci-022789-a679c21f-result.json) · [Trilingual readback](readbacks/canlift-constant-extension-etale-trilingual.md)

## The global Vélu bound

For a point in the compactly bounded subset, the placewise estimates on the descended ratio combine by the product formula. The local degrees and the compact bounds control the finite and infinite contributions. The odd bad-place sum identifies the height difference. The final bound retains the chosen $C_0$, the Galois-stable subgroup and the Tate graph-line hypothesis. [Reference](../../../../refer/iut/Iut/Tripod/CyclicIsogeny.lean#L831) · [Project and axiom review](receipts/round-ci-022808-047a35ae-result.json) · [Trilingual readback](readbacks/cyclic-velu-main-bound-trilingual.md)

## The fixed-constant cyclic subgroup bound

The public complex torsion bound supplies the constant for the Legendre family. The odd multiplicative place theorem supplies the graph-line condition. The global Vélu bound then proves the public cyclic subgroup estimate at the constant specified in its statement. [Reference](../../../../refer/iut/Iut/Tripod/CyclicIsogeny.lean#L1064) · [Project and axiom review](receipts/round-ci-022825-5942080c-result.json) · [Trilingual readback](readbacks/tripod-cyclic-bound-odd-trilingual.md)

## Forward étale transport under extension of constants for CanLift

At a closed point whose contraction is zero, restriction to the original Galois closure identifies the inertia group as trivial. The ramification index is therefore one. At a point with nonzero contraction, the ramification index and the two prescribed multiplicities agree with their values before extension of constants. These identities transport the étale condition to the larger constant field. [Pi1 source](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L148) · [Project and axiom review](receipts/round-ci-022835-61a98993-result.json) · [Trilingual readback](readbacks/canlift-constant-extension-forward-trilingual.md)

## Ramification under a change of parameter for CanLift

Mutual integrality of the two parameters identifies the normalization rings inside the same ambient field. The new parameter field still has finite extension degree. The polynomial parameter map preserves the prescribed ramification condition via the isomorphisms of the base and normalization rings. [Pi1 source](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L296) · [Project and axiom review](receipts/round-ci-022835-61a98993-result.json) · [Trilingual readback](readbacks/canlift-change-parameter-trilingual.md)

## Multiplicities of the sign quotient under extension of constants

The sign-quotient multiplicity equals the ramification index of the quadratic coordinate field. The quadratic coordinate equation supplies the finite Galois extension over both constant fields. The ramification comparison then gives equality of multiplicities at closed points with nonzero contraction. [Pi1 source](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/HemiTY.lean) · [Project and axiom review](receipts/round-ci-022835-61a98993-result.json) · [Trilingual readback](readbacks/canlift-sign-multiplicity-trilingual.md)

## Canonical Corollary 2.2 with the proved cyclic bound

`canonicalCorollary22HighHeightEstimate_of_cyclicBound` supplies the `CurveFactsProp` premise of the source assembly with `cyclicBoundOdd` at the fixed constant. It still takes the curve provider, core finiteness, anabelian existence, both prime estimates and the universally quantified `h312` for the concrete theta data. [Project and axiom review](receipts/round-ci-022840-3258b7f9-result.json) · [Trilingual readback](readbacks/tripod-canonical-corollary22-cyclic-trilingual.md)

## Descent of a quadratic cover map for CanLift

The change of parameter and extension of constants give compatible contractions on the polynomial lines. The sign-quotient multiplicities agree under that compatibility at nonzero contractions. The étale identity consequently descends to the smaller constant field and the given quadratic-cover rigidity condition identifies the value of the descended map. [Pi1 source](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean) · [Project and axiom review](receipts/round-ci-022857-2bd71c3a-result.json) · [Trilingual readback](readbacks/canlift-descended-cover-trilingual.md)

## Realization of finite covers over a general base field

A chosen transcendental integral parameter realizes both affine coordinate rings as normalizations inside the same algebraic closure of a rational function field. The cover map corresponds to the inclusion of those normalizations. The general realization retains the complex specialization used by the existing CanLift route. [Project and axiom review](receipts/round-ci-022884-1f96e82a-result.json) · [Trilingual readback](readbacks/canlift-realization-trilingual.md)

## The quadratic Weierstrass model for CanLift

The Weierstrass coordinate equation with a transcendental first coordinate yields a function-field embedding at the two chosen coordinates. The signed and unsigned normalization rings identify with the two rings in the quadratic model. Their canonical map is compatible with the inclusion of normalization rings in the same ambient field. [Project and axiom review](receipts/round-ci-022884-1f96e82a-result.json) · [Trilingual readback](readbacks/canlift-quadratic-model-trilingual.md)

## Core criterion and extension of a quadratic cover

The characteristic-zero unramified Galois closure and uniqueness of maps on each cover give the core criterion. Forward extension of a quadratic cover preserves its étale condition, so upper-field rigidity implies lower-field rigidity. [Project and axiom review](receipts/round-ci-022911-3f6a3a0a-result.json) · [Trilingual readback](readbacks/canlift-core-criterion-and-extended-cover-trilingual.md)

## Lefschetz descent on the signed normalization

On the actual signed and unsigned models, core uniqueness and quadratic-cover rigidity imply each other. Rigidity on countable algebraically closed models gives rigidity over the original algebraically closed field. The core property also descends along a field embedding. Both descent theorems supply `canLift27_of_complex`, which takes `CanLift27Complex` as its input. The joint project review checked 13 declarations. Each depends only on `propext`, `Classical.choice`, and `Quot.sound`. [Core comparison](readbacks/canlift-corestar-trilingual.md) · [Countable descent](readbacks/canlift-countable-rigidity-trilingual.md) · [Embedding descent build](receipts/round-ci-023015-92216e88-result.json) · [Project and axiom review](receipts/round-ci-023046-3367d913-result.json)

## Explicit prime estimates for Corollary 2.2

The Chebyshev certificate has threshold $10^{12}$ and factors $2/3$ and $2$. The prime-counting certificate has factor $3/2$ beyond a real threshold greater than one. The canonical Corollary 2.2 specialization consumes both certificates and retains the curve provider, core finiteness, anabelian existence and the universal `h312`. [Reference](../../../../refer/iut/Iut/Implication/ChebyshevExplicit.lean) · [Project and axiom review](receipts/round-ci-022926-2a7dcca5-result.json) · [Chebyshev readback](readbacks/chebyshev-explicit-trilingual.md) · [Prime-counting readback](readbacks/prime-counting-explicit-trilingual.md)

## The q-pilot normalization for Corollary 3.12

For each rational prime, the concrete q-pilot contribution divided by $2\ell$ equals the sum of the negative logarithms of the chosen Tate-root norms over the complete prime fiber, divided by the torsion field degree. The identity tracks the same local theta data and uses the same quantity as the finite-place volume bound. [Project and axiom review](receipts/round-ci-022926-2a7dcca5-result.json) · [Trilingual readback](readbacks/cor312-q-pilot-normalization-trilingual.md)

## Counterexample to the unrestricted Corollary 3.12 premise

Given valid initial theta data, local theta data and a q-pilot, `ThetaLocalData.not_forall_corollary312Variant` refutes the premise over all `LocalTheory` inputs used by the high-height entry point. The construction uses a radius $0<r\le 1$ for the archimedean log-shell and sets the archimedean `indAut` to `{id}`. It keeps the finite-place contributions and the q-pilot fixed. The right-hand side equals its value at radius $1$ plus $\log r$, so it can fall below the fixed left-hand side. The proof of Corollary 3.12 for the full P7 family still needs the source-specific log-shell and measure identities. The project and axiom review checked five declarations with only `propext`, `Classical.choice`, and `Quot.sound`. [Source consumer](../../../../refer/iut/Iut/Tripod/Main.lean#L130) · [Counterexample](../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L369) · [Project and axiom review](receipts/round-ci-023160-024629d3-result.json)

## Corollaries 2.2 and 2.3 on the source P7 family

`IsSourceP7Variant` records an admissible point, the prime and the P7 hypotheses, and equality with the variant bundle constructed by `pointThetaData`. `pointThetaDataExistence_from_source` supplies this equality, the certificate and local estimate for Theorem 1.10, and the arithmetic comparisons on one bundle. The explicit-prime Corollary 2.2 entry applies `c2` to that witness. The Corollary 2.3 entry uses the same curve provider for the comparison with `htCan` and gives `StatementII` using the large-height error bound and Northcott finiteness. The source P7 entries take the curve provider, core finiteness, anabelian existence and the 3.12 inequality on the whole source P7 family as parameters. The joint review checked seven declarations, each using `propext`, `Classical.choice`, and `Quot.sound`. [Source P7](../../../Solutions/Source_TripodP7.lean#L27) · [Corollary 2.2](../../../Solutions/Source_TripodCanonicalCorollary22PrimeEstimates.lean#L26) · [Corollary 2.3](../../../Solutions/Source_TripodStatementIIOnSourceP7.lean#L17) · [Project and axiom review](receipts/round-ci-023226-fcded28f-result.json) · [Trilingual readback](readbacks/tripod-source-p7-statement-ii-trilingual.md)

## Full-fiber and selected-place q-pilot identities

The signed q-pilot left-hand side is the sum of the log norms of the chosen roots over the complete torsion-field fibers above the bad residue characteristics, divided by the absolute torsion-field degree. The moduli-field identity writes the same value as $-\sum_v\log|j|_v/(2\ell[M:\mathbb Q])$ over the moduli places of the q-pilot. With compatible algebra maps, the chosen place above each $v$ gives $\log\|q_{w_v}^{1/(2\ell)}\|/[K_{t,w_v}:M_v]$ in the sum, divided by $[M:\mathbb Q]$. The `pointThetaData` constructor supplies compatibility of the stored map with $M\to F\to K_t$, so the formula applies to the q-pilot of the same source P7 bundle. The identification of these representatives and weights with Joshi's formula and the normalized volume identity are still open. The joint review checked 11 declarations using only `propext`, `Classical.choice`, and `Quot.sound`. [Full-fiber identity](../../../Solutions/Source_ReferenceIutCor312QPilotLeftHandSide.lean#L18) · [Moduli sum](../../../Solutions/Source_ReferenceIutCor312QPilotModuli.lean#L115) · [Selected-place identity](../../../Solutions/Source_ReferenceIutCor312RepresentativeQPilot.lean#L87) · [Point-data specialization](../../../Solutions/Source_ReferenceIutPointModuliMap.lean#L32) · [Project and axiom review](receipts/round-ci-023258-e891f8b6-result.json)

## The moduli-fiber weight in the P7 q-pilot

`pointThetaData_qPilot_lhs_eq_sum_section_log_norm_with_fiber_weight` uses the same P7 point data and the stored section above each bad moduli place. It rewrites the degree $[M:\mathbb Q]$ as $\sum_{a\mid v_{\mathbb Q}}[M_a:\mathbb Q_{v_{\mathbb Q}}]$ using the complete moduli fiber. The denominator of each term is this sum times the relative local degree at the selected place, as in Mochizuki III, Remark 3.1.1(ii). The source comparison still requires identification of the paper's chosen places, completions, and theta volume. Job `ci-023346-02b8f7a4` passed with a local instance syntax warning. Job `ci-023353-65caf5fb` produced the revised artifact without diagnostics. The review confirmed `propext`, `Classical.choice`, and `Quot.sound`. [Mochizuki III](../../../../refer/Mochizuki/Inter-universal_Teichmuller_Theory.md#L2090) · [Lean theorem](../../../Solutions/Source_ReferenceIutCor312PointRepresentativeWeight.lean#L21) · [Review](receipts/round-ci-023357-6f06b3a0-result.json) · [Independent trilingual readback](readbacks/p7-representative-weight-trilingual.md)

## The archimedean theta-hull volume in the concrete local theory

At infinity each factor automorphism preserves the log-shell and the identity belongs to the automorphism set. The theta component therefore equals the log-shell. This is a positive radial scaling of the integral ball, so the product region already belongs to the hull system and equals its own hull. Every component has normalized log-volume $|S|\log\pi$ for the capsule label set $S$. The product weights sum to one, giving the same value for the complete packet. This is the archimedean term of the concrete `RHSData.rhs` used in P7. The first check hit a dependent `Fintype` mismatch. The corrected proof uses the label type of the actual container. The review confirmed `propext`, `Classical.choice`, and `Quot.sound`. [Lean theorem](../../../Solutions/Source_ReferenceIutCor312ArchimedeanVolume.lean#L30) · [Review](receipts/round-ci-023384-21d4e243-result.json) · [Independent trilingual readback](readbacks/p7-archimedean-volume-trilingual.md)

## Finite principal regions in the concrete local theory

At a rational prime $p$, fix a tensor tuple of completions of $K$ and scale the integral closure in the tensor algebra by a nonzero element $x$ of one factor $K_w$. Each factorwise automorphism of the tuple preserves this region. Its union of images therefore equals the region itself. Transporting additive Haar measure through the tensor equivalence gives the exact normalized log-volume $\log\|x\|_w/[K_w:\mathbb Q_p]$. Both equations supply the finite theta packet calculation for `ThetaLocalData`. The first two volume checks reached the default conversion heartbeat. Splitting the measurable equivalence, Haar transport, mass ratio, and tensor dimension resolved the failure. The orbit artifact retained a local instance style warning. Both public declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. [Orbit](../../../Solutions/Source_ReferenceIutConcreteLocalFinitePrincipalOrbit.lean#L107) · [Volume](../../../Solutions/Source_ReferenceIutConcreteLocalFinitePrincipalVolume.lean#L91) · [Project and axiom review](receipts/round-ci-023522-f4c700f6-result.json) · [Independent trilingual readback](readbacks/p7-finite-principal-volume-trilingual.md)

## R3 polynomial covering count for CanLift

The count classifies a nonconstant polynomial when its ramification index times the multiplicity of the marked points is constant on each fiber. For a three-point marked set of multiplicity two, the degree is one, two with a reflection preserving the marked set, or three with a common cube after translation. Applied to the two-torsion roots of a complex Weierstrass curve, the reflection forces $j=1728$ and the common cube forces $j=0$. Excluding these values gives injectivity. The next analytic step is to derive the fiberwise weighted ramification identity from a uniformization and its invariant generator. The joint review checked eight declarations using only `propext`, `Classical.choice`, and `Quot.sound`. [Polynomial classification](../../../Solutions/Source_ReferenceIutCanLiftPolynomialOrbifoldCount.lean) · [Weierstrass application](../../../Solutions/Source_ReferenceIutCanLiftWeierstrassOrbifoldCount.lean#L77) · [Project and axiom review](receipts/round-ci-023324-4a0a2990-result.json) · [Independent trilingual readback](readbacks/canlift-r3-polynomial-orbifold-count-trilingual.md)

## First-coordinate rigidity from an invariant polynomial

The proof adapts the local-order argument in Oka's `Oka/Uniformization/R3.lean` at `75dcdc3faadd10b986afb9283e89902bcdddecd4` under Apache-2.0. On the affine complex Weierstrass curve, the square of the partial derivative in $y$ equals the two-torsion polynomial in $x$. The local order of the first coordinate minus its value is two at the marked points and one elsewhere. Composition with the invariant polynomial multiplies this order by the polynomial's ramification index. A Möbius change of variable has nonzero derivative, so orbit transitivity makes the weighted order constant on each polynomial fiber. The previous R3 count gives injectivity and forces the subgroup to fix the first coordinate. The consumer takes that subgroup to be the commensurator. It still requires the actual uniformization and a positive-degree polynomial whose fibers are commensurator orbits. The first check reported two instance mismatches in derivative proofs. Direct proof terms resolved both. The project review confirmed only `propext`, `Classical.choice`, and `Quot.sound` for both declarations. [Oka source](https://github.com/lana-agents/oka/blob/75dcdc3faadd10b986afb9283e89902bcdddecd4/Oka/Uniformization/R3.lean#L334) · [Rigidity theorem](../../../Solutions/Source_ReferenceIutCanLiftFirstCoordinateRigidity.lean#L151) · [Complex consumer](../../../Solutions/Source_ReferenceIutCanLiftComplexAssembly.lean#L35) · [Review](receipts/round-ci-023417-776cb585-result.json) · [Independent trilingual readback](readbacks/canlift-r3-first-coordinate-trilingual.md)

## MCP-CI receipts for this batch

Each job uses an exclusive worktree. Successful and failed receipt rows use compiler wall time and peak process-tree RSS when available. Timeout rows use the elapsed compile time as a lower bound. The receipt stores the exact source hash, input paths and diagnostics.

| Job | Target | Input SHA-256 prefix | Status | Exit | Wall (s) | CPU total (user + system, s) | Peak RSS (GiB) |
| --- | --- | --- | --- | ---: | ---: | ---: | ---: |
| [`ci-020970-a4f4c181`](receipts/round-ci-020970-a4f4c181-result.json) | `Source_TripodCyclicLocal` | `f92e5ae5ee45` | timeout | unknown | 180.06 | unknown | unknown |
| [`ci-020977-fe33da7d`](receipts/round-ci-020977-fe33da7d-result.json) | `Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound` | `f7d620ede476` | succeeded | 0 | 68.86 | 65.13 (1.95 + 63.18) | 2.93 |
| [`ci-020978-f1a1f43a`](receipts/round-ci-020978-f1a1f43a-result.json) | `Source_ReferenceIutInitialThetaData` | `775b55889862` | succeeded | 0 | 90.70 | 86.63 (3.03 + 83.60) | 4.06 |
| [`ci-020980-21308cab`](receipts/round-ci-020980-21308cab-result.json) | `Source_ReferenceIutTateFamilyBridge` | `af2880f12f37` | timeout | unknown | 180.11 | unknown | unknown |
| [`ci-020982-e9892113`](receipts/round-ci-020982-e9892113-result.json) | `Source_ReferenceIutInitialThetaData` | `775b55889862` | succeeded | 0 | 109.97 | 101.85 (4.17 + 97.68) | 4.10 |
| [`ci-020983-a6aab846`](receipts/round-ci-020983-a6aab846-result.json) | `Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound` | `f7d620ede476` | succeeded | 0 | 73.88 | 67.42 (2.50 + 64.92) | 2.97 |
| [`ci-020991-ef904f5d`](receipts/round-ci-020991-ef904f5d-result.json) | `ReviewInitialThetaData` | `4a13db300c0c` | succeeded | 0 | 168.46 | 161.51 (6.51 + 155.00) | 8.07 |
| [`ci-020992-e7860cdf`](receipts/round-ci-020992-e7860cdf-result.json) | `Source_ReferenceIutQPilot` | `e02ac03f9a8a` | succeeded | 0 | 138.43 | 131.34 (6.25 + 125.09) | 7.50 |
| [`ci-020993-2f7ef46d`](receipts/round-ci-020993-2f7ef46d-result.json) | `Source_TripodCyclicBoundFromSource` | `eff133daf8b7` | succeeded | 0 | 134.16 | 125.76 (5.95 + 119.81) | 7.49 |
| [`ci-020994-651732f6`](receipts/round-ci-020994-651732f6-result.json) | `Source_ReferenceIutTateFamilyBridge` | `af2880f12f37` | succeeded | 0 | 135.79 | 128.84 (11.67 + 117.17) | 7.51 |
| [`ci-021003-044a40f0`](receipts/round-ci-021003-044a40f0-result.json) | `Source_ReferenceIutTateFamilyBridge` | `af2880f12f37` | succeeded | 0 | 173.87 | 159.81 (11.64 + 148.17) | 7.51 |
| [`ci-021004-ca789d9a`](receipts/round-ci-021004-ca789d9a-result.json) | `Source_ReferenceIutQPilot` | `e02ac03f9a8a` | succeeded | 0 | 165.21 | 150.88 (6.95 + 143.93) | 7.53 |
| [`ci-021005-56b64774`](receipts/round-ci-021005-56b64774-result.json) | `Source_TripodCyclicBoundFromSource` | `eff133daf8b7` | succeeded | 0 | 160.83 | 146.70 (5.67 + 141.03) | 7.41 |
| [`ci-021006-ca1443c9`](receipts/round-ci-021006-ca1443c9-result.json) | `Source_TripodCyclicDecomposition` | `7f242f46bbea` | failed | 1 | 79.55 | 72.62 (3.00 + 69.62) | 3.89 |
| [`ci-021007-3ecd62cd`](receipts/round-ci-021007-3ecd62cd-result.json) | `Source_TripodCyclicPrimeSubgroups` | `4122550c81be` | failed | 1 | 44.29 | 38.71 (2.25 + 36.46) | 2.10 |
| [`ci-021008-d1014204`](receipts/round-ci-021008-d1014204-result.json) | `Thm_AbcAdaptation_Tripod_legendre_torsion_x_le` | `324181b6173b` | succeeded | 0 | 55.39 | 50.42 (2.25 + 48.17) | 2.95 |
| [`ci-021009-001c6dff`](receipts/round-ci-021009-001c6dff-result.json) | `Thm_AbcAdaptation_Tripod_Cyclic_main_bound` | `5baf7e423305` | succeeded | 0 | 156.73 | 147.72 (5.37 + 142.35) | 7.38 |
| [`ci-021011-82dde4bc`](receipts/round-ci-021011-82dde4bc-result.json) | `Thm_AbcAdaptation_Tripod_cyclicLocalGraphLine` | `a4e35972784e` | succeeded | 0 | 141.14 | 133.93 (5.26 + 128.67) | 7.38 |
| [`ci-021017-ba34a3d2`](receipts/round-ci-021017-ba34a3d2-result.json) | `Source_ReferenceIutCurveTateFamily` | `4a13527d19df` | timeout | unknown | 180.08 | unknown | unknown |
| [`ci-021018-0891354d`](receipts/round-ci-021018-0891354d-result.json) | `ReviewQPilot` | `690aa3cccbda` | succeeded | 0 | 223.20 | 204.26 (6.20 + 198.06) | 8.07 |
| [`ci-021019-7fdc70e3`](receipts/round-ci-021019-7fdc70e3-result.json) | `ReviewCyclicBoundFromSource` | `e8f91fcb6948` | succeeded | 0 | 219.36 | 201.30 (6.32 + 194.98) | 8.07 |
| [`ci-021020-6f1297ae`](receipts/round-ci-021020-6f1297ae-result.json) | `Source_TripodCyclicDecomposition` | `4d1c24e7f4df` | succeeded | 0 | 116.86 | 102.40 (3.25 + 99.15) | 3.91 |
| [`ci-021021-bcdf50ff`](receipts/round-ci-021021-bcdf50ff-result.json) | `Source_TripodCyclicPrimeSubgroups` | `5f4bf3dbdab3` | succeeded | 0 | 70.30 | 60.65 (2.37 + 58.28) | 2.13 |
| [`ci-021022-78e498d3`](receipts/round-ci-021022-78e498d3-result.json) | `Thm_AbcAdaptation_Tripod_legendre_torsion_x_le` | `324181b6173b` | succeeded | 0 | 114.09 | 104.10 (2.01 + 102.09) | 2.96 |
| [`ci-021023-2d6d01f8`](receipts/round-ci-021023-2d6d01f8-result.json) | `Thm_AbcAdaptation_Tripod_Cyclic_main_bound` | `5baf7e423305` | succeeded | 0 | 198.53 | 184.42 (4.82 + 179.60) | 7.38 |
| [`ci-021025-e4cc585e`](receipts/round-ci-021025-e4cc585e-result.json) | `Thm_AbcAdaptation_Tripod_cyclicLocalGraphLine` | `a4e35972784e` | succeeded | 0 | 174.14 | 167.75 (4.93 + 162.82) | 7.44 |
| [`ci-021036-48c12b04`](receipts/round-ci-021036-48c12b04-result.json) | `Source_ReferenceIutCurveTateFamily` | `4a13527d19df` | failed | 1 | 146.23 | 142.44 (6.51 + 135.93) | 7.50 |
| [`ci-021040-9363a3ed`](receipts/round-ci-021040-9363a3ed-result.json) | `Source_TripodCyclicLocal` | `83442d6e34be` | failed | 1 | 141.25 | 137.01 (9.42 + 127.59) | 7.55 |
| [`ci-021041-a2673082`](receipts/round-ci-021041-a2673082-result.json) | `Thm_AbcAdaptation_Tripod_cyclicBoundOdd` | `336e3a5c9a13` | succeeded | 0 | 135.46 | 127.99 (4.18 + 123.81) | 7.32 |
| [`ci-021042-adaad4f9`](receipts/round-ci-021042-adaad4f9-result.json) | `Sketch_Tripod_cyclicBoundOdd` | `79ce8afa71b6` | succeeded | 0 | 133.09 | 125.96 (4.95 + 121.01) | 7.50 |
| [`ci-021055-c957c548`](receipts/round-ci-021055-c957c548-result.json) | `Source_ReferenceIutCurveTateFamily` | `ff772bb7ddc0` | succeeded | 0 | 251.25 | 234.18 (5.15 + 229.03) | 7.40 |
| [`ci-021057-403b93b0`](receipts/round-ci-021057-403b93b0-result.json) | `Thm_AbcAdaptation_Tripod_cyclicBoundOdd` | `336e3a5c9a13` | succeeded | 0 | 235.35 | 221.03 (5.64 + 215.39) | 7.50 |
| [`ci-021058-664a4c90`](receipts/round-ci-021058-664a4c90-result.json) | `Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory` | `6dedb4b3519b` | succeeded | 0 | 120.28 | 114.81 (4.28 + 110.53) | 4.09 |
| [`ci-021066-3f1df09c`](receipts/round-ci-021066-3f1df09c-result.json) | `Source_TripodCyclicLocal` | `f03181dc9557` | failed | 1 | 200.04 | 198.46 (11.62 + 186.84) | 7.57 |
| [`ci-021067-60f01360`](receipts/round-ci-021067-60f01360-result.json) | `Sketch_Tripod_cyclicBoundOdd` | `79ce8afa71b6` | succeeded | 0 | 193.43 | 188.60 (5.85 + 182.75) | 7.50 |
| [`ci-021069-f33ba10b`](receipts/round-ci-021069-f33ba10b-result.json) | `Source_ReferenceIutPointThetaData` | `9365101b2f77` | timeout | unknown | 180.05 | unknown | unknown |
| [`ci-021071-aa486ce7`](receipts/round-ci-021071-aa486ce7-result.json) | `ReviewCurveTateFamily` | `5293b1677d10` | failed | 1 | 181.70 | 180.21 (5.06 + 175.15) | 8.07 |
| [`ci-021077-6e4a92b6`](receipts/round-ci-021077-6e4a92b6-result.json) | `Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory` | `6dedb4b3519b` | succeeded | 0 | 78.90 | 78.49 (4.64 + 73.85) | 4.13 |
| [`ci-021095-a05fa104`](receipts/round-ci-021095-a05fa104-result.json) | `ReviewCyclicBoundReduction` | `973b04119656` | failed | 0 | 140.89 | 136.41 (5.10 + 131.31) | 7.93 |
| [`ci-021096-88b726c0`](receipts/round-ci-021096-88b726c0-result.json) | `ReviewCurveTateFamily` | `6dd601f9ef74` | succeeded | 0 | 140.83 | 135.67 (6.32 + 129.35) | 8.09 |
| [`ci-021097-81ca14f0`](receipts/round-ci-021097-81ca14f0-result.json) | `Source_ReferenceIutPointThetaData` | `9365101b2f77` | succeeded | 0 | 125.59 | 119.76 (5.62 + 114.14) | 7.51 |
| [`ci-021098-347dc0ca`](receipts/round-ci-021098-347dc0ca-result.json) | `Source_ReferenceIutConcreteFibers` | `a92388593f28` | succeeded | 0 | 59.78 | 56.48 (2.31 + 54.17) | 3.95 |
| [`ci-021104-74aaefd7`](receipts/round-ci-021104-74aaefd7-result.json) | `Source_ReferenceIutConcreteFibers` | `a92388593f28` | succeeded | 0 | 62.73 | 61.57 (3.28 + 58.29) | 4.07 |
| [`ci-021105-c95ca126`](receipts/round-ci-021105-c95ca126-result.json) | `ReviewCyclicBoundReduction` | `973b04119656` | succeeded | 0 | 114.24 | 111.88 (5.29 + 106.59) | 7.97 |
| [`ci-021106-42bed987`](receipts/round-ci-021106-42bed987-result.json) | `Source_ReferenceIutPointThetaData` | `9365101b2f77` | succeeded | 0 | 109.12 | 106.44 (5.35 + 101.09) | 7.52 |
| [`ci-021113-826459f1`](receipts/round-ci-021113-826459f1-result.json) | `ReviewConcreteFibers` | `09206588165c` | succeeded | 0 | 133.94 | 128.84 (5.39 + 123.45) | 8.07 |
| [`ci-021114-34799f4b`](receipts/round-ci-021114-34799f4b-result.json) | `ReviewPointThetaData` | `8bcc85c490cd` | succeeded | 0 | 135.19 | 128.98 (5.00 + 123.98) | 7.80 |
| [`ci-021115-88da22ae`](receipts/round-ci-021115-88da22ae-result.json) | `Source_ReferenceIutConcreteContainer` | `eececb6c54b4` | failed | 1 | 60.05 | 58.71 (3.06 + 55.65) | 4.08 |
| [`ci-021131-9063c9ce`](receipts/round-ci-021131-9063c9ce-result.json) | `Source_TripodCoreGeometry` | `540253206f51` | succeeded | 0 | 56.54 | 56.41 (3.20 + 53.21) | 4.12 |
| [`ci-021135-11c0e597`](receipts/round-ci-021135-11c0e597-result.json) | `Source_TripodCoreGeometry` | `540253206f51` | succeeded | 0 | 57.49 | 57.38 (3.18 + 54.20) | 4.12 |
| [`ci-021139-9792c77f`](receipts/round-ci-021139-9792c77f-result.json) | `Source_TripodCoreModel` | `cc8b83636395` | succeeded | 0 | 56.87 | 56.29 (2.40 + 53.89) | 4.03 |
| [`ci-021144-43a32291`](receipts/round-ci-021144-43a32291-result.json) | `Source_TripodCoreModel` | `cc8b83636395` | succeeded | 0 | 51.16 | 50.44 (2.73 + 47.71) | 4.02 |
| [`ci-021147-606ee1da`](receipts/round-ci-021147-606ee1da-result.json) | `ReviewTripodCoreModel` | `eb8cceff8753` | succeeded | 0 | 115.59 | 114.57 (5.12 + 109.45) | 7.83 |
| [`ci-021167-409d592e`](receipts/round-ci-021167-409d592e-result.json) | `Source_ReferenceIutTowerLocalFacts` | `f6c29d8fe1d8` | succeeded | 0 | 50.82 | 51.60 (6.34 + 45.26) | 4.11 |
| [`ci-021169-b1f48043`](receipts/round-ci-021169-b1f48043-result.json) | `Source_ReferenceIutTowerLocalFacts` | `f6c29d8fe1d8` | succeeded | 0 | 47.17 | 47.43 (5.92 + 41.51) | 4.10 |
| [`ci-021174-f7028043`](receipts/round-ci-021174-f7028043-result.json) | `Source_ReferenceIutConcreteContainer` | `20450654a225` | succeeded | 0 | 48.89 | 46.74 (2.65 + 44.09) | 4.05 |
| [`ci-021175-bb46c6bf`](receipts/round-ci-021175-bb46c6bf-result.json) | `Source_TripodCyclicLocal` | `e08e8712be6b` | failed | 1 | 96.56 | 97.74 (9.40 + 88.34) | 7.57 |
| [`ci-021176-2af17504`](receipts/round-ci-021176-2af17504-result.json) | `Source_ReferenceIutTowerRamIdx` | `76ca9a6bdc8b` | failed | 1 | 56.46 | 55.63 (8.79 + 46.84) | 4.14 |
| [`ci-021187-e20c5b25`](receipts/round-ci-021187-e20c5b25-result.json) | `Source_ReferenceIutConcreteContainer` | `20450654a225` | succeeded | 0 | 65.82 | 65.46 (3.84 + 61.62) | 4.09 |
| [`ci-021188-a24859aa`](receipts/round-ci-021188-a24859aa-result.json) | `Source_TripodCyclicLocal` | `ccd09f0cc498` | succeeded | 0 | 110.73 | 113.11 (11.15 + 101.96) | 7.57 |
| [`ci-021189-233bca40`](receipts/round-ci-021189-233bca40-result.json) | `Source_ReferenceIutTowerRamIdx` | `2eacb7dd8d78` | failed | 1 | 60.83 | 60.25 (9.00 + 51.25) | 4.13 |
| [`ci-021199-884a20d3`](receipts/round-ci-021199-884a20d3-result.json) | `Source_ReferenceIutConcreteThetaRegion` | `4a80cbe5e0e6` | failed | 1 | 129.95 | 123.29 (5.20 + 118.09) | 7.51 |
| [`ci-021200-5a4e6c8b`](receipts/round-ci-021200-5a4e6c8b-result.json) | `ReviewConcreteContainerAndTower` | `0b1b0f4bf453` | succeeded | 0 | 140.52 | 133.87 (5.23 + 128.64) | 7.88 |
| [`ci-021201-c749f731`](receipts/round-ci-021201-c749f731-result.json) | `Source_TripodCyclicLocal` | `ccd09f0cc498` | succeeded | 0 | 124.09 | 122.60 (12.32 + 110.28) | 7.58 |
| [`ci-021202-85bbdf32`](receipts/round-ci-021202-85bbdf32-result.json) | `Source_ReferenceIutTowerRamIdx` | `a1d873ca5b7d` | succeeded | 0 | 61.48 | 59.69 (8.87 + 50.82) | 4.13 |
| [`ci-021207-70c84ff6`](receipts/round-ci-021207-70c84ff6-result.json) | `Source_ReferenceIutConcreteThetaRegion` | `6a72169fb99a` | succeeded | 0 | 118.13 | 112.05 (5.46 + 106.59) | 7.51 |
| [`ci-021208-4b457ebf`](receipts/round-ci-021208-4b457ebf-result.json) | `ReviewCyclicLocal` | `09431ecd0294` | succeeded | 0 | 128.78 | 123.85 (5.50 + 118.35) | 8.08 |
| [`ci-021209-89629b6e`](receipts/round-ci-021209-89629b6e-result.json) | `Source_ReferenceIutTowerRamIdx` | `a1d873ca5b7d` | succeeded | 0 | 59.01 | 57.56 (8.39 + 49.17) | 4.12 |
| [`ci-021214-d2adbcde`](receipts/round-ci-021214-d2adbcde-result.json) | `Source_ReferenceIutConcreteThetaRegion` | `6a72169fb99a` | succeeded | 0 | 117.86 | 113.05 (6.10 + 106.95) | 7.55 |
| [`ci-021215-021e43b6`](receipts/round-ci-021215-021e43b6-result.json) | `ReviewTowerRamIdx` | `fce5ec209699` | succeeded | 0 | 126.43 | 121.66 (4.71 + 116.95) | 7.79 |
| [`ci-021216-16355172`](receipts/round-ci-021216-16355172-result.json) | `Source_ReferenceIutTowerDifferentFormula` | `228a9344fe3f` | failed | 1 | 58.90 | 56.79 (5.84 + 50.95) | 4.11 |
| [`ci-021221-fe31f887`](receipts/round-ci-021221-fe31f887-result.json) | `Source_ReferenceIutConcreteInvariants` | `c8c873064dc7` | failed | 1 | 124.76 | 123.59 (7.09 + 116.50) | 7.54 |
| [`ci-021222-3381d9bc`](receipts/round-ci-021222-3381d9bc-result.json) | `Source_ReferenceIutTowerDifferentArithmetic` | `8c2274572f05` | failed | 1 | 62.28 | 60.54 (7.01 + 53.53) | 4.13 |
| [`ci-021223-4784b8ac`](receipts/round-ci-021223-4784b8ac-result.json) | `Source_ReferenceIutTowerDifferentFormula` | `874201b23ca0` | failed | 1 | 56.61 | 54.44 (5.90 + 48.54) | 4.11 |
| [`ci-021231-c4b187c7`](receipts/round-ci-021231-c4b187c7-result.json) | `Source_ReferenceIutConcreteInvariants` | `86a61728bdc2` | failed | 1 | 105.70 | 102.83 (5.87 + 96.96) | 7.53 |
| [`ci-021232-da1ab244`](receipts/round-ci-021232-da1ab244-result.json) | `Source_ReferenceIutTowerDifferentArithmetic` | `961936b4737b` | succeeded | 0 | 56.25 | 52.88 (6.32 + 46.56) | 4.13 |
| [`ci-021233-977f9c72`](receipts/round-ci-021233-977f9c72-result.json) | `Source_ReferenceIutTowerDifferentFormula` | `e4dd94a30493` | succeeded | 0 | 53.53 | 49.57 (5.57 + 44.00) | 4.11 |
| [`ci-021234-07b064a8`](receipts/round-ci-021234-07b064a8-result.json) | `Source_ReferenceIutConcreteLocalArithmetic` | `0ceef9fbd146` | failed | 1 | 48.46 | 44.32 (2.59 + 41.73) | 4.00 |
| [`ci-021248-f876f76b`](receipts/round-ci-021248-f876f76b-result.json) | `Source_ReferenceIutConcreteInvariants` | `b2ec46092708` | succeeded | 0 | 142.03 | 139.71 (7.26 + 132.45) | 7.54 |
| [`ci-021249-0ae7ab85`](receipts/round-ci-021249-0ae7ab85-result.json) | `Source_ReferenceIutConcreteLocalArithmetic` | `d3450657e94b` | succeeded | 0 | 62.80 | 58.96 (3.18 + 55.78) | 4.07 |
| [`ci-021250-226b76a1`](receipts/round-ci-021250-226b76a1-result.json) | `Source_ReferenceIutTowerDifferentArithmetic` | `961936b4737b` | succeeded | 0 | 63.85 | 61.97 (7.82 + 54.15) | 4.13 |
| [`ci-021251-2e43e50b`](receipts/round-ci-021251-2e43e50b-result.json) | `Source_ReferenceIutTowerDifferentFormula` | `e4dd94a30493` | succeeded | 0 | 70.89 | 67.49 (6.35 + 61.14) | 4.11 |
| [`ci-021252-dea0c46b`](receipts/round-ci-021252-dea0c46b-result.json) | `Source_ReferenceIutTowerIdealOrder` | `3c3ca179bf74` | succeeded | 0 | 62.44 | 59.63 (2.85 + 56.78) | 3.92 |
| [`ci-021253-b0249bd2`](receipts/round-ci-021253-b0249bd2-result.json) | `Source_ReferenceIutTowerQuotientBasis` | `85bc4665e960` | succeeded | 0 | 60.98 | 60.24 (2.90 + 57.34) | 3.20 |
| [`ci-021258-004275f0`](receipts/round-ci-021258-004275f0-result.json) | `Source_ReferenceIutConcreteInvariants` | `b2ec46092708` | succeeded | 0 | 140.27 | 137.37 (6.98 + 130.39) | 7.54 |
| [`ci-021259-24d648fa`](receipts/round-ci-021259-24d648fa-result.json) | `Source_ReferenceIutConcreteLocalArithmetic` | `d3450657e94b` | succeeded | 0 | 69.76 | 66.63 (2.96 + 63.67) | 4.08 |
| [`ci-021260-58b07a74`](receipts/round-ci-021260-58b07a74-result.json) | `Source_ReferenceIutTowerIdealOrder` | `3c3ca179bf74` | succeeded | 0 | 67.19 | 64.45 (2.75 + 61.70) | 3.88 |
| [`ci-021261-6388f35f`](receipts/round-ci-021261-6388f35f-result.json) | `Source_ReferenceIutTowerQuotientBasis` | `85bc4665e960` | succeeded | 0 | 47.68 | 45.07 (2.28 + 42.79) | 3.12 |
| [`ci-021263-eac61cdf`](receipts/round-ci-021263-eac61cdf-result.json) | `Source_ReferenceIutTowerStepIII` | `d9cf0fe0dcbe` | failed | 1 | 83.76 | 86.70 (20.60 + 66.10) | 4.26 |
| [`ci-021270-ac3cb671`](receipts/round-ci-021270-ac3cb671-result.json) | `ReviewConcreteThetaInvariants` | `0607632f04a5` | succeeded | 0 | 233.99 | 229.37 (7.09 + 222.28) | 8.08 |
| [`ci-021271-3fcf7b4a`](receipts/round-ci-021271-3fcf7b4a-result.json) | `Source_ReferenceIutConcreteLocalEstimate` | `af0952d46e43` | failed | 1 | 169.83 | 165.62 (8.98 + 156.64) | 7.57 |
| [`ci-021272-006a8269`](receipts/round-ci-021272-006a8269-result.json) | `Source_ReferenceIutConcreteDifferentDegree` | `840b5f35e2e4` | failed | 1 | 166.00 | 159.17 (6.32 + 152.85) | 7.51 |
| [`ci-021273-795ab8de`](receipts/round-ci-021273-795ab8de-result.json) | `Source_ReferenceIutTowerDifferentPowers` | `69b824658168` | failed | 1 | 83.99 | 81.49 (4.06 + 77.43) | 4.09 |
| [`ci-021291-69d8c813`](receipts/round-ci-021291-69d8c813-result.json) | `Source_ReferenceIutConcreteLocalEstimate` | `b0933bac6ee8` | failed | 1 | 105.51 | 101.29 (8.98 + 92.31) | 7.58 |
| [`ci-021292-fe610ea0`](receipts/round-ci-021292-fe610ea0-result.json) | `Source_ReferenceIutEmbedCompletion` | `ac63ebed39ba` | failed | 1 | 50.89 | 49.30 (4.29 + 45.01) | 4.07 |
| [`ci-021293-d1b1e969`](receipts/round-ci-021293-d1b1e969-result.json) | `Source_ReferenceIutTateRoots` | `45681d68abc2` | succeeded | 0 | 36.33 | 35.40 (2.39 + 33.01) | 3.13 |
| [`ci-021294-6d3b4575`](receipts/round-ci-021294-6d3b4575-result.json) | `Source_ReferenceIutCanLiftPresentation` | `4c1bf0543f21` | failed | 1 | 100.33 | 97.07 (8.01 + 89.06) | 7.62 |
| [`ci-021320-4bd9032e`](receipts/round-ci-021320-4bd9032e-result.json) | `Source_ReferenceIutConcreteLocalEstimate` | `dd57a9ff37b0` | failed | 1 | 184.10 | 184.85 (7.48 + 177.37) | 7.58 |
| [`ci-021324-dfcdd9b6`](receipts/round-ci-021324-dfcdd9b6-result.json) | `Source_ReferenceIutTateRoots` | `45681d68abc2` | succeeded | 0 | 67.45 | 66.92 (1.96 + 64.96) | 3.11 |
| [`ci-021338-71910910`](receipts/round-ci-021338-71910910-result.json) | `Source_ReferenceIutConcreteLocalEstimate` | `3e242c2b3d43` | succeeded | 0 | 205.33 | 204.17 (8.78 + 195.39) | 7.58 |
| [`ci-021340-fefab1d1`](receipts/round-ci-021340-fefab1d1-result.json) | `Source_ReferenceIutCanLiftPresentation` | `3efb9eefe42d` | succeeded | 0 | 187.50 | 184.32 (7.17 + 177.15) | 7.61 |
| [`ci-021341-52f08107`](receipts/round-ci-021341-52f08107-result.json) | `Source_ReferenceIutCanLiftPolynomialDegree` | `e7f1f7b78325` | succeeded | 0 | 50.29 | 48.78 (2.10 + 46.68) | 2.76 |
| [`ci-021342-672fe423`](receipts/round-ci-021342-672fe423-result.json) | `Source_ReferenceIutCanLiftCoverDescent` | `016c2a91b9d5` | succeeded | 0 | 63.66 | 61.77 (2.67 + 59.10) | 3.67 |
| [`ci-021358-42a0bc66`](receipts/round-ci-021358-42a0bc66-result.json) | `Source_ReferenceIutCanLiftCoverDescent` | `016c2a91b9d5` | succeeded | 0 | 70.78 | 66.38 (2.53 + 63.85) | 3.65 |
| [`ci-021359-75c78f0a`](receipts/round-ci-021359-75c78f0a-result.json) | `Source_ReferenceIutCanLiftPresentation` | `3efb9eefe42d` | succeeded | 0 | 176.43 | 171.43 (8.54 + 162.89) | 7.64 |
| [`ci-021360-3dc1dbcb`](receipts/round-ci-021360-3dc1dbcb-result.json) | `Source_ReferenceIutCanLiftPolynomialDegree` | `e7f1f7b78325` | succeeded | 0 | 52.34 | 48.97 (2.54 + 46.43) | 2.79 |
| [`ci-021368-04a24c77`](receipts/round-ci-021368-04a24c77-result.json) | `Source_ReferenceIutConcreteLocalEstimate` | `3e242c2b3d43` | succeeded | 0 | 170.40 | 171.38 (8.87 + 162.51) | 7.58 |
| [`ci-021375-2c3207e2`](receipts/round-ci-021375-2c3207e2-result.json) | `Source_ReferenceIutCanLiftPolynomialRamification` | `504bdb5dedc8` | failed | 1 | 83.19 | 81.34 (2.56 + 78.78) | 3.31 |
| [`ci-021376-3814489c`](receipts/round-ci-021376-3814489c-result.json) | `Source_ReferenceIutConcreteExistence` | `e1e8fba4df2d` | timeout | unknown | 180.07 | unknown | unknown |
| [`ci-021377-b789e151`](receipts/round-ci-021377-b789e151-result.json) | `Source_ReferenceIutCanLiftBranchMultiplicity` | `93792202d417` | timeout | unknown | 181.65 | unknown | unknown |
| [`ci-021378-1f310001`](receipts/round-ci-021378-1f310001-result.json) | `Source_ReferenceIutCanLiftComplex` | `9e021f91ac17` | timeout | unknown | 180.32 | unknown | unknown |
| [`ci-021379-ad1d1868`](receipts/round-ci-021379-ad1d1868-result.json) | `Source_ReferenceIutCanLiftLefschetzAssembly` | `e0ee03b0b640` | timeout | unknown | 180.13 | unknown | unknown |
| [`ci-021380-91c6737e`](receipts/round-ci-021380-91c6737e-result.json) | `ReviewCanLiftFoundations` | `2c40217dd45e` | succeeded | 0 | 282.58 | 275.39 (5.96 + 269.43) | 8.06 |
| [`ci-021381-8cd409b0`](receipts/round-ci-021381-8cd409b0-result.json) | `Source_ReferenceIutCanLiftPolynomialRigidity` | `7232f754a40d` | succeeded | 0 | 101.06 | 97.19 (3.32 + 93.87) | 3.55 |
| [`ci-021390-964c6d68`](receipts/round-ci-021390-964c6d68-result.json) | `Source_ReferenceIutConcreteExistence` | `e1e8fba4df2d` | succeeded | 0 | 219.08 | 213.43 (5.76 + 207.67) | 7.48 |
| [`ci-021401-ad9fab7a`](receipts/round-ci-021401-ad9fab7a-result.json) | `Source_ReferenceIutCanLiftComplex` | `9e021f91ac17` | succeeded | 0 | 204.47 | 192.61 (6.51 + 186.10) | 7.59 |
| [`ci-021402-d442a30b`](receipts/round-ci-021402-d442a30b-result.json) | `Source_ReferenceIutCanLiftPolynomialRamification` | `a3f848c1987b` | succeeded | 0 | 72.91 | 69.78 (2.28 + 67.50) | 3.30 |
| [`ci-021403-03f891ca`](receipts/round-ci-021403-03f891ca-result.json) | `Source_ReferenceIutCanLiftLefschetzAssembly` | `e0ee03b0b640` | failed | 1 | 204.37 | 192.48 (6.78 + 185.70) | 7.57 |
| [`ci-021404-67cf9634`](receipts/round-ci-021404-67cf9634-result.json) | `Source_ReferenceIutCurveConcreteExistence` | `6be153f264aa` | timeout | unknown | 180.07 | unknown | unknown |
| [`ci-021405-7008ce12`](receipts/round-ci-021405-7008ce12-result.json) | `ReviewConcreteLocalEstimate` | `24e64929c024` | succeeded | 0 | 256.86 | 246.40 (5.37 + 241.03) | 7.84 |
| [`ci-021406-f824be01`](receipts/round-ci-021406-f824be01-result.json) | `Source_ReferenceIutCanLiftBranchMultiplicity` | `93792202d417` | succeeded | 0 | 231.72 | 222.66 (8.29 + 214.37) | 7.60 |
| [`ci-021418-6ae2447f`](receipts/round-ci-021418-6ae2447f-result.json) | `Source_ReferenceIutCurveConcreteExistence` | `6be153f264aa` | succeeded | 0 | 282.90 | 271.27 (5.45 + 265.82) | 7.51 |
| [`ci-021419-7fd481c6`](receipts/round-ci-021419-7fd481c6-result.json) | `Source_ReferenceIutCanLiftNormalizationEmbed` | `c37f139651a5` | failed | 1 | 81.66 | 80.25 (19.75 + 60.50) | 3.33 |
| [`ci-021420-ca43813b`](receipts/round-ci-021420-ca43813b-result.json) | `Source_ReferenceIutCanLiftLefschetzAssembly` | `d487fc0f95ff` | succeeded | 0 | 227.94 | 216.86 (7.01 + 209.85) | 7.58 |
| [`ci-021421-a1aa5fbb`](receipts/round-ci-021421-a1aa5fbb-result.json) | `Source_ReferenceIutCanLiftTameInertia` | `51eef15b469b` | succeeded | 0 | 67.18 | 63.20 (5.92 + 57.28) | 3.13 |
| [`ci-021422-7a36ef10`](receipts/round-ci-021422-7a36ef10-result.json) | `Source_ReferenceIutCanLiftGaloisCore` | `52b956bbc7b1` | succeeded | 0 | 70.26 | 67.70 (8.89 + 58.81) | 3.11 |
| [`ci-021423-e2df4f90`](receipts/round-ci-021423-e2df4f90-result.json) | `Source_ReferenceIutCanLiftXDescent` | `16180cb7d627` | timeout | unknown | 180.06 | unknown | unknown |
| [`ci-021424-d3603d7b`](receipts/round-ci-021424-d3603d7b-result.json) | `Source_ReferenceIutCanLiftHemiRigid` | `dad8ed900233` | timeout | unknown | 180.06 | unknown | unknown |
| [`ci-021429-1c8c9c84`](receipts/round-ci-021429-1c8c9c84-result.json) | `Source_ReferenceIutCanLiftNoether` | `94e955b5f3f3` | succeeded | 0 | 105.91 | 100.48 (2.34 + 98.14) | 2.72 |
| [`ci-021440-f6c510e9`](receipts/round-ci-021440-f6c510e9-result.json) | `ReviewConcreteExistence` | `192f6c11b7c9` | succeeded | 0 | 320.18 | 316.10 (5.75 + 310.35) | 8.06 |
| [`ci-021441-1c695540`](receipts/round-ci-021441-1c695540-result.json) | `Source_ReferenceIutCanLiftXDescent` | `16180cb7d627` | succeeded | 0 | 239.94 | 234.86 (4.76 + 230.10) | 7.53 |
| [`ci-021442-24146b1d`](receipts/round-ci-021442-24146b1d-result.json) | `Source_ReferenceIutCanLiftGaloisRamification` | `28e61ba8e1e4` | failed | 1 | 108.79 | 116.13 (17.20 + 98.93) | 3.46 |
| [`ci-021446-ef4a6c70`](receipts/round-ci-021446-ef4a6c70-result.json) | `Source_ReferenceIutCanLiftHemiRigid` | `dad8ed900233` | failed | 1 | 226.76 | 226.36 (10.21 + 216.15) | 7.61 |
| [`ci-021470-4add9083`](receipts/round-ci-021470-4add9083-result.json) | `Thm_AbcAdaptation_Reference_Heights_exists_torsion_x_bound` | `3a54dadd14cd` | succeeded | 0 | 58.54 | 54.71 (2.71 + 52.00) | 3.04 |
| [`ci-021471-1b0fea16`](receipts/round-ci-021471-1b0fea16-result.json) | `Source_ReferenceIutConcreteLocalOrder` | `9e9f0d0aa5f2` | succeeded | 0 | 80.83 | 77.71 (3.00 + 74.71) | 4.07 |
| [`ci-021472-131246a6`](receipts/round-ci-021472-131246a6-result.json) | `Source_TripodCyclicArch` | `bccaf62c0086` | succeeded | 0 | 59.17 | 57.05 (4.84 + 52.21) | 3.07 |
| [`ci-021473-386725b5`](receipts/round-ci-021473-386725b5-result.json) | `Source_ReferenceIutCanLiftNormalizationEmbed` | `7504d5989799` | succeeded | 0 | 67.09 | 70.07 (20.62 + 49.45) | 3.35 |
| [`ci-021483-ab25526b`](receipts/round-ci-021483-ab25526b-result.json) | `ReviewCyclicArch` | `07637703b7e2` | succeeded | 0 | 151.29 | 148.08 (4.93 + 143.15) | 7.90 |
| [`ci-021484-e188518e`](receipts/round-ci-021484-e188518e-result.json) | `Source_ReferenceIutCanLiftGaloisRamification` | `ce63939611fc` | succeeded | 0 | 57.09 | 66.10 (18.73 + 47.37) | 3.48 |
| [`ci-021485-b464462e`](receipts/round-ci-021485-b464462e-result.json) | `Source_ReferenceIutTowerDifferentPowers` | `690d96f91db3` | succeeded | 0 | 68.39 | 66.74 (3.28 + 63.46) | 4.09 |
| [`ci-021486-3e9f7135`](receipts/round-ci-021486-3e9f7135-result.json) | `Source_ReferenceIutCanLiftRealization` | `0501e2bc2c34` | succeeded | 0 | 72.49 | 74.96 (13.40 + 61.56) | 4.12 |
| [`ci-021487-f075d9b3`](receipts/round-ci-021487-f075d9b3-result.json) | `Source_ReferenceIutConcreteLocalPacket` | `b7a3430d6333` | succeeded | 0 | 68.63 | 68.74 (5.73 + 63.01) | 4.11 |
| [`ci-021494-894e3321`](receipts/round-ci-021494-894e3321-result.json) | `Source_ReferenceIutCanLiftHemiRigid` | `77522870495a` | failed | 1 | 133.93 | 133.88 (11.60 + 122.28) | 7.61 |
| [`ci-021503-acdfe227`](receipts/round-ci-021503-acdfe227-result.json) | `Source_ReferenceIutConcreteLocalPacketEquiv` | `b135c83cf413` | failed | 1 | 66.74 | 64.90 (4.92 + 59.98) | 4.13 |
| [`ci-021504-b3d1e00d`](receipts/round-ci-021504-b3d1e00d-result.json) | `Source_ReferenceIutCanLiftGaloisAction` | `10262479b434` | failed | 1 | 57.34 | 60.17 (13.75 + 46.42) | 3.39 |
| [`ci-021505-6d16e48c`](receipts/round-ci-021505-6d16e48c-result.json) | `Source_ReferenceIutConcreteDifferentDegree` | `e6afd8cefb71` | succeeded | 0 | 133.28 | 130.46 (6.75 + 123.71) | 7.54 |
| [`ci-021506-2cdf81e9`](receipts/round-ci-021506-2cdf81e9-result.json) | `ReviewCyclicArchReduction` | `9839175d42ab` | succeeded | 0 | 64.23 | 62.86 (2.79 + 60.07) | 3.72 |
| [`ci-021507-b683305a`](receipts/round-ci-021507-b683305a-result.json) | `Source_ReferenceHeightsTorsionLattice` | `3cf6faf0c7c0` | succeeded | 0 | 59.98 | 60.97 (5.71 + 55.26) | 3.60 |
| [`ci-021508-c4065ea3`](receipts/round-ci-021508-c4065ea3-result.json) | `Source_ReferenceIutCanLiftEtalePoints` | `f76bbcb83f31` | succeeded | 0 | 64.95 | 63.87 (3.64 + 60.23) | 3.91 |
| [`ci-021514-f0ffb817`](receipts/round-ci-021514-f0ffb817-result.json) | `Source_ReferenceHeightsWeierstrassDifferential` | `098bcd6fceaa` | succeeded | 0 | 39.26 | 35.07 (2.01 + 33.06) | 3.43 |
| [`ci-021515-270ccede`](receipts/round-ci-021515-270ccede-result.json) | `Source_ReferenceIutConcreteLocalPacketEquiv` | `6497a886cca5` | succeeded | 0 | 46.50 | 43.98 (5.56 + 38.42) | 4.14 |
| [`ci-021516-0bc97e99`](receipts/round-ci-021516-0bc97e99-result.json) | `Source_ReferenceIutCanLiftHemiRigid` | `6676efd3ca64` | failed | 1 | 97.73 | 94.67 (11.60 + 83.07) | 7.61 |
| [`ci-021517-da5af225`](receipts/round-ci-021517-da5af225-result.json) | `Source_ReferenceIutTowerStepIII` | `4a0f1cb56749` | failed | 1 | 48.52 | 47.97 (9.51 + 38.46) | 4.17 |
| [`ci-021518-b9461f20`](receipts/round-ci-021518-b9461f20-result.json) | `Source_ReferenceIutCanLiftEtaleLocal` | `3a799d448182` | succeeded | 0 | 45.45 | 42.81 (5.06 + 37.75) | 3.93 |
| [`ci-021519-232386b3`](receipts/round-ci-021519-232386b3-result.json) | `Source_ReferenceIutCanLiftGaloisAction` | `514e5d65120a` | succeeded | 0 | 41.27 | 42.70 (11.60 + 31.10) | 3.38 |
| [`ci-021531-66b7da6a`](receipts/round-ci-021531-66b7da6a-result.json) | `Source_ReferenceHeightsWeierstrassFibers` | `c4dd68d68014` | succeeded | 0 | 55.03 | 51.04 (2.75 + 48.29) | 3.45 |
| [`ci-021532-c1962d99`](receipts/round-ci-021532-c1962d99-result.json) | `Source_ReferenceIutCanLiftHemiRigid` | `0614230309f1` | succeeded | 0 | 121.98 | 116.02 (11.21 + 104.81) | 7.62 |
| [`ci-021534-9f07f95d`](receipts/round-ci-021534-9f07f95d-result.json) | `ReviewConcreteLocalPacket` | `36d4afd6dfc8` | succeeded | 0 | 129.62 | 122.68 (5.42 + 117.26) | 7.78 |
| [`ci-021535-d9ca78fc`](receipts/round-ci-021535-d9ca78fc-result.json) | `Source_ReferenceIutTowerStepIII` | `b87a080dcecd` | succeeded | 0 | 62.77 | 61.87 (8.73 + 53.14) | 4.17 |
| [`ci-021536-76511b9c`](receipts/round-ci-021536-76511b9c-result.json) | `Source_ReferenceIutCanLiftAnalyticBounds` | `207541998134` | succeeded | 0 | 48.23 | 45.59 (2.42 + 43.17) | 3.11 |
| [`ci-021537-3b4ec618`](receipts/round-ci-021537-3b4ec618-result.json) | `Source_ReferenceIutCanLiftRamificationTransport` | `0c20f3f33de0` | succeeded | 0 | 51.81 | 50.49 (2.60 + 47.89) | 3.37 |
| [`ci-021546-97516644`](receipts/round-ci-021546-97516644-result.json) | `Source_ReferenceIutCanLiftCoveringSections` | `2506e1735a50` | failed | 1 | 31.95 | 29.32 (1.31 + 28.01) | 2.03 |
| [`ci-021547-e13b757c`](receipts/round-ci-021547-e13b757c-result.json) | `Source_ReferenceIutCanLiftAnalyticRoots` | `8bc84272633a` | succeeded | 0 | 54.37 | 51.93 (4.03 + 47.90) | 3.56 |
| [`ci-021548-ca8905c3`](receipts/round-ci-021548-ca8905c3-result.json) | `Source_ReferenceIutCanLiftAnalyticInput` | `6901500f76af` | failed | 1 | 141.56 | 124.06 (6.06 + 118.00) | 7.56 |
| [`ci-021549-ea717c9f`](receipts/round-ci-021549-ea717c9f-result.json) | `Source_ReferenceIutCanLiftUnramifiedClosure` | `1fa041cd051a` | failed | 1 | 155.77 | 141.26 (23.00 + 118.26) | 7.66 |
| [`ci-021550-a26d38d4`](receipts/round-ci-021550-a26d38d4-result.json) | `Source_ReferenceIutCanLiftEtaleCoordinates` | `42654600968c` | failed | 1 | 53.43 | 52.27 (4.92 + 47.35) | 3.61 |
| [`ci-021551-dc1d2a81`](receipts/round-ci-021551-dc1d2a81-result.json) | `Source_ReferenceIutTowerSerreCore` | `6ddb657f8a3c` | failed | 1 | 66.42 | 67.85 (10.60 + 57.25) | 3.31 |
| [`ci-021566-133d1dd4`](receipts/round-ci-021566-133d1dd4-result.json) | `Source_ReferenceHeightsLatticePointMap` | `aa16d0727826` | failed | 1 | 59.06 | 54.40 (3.01 + 51.39) | 3.98 |
| [`ci-021567-5384a6cb`](receipts/round-ci-021567-5384a6cb-result.json) | `Source_ReferenceHeightsModularCusp` | `4f169f1ba8bc` | failed | 1 | 58.69 | 53.74 (3.90 + 49.84) | 3.99 |
| [`ci-021568-d07cfdd4`](receipts/round-ci-021568-d07cfdd4-result.json) | `Source_ReferenceIutCanLiftCoveringSections` | `04093bcff6af` | failed | 1 | 40.10 | 37.52 (1.65 + 35.87) | 2.06 |
| [`ci-021569-f47bd4e2`](receipts/round-ci-021569-f47bd4e2-result.json) | `ReviewTowerStepIII` | `1ae28cf94e6e` | succeeded | 0 | 133.96 | 129.79 (5.87 + 123.92) | 8.09 |
| [`ci-021570-d46e7a2a`](receipts/round-ci-021570-d46e7a2a-result.json) | `Source_ReferenceHeightsTorsionCurve` | `88aca311d90f` | succeeded | 0 | 49.04 | 46.08 (3.65 + 42.43) | 3.59 |
| [`ci-021571-05ada488`](receipts/round-ci-021571-05ada488-result.json) | `Source_ReferenceIutTowerSerreCore` | `858fff11e38d` | failed | 1 | 51.60 | 54.53 (9.82 + 44.71) | 3.33 |
| [`ci-021580-7461197f`](receipts/round-ci-021580-7461197f-result.json) | `Source_ReferenceIutCanLiftAnalyticInput` | `3f3f89a2c731` | succeeded | 0 | 105.71 | 101.51 (5.28 + 96.23) | 7.58 |
| [`ci-021581-51b92031`](receipts/round-ci-021581-51b92031-result.json) | `Source_ReferenceIutCanLiftEtaleCoordinates` | `efb8fa276f5f` | succeeded | 0 | 49.71 | 49.57 (4.68 + 44.89) | 3.63 |
| [`ci-021582-1febe339`](receipts/round-ci-021582-1febe339-result.json) | `Source_ReferenceIutCanLiftUnramifiedClosure` | `0dc39df2dcda` | failed | 1 | 119.53 | 119.44 (22.15 + 97.29) | 7.67 |
| [`ci-021588-5456b49c`](receipts/round-ci-021588-5456b49c-result.json) | `Source_ReferenceIutCanLiftCoveringSections` | `5e0b53e3ef5d` | succeeded | 0 | 28.76 | 28.15 (1.73 + 26.42) | 2.10 |
| [`ci-021598-ac6b1618`](receipts/round-ci-021598-ac6b1618-result.json) | `Source_ReferenceIutTowerSerreCore` | `7cc5ef8c2b56` | failed | 1 | 66.55 | 65.85 (9.39 + 56.46) | 3.31 |
| [`ci-021599-ccbfee3d`](receipts/round-ci-021599-ccbfee3d-result.json) | `Source_ReferenceIutConcreteLocalIntegral` | `1c7ca185cab0` | failed | 1 | 78.79 | 76.33 (6.23 + 70.10) | 4.16 |
| [`ci-021600-b7e05641`](receipts/round-ci-021600-b7e05641-result.json) | `Source_ReferenceIutCanLiftUnramifiedClosure` | `1c47f33ad475` | failed | 1 | 160.22 | 157.63 (24.12 + 133.51) | 7.66 |
| [`ci-021602-3e104202`](receipts/round-ci-021602-3e104202-result.json) | `Source_ReferenceIutTowerStepIIIForTheta` | `af6806bda844` | succeeded | 0 | 142.65 | 136.04 (6.01 + 130.03) | 7.52 |
| [`ci-021603-c34a5f2a`](receipts/round-ci-021603-c34a5f2a-result.json) | `Source_ReferenceHeightsLatticeModular` | `0d884d263c3e` | succeeded | 0 | 75.90 | 71.10 (3.35 + 67.75) | 3.99 |
| [`ci-021604-03622920`](receipts/round-ci-021604-03622920-result.json) | `Source_ReferenceHeightsModularCusp` | `48c006c3feaf` | succeeded | 0 | 72.58 | 67.45 (3.14 + 64.31) | 3.99 |
| [`ci-021615-42598a95`](receipts/round-ci-021615-42598a95-result.json) | `Source_ReferenceIutTowerSerreCore` | `7f6de7687553` | succeeded | 0 | 54.80 | 56.06 (10.64 + 45.42) | 3.31 |
| [`ci-021616-6e2ea5a0`](receipts/round-ci-021616-6e2ea5a0-result.json) | `ReviewTowerStepIIIForTheta` | `ca117a983036` | succeeded | 0 | 159.71 | 147.91 (6.32 + 141.59) | 7.89 |
| [`ci-021617-fb4d9a8a`](receipts/round-ci-021617-fb4d9a8a-result.json) | `ReviewHeightsModularCusp` | `7ae224f1b035` | succeeded | 0 | 156.52 | 146.05 (5.98 + 140.07) | 8.07 |
| [`ci-021618-bdf4e6c7`](receipts/round-ci-021618-bdf4e6c7-result.json) | `Source_ReferenceHeightsLatticePointMap` | `2fc6c3c5d401` | succeeded | 0 | 66.08 | 61.78 (3.57 + 58.21) | 3.98 |
| [`ci-021619-ba5cf530`](receipts/round-ci-021619-ba5cf530-result.json) | `Source_ReferenceIutCanLiftAnalyticLocal` | `d521db6608a7` | succeeded | 0 | 65.30 | 61.04 (4.14 + 56.90) | 3.92 |
| [`ci-021620-8c518d6c`](receipts/round-ci-021620-8c518d6c-result.json) | `Source_ReferenceIutCanLiftUnramifiedClosure` | `947d489bc337` | succeeded | 0 | 171.57 | 168.08 (24.15 + 143.93) | 7.69 |
| [`ci-021621-c7fa6c71`](receipts/round-ci-021621-c7fa6c71-result.json) | `Source_ReferenceIutCanLiftWeierstrassGerms` | `8b8175b313ef` | failed | 1 | 72.10 | 69.08 (8.46 + 60.62) | 3.24 |
| [`ci-021629-af1fc0b9`](receipts/round-ci-021629-af1fc0b9-result.json) | `Source_ReferenceIutTowerSerreBound` | `64651abcaf96` | succeeded | 0 | 81.05 | 77.61 (10.35 + 67.26) | 4.14 |
| [`ci-021630-d335e5cc`](receipts/round-ci-021630-d335e5cc-result.json) | `Source_ReferenceIutConcreteLocalIntegral` | `8aa40069e424` | failed | 1 | 92.07 | 87.93 (6.15 + 81.78) | 4.15 |
| [`ci-021632-cb4dd3c0`](receipts/round-ci-021632-cb4dd3c0-result.json) | `Source_ReferenceIutCanLiftAnalyticChart` | `804dce25c61d` | succeeded | 0 | 72.46 | 67.83 (4.01 + 63.82) | 3.93 |
| [`ci-021634-3b277bcf`](receipts/round-ci-021634-3b277bcf-result.json) | `Source_ReferenceIutThetaLocalBadChars` | `d9d9680b68b3` | timeout | unknown | 180.04 | unknown | unknown |
| [`ci-021635-02f7a659`](receipts/round-ci-021635-02f7a659-result.json) | `Source_TripodTpdGalois` | `298d336e2b49` | succeeded | 0 | 116.40 | 117.81 (13.56 + 104.25) | 4.26 |
| [`ci-021636-bc9102a0`](receipts/round-ci-021636-bc9102a0-result.json) | `Source_ReferenceIutEmbedCompletion` | `9ceb1db9a12b` | succeeded | 0 | 104.09 | 99.86 (4.96 + 94.90) | 4.10 |
| [`ci-021637-da4eea75`](receipts/round-ci-021637-da4eea75-result.json) | `Source_ReferenceHeightsLatticePointMapInjectivity` | `260a078183fc` | succeeded | 0 | 97.85 | 93.78 (3.43 + 90.35) | 3.98 |
| [`ci-021639-f2a3f73a`](receipts/round-ci-021639-f2a3f73a-result.json) | `Source_ReferenceHeightsModularComparisons` | `8298de28d83e` | failed | 1 | 109.70 | 105.41 (3.09 + 102.32) | 3.97 |
| [`ci-021631-5a00aac0`](receipts/round-ci-021631-5a00aac0-result.json) | `ReviewCanLiftClosure` | `939ca8563bc5` | succeeded | 0 | 211.22 | 199.48 (6.31 + 193.17) | 7.94 |
| [`ci-021638-e2d71441`](receipts/round-ci-021638-e2d71441-result.json) | `Source_ReferenceHeightsModularRange` | `aab396ad31f1` | succeeded | 0 | 125.71 | 120.96 (2.59 + 118.37) | 3.90 |
| [`ci-021649-3ffa7c78`](receipts/round-ci-021649-3ffa7c78-result.json) | `Source_ReferenceIutThetaLocalBadChars` | `d9d9680b68b3` | succeeded | 0 | 214.47 | 203.49 (7.21 + 196.28) | 7.53 |
| [`ci-021650-9fef3fb8`](receipts/round-ci-021650-9fef3fb8-result.json) | `Source_ReferenceIutTowerInertia` | `2cd6b3ff7209` | succeeded | 0 | 87.77 | 79.19 (4.40 + 74.79) | 4.06 |
| [`ci-021651-5fdc99f2`](receipts/round-ci-021651-5fdc99f2-result.json) | `ReviewTripodTpdGalois` | `ab30e4dfe776` | succeeded | 0 | 270.43 | 260.22 (6.37 + 253.85) | 8.02 |
| [`ci-021647-79c40b1e`](receipts/round-ci-021647-79c40b1e-result.json) | `Source_ReferenceIutTowerDifferentBound` | `a447f9d5f677` | failed | 1 | 105.76 | 97.02 (3.79 + 93.23) | 4.09 |
| [`ci-021648-f52797c5`](receipts/round-ci-021648-f52797c5-result.json) | `Source_ReferenceIutConcreteLocalIntegral` | `50aadf09e9ce` | succeeded | 0 | 99.72 | 91.65 (7.14 + 84.51) | 4.16 |
| [`ci-021652-c41c2a60`](receipts/round-ci-021652-c41c2a60-result.json) | `ReviewHeightsLatticePointAndRange` | `ba34886112e7` | succeeded | 0 | 252.35 | 242.81 (6.50 + 236.31) | 7.86 |
| [`ci-021653-17da42ae`](receipts/round-ci-021653-17da42ae-result.json) | `Source_ReferenceIutCanLiftAnalyticCovering` | `0fe7b2f8818b` | succeeded | 0 | 112.33 | 110.60 (4.64 + 105.96) | 3.95 |
| [`ci-021654-d6dcd274`](receipts/round-ci-021654-d6dcd274-result.json) | `Source_ReferenceIutCanLiftWeierstrassGerms` | `e6384bfcf26b` | succeeded | 0 | 91.73 | 89.99 (4.78 + 85.21) | 3.27 |
| [`ci-021655-fb4d46d2`](receipts/round-ci-021655-fb4d46d2-result.json) | `Source_ReferenceHeightsModularComparisons` | `4602dd4a4826` | succeeded | 0 | 99.54 | 96.75 (3.35 + 93.40) | 3.97 |
| [`ci-021660-c768ca58`](receipts/round-ci-021660-c768ca58-result.json) | `Source_ReferenceIutTowerDifferentBound` | `99dbbb87d580` | succeeded | 0 | 111.42 | 102.96 (5.68 + 97.28) | 4.11 |
| [`ci-021661-9daca3c9`](receipts/round-ci-021661-9daca3c9-result.json) | `Source_ReferenceIutConcreteLocalHaar` | `fab62abd78fd` | succeeded | 0 | 109.01 | 100.22 (5.76 + 94.46) | 4.15 |
| [`ci-021662-fb650ace`](receipts/round-ci-021662-fb650ace-result.json) | `Source_ReferenceIutTateCompat` | `6ccb2d81845b` | failed | 1 | 111.67 | 102.23 (6.75 + 95.48) | 4.11 |
| [`ci-021666-feeb4503`](receipts/round-ci-021666-feeb4503-result.json) | `Source_ReferenceHeightsWeierstrassSurjectivity` | `6f918663ad76` | succeeded | 0 | 94.75 | 86.15 (4.03 + 82.12) | 3.99 |
| [`ci-021663-26f00e0b`](receipts/round-ci-021663-26f00e0b-result.json) | `Source_ReferenceIutTowerReductionKernel` | `08697b538591` | succeeded | 0 | 71.56 | 64.28 (3.21 + 61.07) | 2.86 |
| [`ci-021664-ebc771f0`](receipts/round-ci-021664-ebc771f0-result.json) | `Source_ReferenceIutCanLiftCayley` | `56b9f67af9d2` | succeeded | 0 | 79.57 | 72.05 (2.34 + 69.71) | 3.13 |
| [`ci-021665-a706a93e`](receipts/round-ci-021665-a706a93e-result.json) | `Source_ReferenceIutCanLiftEntirePolynomial` | `77a3358f884e` | succeeded | 0 | 81.87 | 76.03 (3.10 + 72.93) | 3.41 |
| [`ci-021667-f7dd1302`](receipts/round-ci-021667-f7dd1302-result.json) | `ReviewStepIIIBadChars` | `8b79c37c2dc9` | succeeded | 0 | 180.53 | 171.04 (5.50 + 165.54) | 7.85 |
| [`ci-021668-80e34e19`](receipts/round-ci-021668-80e34e19-result.json) | `ReviewHeightsModularComparisons` | `623478053b4b` | succeeded | 0 | 172.64 | 168.21 (5.82 + 162.39) | 7.96 |
| [`ci-021675-79e26edc`](receipts/round-ci-021675-79e26edc-result.json) | `Source_ReferenceIutTowerDifferent` | `749c44bcc6a4` | failed | 1 | 160.14 | 141.20 (6.25 + 134.95) | 4.14 |
| [`ci-021676-658769a3`](receipts/round-ci-021676-658769a3-result.json) | `ReviewTowerSerreBound` | `76c9a2554ce1` | interrupted | unknown | unknown | unknown | unknown |
| [`ci-021678-d775db09`](receipts/round-ci-021678-d775db09-result.json) | `Source_ReferenceIutConcreteLocalFiniteHull` | `87c77077a509` | failed | 1 | 168.30 | 172.36 (47.40 + 124.96) | 4.50 |
| [`ci-021679-f78fe30d`](receipts/round-ci-021679-f78fe30d-result.json) | `Source_ReferenceIutConcreteLocalArchimedean` | `a814f3df4b2c` | failed | 1 | 141.64 | 126.21 (8.98 + 117.23) | 4.16 |
| [`ci-021682-936ae3f9`](receipts/round-ci-021682-936ae3f9-result.json) | `Source_ReferenceIutTowerTorsionRigid` | `d7b5f665fba6` | succeeded | 0 | 130.83 | 113.32 (3.54 + 109.78) | 4.11 |
| [`ci-021683-9a513cee`](receipts/round-ci-021683-9a513cee-result.json) | `Source_ReferenceIutCanLiftHalfPlaneAut` | `05d6907995e5` | succeeded | 0 | 126.75 | 119.10 (4.65 + 114.45) | 3.54 |
| [`ci-021684-130f31cf`](receipts/round-ci-021684-130f31cf-result.json) | `Source_ReferenceIutThetaLocalOrder` | `98d3b5006f44` | failed | 1 | 153.65 | 145.80 (3.23 + 142.57) | 4.10 |
| [`ci-021685-f2ec1920`](receipts/round-ci-021685-f2ec1920-result.json) | `Source_TripodTwoTorsion` | `7d17d3c60d4a` | failed | 1 | 126.02 | 121.19 (2.54 + 118.65) | 3.94 |
| [`ci-021686-d9ddab91`](receipts/round-ci-021686-d9ddab91-result.json) | `Source_ReferenceIutPointThetaData` | `7a24f1202653` | interrupted | unknown | unknown | unknown | unknown |
| [`ci-021692-f4cf2515`](receipts/round-ci-021692-f4cf2515-result.json) | `Source_ReferenceIutTowerDifferent` | `7bef44fcc7bd` | succeeded | 0 | 53.88 | 45.95 (6.50 + 39.45) | 4.15 |
| [`ci-021693-678cb693`](receipts/round-ci-021693-678cb693-result.json) | `ReviewTowerSerreBound` | `76c9a2554ce1` | succeeded | 0 | 113.85 | 100.27 (5.79 + 94.48) | 8.05 |
| [`ci-021694-2a5e58ce`](receipts/round-ci-021694-2a5e58ce-result.json) | `Source_ReferenceIutTateCompat` | `4c519b31ad39` | succeeded | 0 | 50.80 | 46.71 (7.75 + 38.96) | 4.13 |
| [`ci-021695-c283686a`](receipts/round-ci-021695-c283686a-result.json) | `Source_ReferenceIutThetaLocalOrder` | `cc50bae0fa3d` | succeeded | 0 | 48.14 | 42.73 (3.92 + 38.81) | 4.10 |
| [`ci-021696-ee99a7c6`](receipts/round-ci-021696-ee99a7c6-result.json) | `Source_TripodTwoTorsion` | `17f90044c723` | succeeded | 0 | 46.43 | 40.54 (3.17 + 37.37) | 4.05 |
| [`ci-021697-6b3de098`](receipts/round-ci-021697-6b3de098-result.json) | `Source_ReferenceIutCanLiftUniformizationCover` | `f27b0960996a` | succeeded | 0 | 43.23 | 38.35 (4.65 + 33.70) | 3.69 |
| [`ci-021698-b8725f13`](receipts/round-ci-021698-b8725f13-result.json) | `Source_ReferenceIutPointThetaData` | `7a24f1202653` | succeeded | 0 | 95.64 | 82.60 (5.59 + 77.01) | 7.50 |
| [`ci-021732-661a23a8`](receipts/round-ci-021732-661a23a8-result.json) | `Source_ReferenceIutConcreteLocalArchimedean` | `2958f19b1b3a` | succeeded | 0 | 52.42 | 50.82 (9.23 + 41.59) | 4.15 |
| [`ci-021729-842755bc`](receipts/round-ci-021729-842755bc-result.json) | `Source_ReferenceIutTowerArithmetic` | `c11fb3127fcf` | succeeded | 0 | 116.92 | 103.11 (7.18 + 95.93) | 7.52 |
| [`ci-021730-14751bfe`](receipts/round-ci-021730-14751bfe-result.json) | `ReviewTowerDifferent` | `fb5106cf7f52` | succeeded | 0 | 133.80 | 119.27 (6.40 + 112.87) | 7.86 |
| [`ci-021731-f83bdb03`](receipts/round-ci-021731-f83bdb03-result.json) | `Source_ReferenceIutConcreteLocalFiniteHull` | `5a2398a4170d` | failed | 1 | 76.22 | 71.82 (29.12 + 42.70) | 4.32 |
| [`ci-021733-e3b51b8b`](receipts/round-ci-021733-e3b51b8b-result.json) | `Source_ReferenceIutThetaLocalRoots` | `23750aae79a3` | failed | 1 | 112.98 | 102.86 (10.26 + 92.60) | 7.55 |
| [`ci-021734-e798309d`](receipts/round-ci-021734-e798309d-result.json) | `Source_ReferenceIutCurveConcreteExistence` | `4efe580fb10d` | succeeded | 0 | 110.25 | 98.32 (6.25 + 92.07) | 7.51 |
| [`ci-021735-b018ec34`](receipts/round-ci-021735-b018ec34-result.json) | `Source_ReferenceIutCanLiftPolynomialDescent` | `5d9b88ae2b49` | failed | 1 | 71.68 | 63.32 (3.56 + 59.76) | 3.96 |
| [`ci-021736-36a3bde8`](receipts/round-ci-021736-36a3bde8-result.json) | `Source_ReferenceHeightsWeierstrassPrincipalPart` | `59167a5cada3` | succeeded | 0 | 54.03 | 50.82 (7.04 + 43.78) | 3.51 |
| [`ci-021737-b021feb5`](receipts/round-ci-021737-b021feb5-result.json) | `Source_ReferenceHeightsWeierstrassPFiber` | `23a03643a7d0` | succeeded | 0 | 46.11 | 40.25 (2.71 + 37.54) | 3.41 |
| [`ci-021742-eb56803e`](receipts/round-ci-021742-eb56803e-result.json) | `ReviewTowerArithmetic` | `e730aaee528e` | succeeded | 0 | 87.81 | 79.84 (6.06 + 73.78) | 8.11 |
| [`ci-021744-b251f5a2`](receipts/round-ci-021744-b251f5a2-result.json) | `ReviewLocalArchimedean` | `553d77da542f` | succeeded | 0 | 81.51 | 74.87 (5.45 + 69.42) | 7.87 |
| [`ci-021745-58805c7d`](receipts/round-ci-021745-58805c7d-result.json) | `Source_ReferenceIutConcreteLocalFiniteHull` | `8ebc3751211c` | succeeded | 0 | 39.98 | 39.50 (8.00 + 31.50) | 4.17 |
| [`ci-021747-762a95ab`](receipts/round-ci-021747-762a95ab-result.json) | `Source_ReferenceIutCanLiftAnalyticLiftFacts` | `38a98bb5230b` | failed | 1 | 46.28 | 46.15 (5.62 + 40.53) | 3.97 |
| [`ci-021743-f33906a6`](receipts/round-ci-021743-f33906a6-result.json) | `ReviewPointwiseP7` | `32e0595fc489` | succeeded | 0 | 84.64 | 77.25 (5.57 + 71.68) | 8.09 |
| [`ci-021746-70530b67`](receipts/round-ci-021746-70530b67-result.json) | `Source_TripodUnramifiedBase` | `cc6c943064fe` | failed | 1 | 36.84 | 39.23 (8.75 + 30.48) | 4.23 |
| [`ci-021748-17c31447`](receipts/round-ci-021748-17c31447-result.json) | `Source_ReferenceHeightsWeierstrassAdditionDifferential` | `9b18451c213c` | succeeded | 0 | 36.78 | 36.93 (4.48 + 32.45) | 3.49 |
| [`ci-021756-7f9a2015`](receipts/round-ci-021756-7f9a2015-result.json) | `ReviewFiniteLocalVolumeAndHull` | `3302ea885dea` | succeeded | 0 | 124.05 | 119.04 (5.89 + 113.15) | 7.99 |
| [`ci-021757-a124d957`](receipts/round-ci-021757-a124d957-result.json) | `Source_ReferenceIutConcreteLocalFiniteIndeterminacy` | `fe102f2e3ef2` | succeeded | 0 | 58.92 | 56.97 (6.04 + 50.93) | 4.17 |
| [`ci-021758-41ef5e9c`](receipts/round-ci-021758-41ef5e9c-result.json) | `Source_ReferenceIutThetaLocalRoots` | `31ffc07de62e` | failed | 1 | 104.62 | 101.68 (9.26 + 92.42) | 7.56 |
| [`ci-021759-7f231e36`](receipts/round-ci-021759-7f231e36-result.json) | `Source_ReferenceIutCanLiftPolynomialDescent` | `bbca31644de2` | failed | 1 | 48.29 | 45.84 (2.42 + 43.42) | 3.89 |
| [`ci-021760-ad28dde9`](receipts/round-ci-021760-ad28dde9-result.json) | `Source_ReferenceHeightsWeierstrassAdditionLocal` | `21637253b37a` | succeeded | 0 | 40.21 | 37.86 (2.90 + 34.96) | 3.46 |
| [`ci-021781-bac5be78`](receipts/round-ci-021781-bac5be78-result.json) | `Source_ReferenceIutConcreteLocalFiniteLogShell` | `7a0235d9ba01` | succeeded | 0 | 66.50 | 60.99 (7.17 + 53.82) | 4.44 |
| [`ci-021782-4f3d1c74`](receipts/round-ci-021782-4f3d1c74-result.json) | `Source_ReferenceIutConcreteLocalProp14` | `c0b3cc7fabf7` | succeeded | 0 | 55.34 | 50.90 (5.26 + 45.64) | 4.16 |
| [`ci-021783-62c8c49f`](receipts/round-ci-021783-62c8c49f-result.json) | `Source_ReferenceIutCanLiftPolynomialDescent` | `e883bd82d43d` | succeeded | 0 | 49.98 | 46.50 (4.21 + 42.29) | 4.00 |
| [`ci-021784-6019ad2b`](receipts/round-ci-021784-6019ad2b-result.json) | `Source_ReferenceIutCanLiftAnalyticLiftFacts` | `368790818340` | succeeded | 0 | 47.59 | 42.59 (3.95 + 38.64) | 3.94 |
| [`ci-021785-eeb5e5a8`](receipts/round-ci-021785-eeb5e5a8-result.json) | `Source_TripodUnramifiedBase` | `760e2903c59a` | succeeded | 0 | 52.81 | 52.41 (9.73 + 42.68) | 4.24 |
| [`ci-021786-3b8ea5bc`](receipts/round-ci-021786-3b8ea5bc-result.json) | `Source_ReferenceHeightsWeierstrassAddition` | `5451571e63b6` | succeeded | 0 | 38.63 | 36.58 (3.46 + 33.12) | 3.48 |
| [`ci-021801-bea652a9`](receipts/round-ci-021801-bea652a9-result.json) | `ReviewFiniteLocalLogShell` | `e562db258e01` | succeeded | 0 | 141.52 | 134.73 (6.84 + 127.89) | 8.07 |
| [`ci-021802-fadb9b6b`](receipts/round-ci-021802-fadb9b6b-result.json) | `Source_ReferenceIutThetaLocalRoots` | `15dd9ac1992c` | succeeded | 0 | 128.69 | 122.65 (10.53 + 112.12) | 7.56 |
| [`ci-021803-be3cea0c`](receipts/round-ci-021803-be3cea0c-result.json) | `Source_ReferenceIutCanLiftInvariantCoordinates` | `d1df5348539d` | failed | 1 | 60.29 | 56.46 (4.89 + 51.57) | 4.00 |
| [`ci-021804-cc7f139b`](receipts/round-ci-021804-cc7f139b-result.json) | `Source_ReferenceIutCanLiftAnalyticTransitivity` | `b33316daea2e` | succeeded | 0 | 58.51 | 53.32 (5.06 + 48.26) | 3.95 |
| [`ci-021805-6874d919`](receipts/round-ci-021805-6874d919-result.json) | `Source_ReferenceIutCanLiftDeckGroup` | `383f70cd12f7` | succeeded | 0 | 52.64 | 48.49 (4.93 + 43.56) | 3.68 |
| [`ci-021806-7020411f`](receipts/round-ci-021806-7020411f-result.json) | `Source_ReferenceHeightsLatticePointMapAddition` | `8a0b798aeca8` | failed | 1 | 55.64 | 52.04 (4.15 + 47.89) | 3.99 |
| [`ci-021807-b0bde7bd`](receipts/round-ci-021807-b0bde7bd-result.json) | `Source_TripodTpdRamIdx` | `fc0dcffde300` | failed | 1 | 56.71 | 57.92 (6.60 + 51.32) | 4.14 |
| [`ci-021818-2b32f85f`](receipts/round-ci-021818-2b32f85f-result.json) | `Source_ReferenceIutConcreteLocalTheory` | `c865f165e9c0` | succeeded | 0 | 60.73 | 58.25 (5.46 + 52.79) | 4.41 |
| [`ci-021819-a1f17889`](receipts/round-ci-021819-a1f17889-result.json) | `Source_ReferenceIutCanLiftInvariantCoordinates` | `10024954b65c` | succeeded | 0 | 54.06 | 52.49 (4.43 + 48.06) | 4.00 |
| [`ci-021820-8e1c5508`](receipts/round-ci-021820-8e1c5508-result.json) | `Source_ReferenceIutTorsionFaithful` | `e553b53abd27` | failed | 1 | 45.55 | 44.99 (4.57 + 40.42) | 3.98 |
| [`ci-021821-b729dc7c`](receipts/round-ci-021821-b729dc7c-result.json) | `Source_TripodTpdGalois` | `57a6d095a818` | succeeded | 0 | 50.16 | 55.06 (14.25 + 40.81) | 4.26 |
| [`ci-021829-c6ba75e9`](receipts/round-ci-021829-c6ba75e9-result.json) | `Source_ReferenceIutConcreteLocalTheory` | `c865f165e9c0` | succeeded | 0 | 82.97 | 78.32 (6.42 + 71.90) | 4.43 |
| [`ci-021830-79e70319`](receipts/round-ci-021830-79e70319-result.json) | `Source_ReferenceIutThetaLocalRoots` | `15dd9ac1992c` | succeeded | 0 | 139.46 | 134.93 (11.15 + 123.78) | 7.56 |
| [`ci-021831-4d615b5d`](receipts/round-ci-021831-4d615b5d-result.json) | `Source_ReferenceIutCanLiftInvariantCoordinates` | `10024954b65c` | succeeded | 0 | 65.06 | 60.61 (4.76 + 55.85) | 4.01 |
| [`ci-021832-acf77054`](receipts/round-ci-021832-acf77054-result.json) | `Source_ReferenceIutCanLiftAnalyticTransitivity` | `b33316daea2e` | succeeded | 0 | 62.72 | 57.85 (4.35 + 53.50) | 3.95 |
| [`ci-021833-9ff7f547`](receipts/round-ci-021833-9ff7f547-result.json) | `Source_ReferenceIutCanLiftDeckGroup` | `383f70cd12f7` | succeeded | 0 | 62.49 | 58.47 (4.90 + 53.57) | 3.69 |
| [`ci-021834-4bb65932`](receipts/round-ci-021834-4bb65932-result.json) | `Source_TripodTpdGalois` | `57a6d095a818` | succeeded | 0 | 72.19 | 75.19 (14.46 + 60.73) | 4.27 |
| [`ci-021835-440b2a29`](receipts/round-ci-021835-440b2a29-result.json) | `ReviewCanLiftAnalyticReduction` | `4f87cbaa6944` | succeeded | 0 | 143.26 | 140.18 (7.20 + 132.98) | 8.06 |
| [`ci-021836-3773059c`](receipts/round-ci-021836-3773059c-result.json) | `Source_ReferenceHeightsLatticePointMapAddition` | `acd28d0bf99f` | succeeded | 0 | 58.91 | 57.46 (4.04 + 53.42) | 4.00 |
| [`ci-021840-0b7a0de4`](receipts/round-ci-021840-0b7a0de4-result.json) | `ReviewConcreteLocalTheory` | `deda439a66b6` | succeeded | 0 | 138.41 | 131.97 (6.04 + 125.93) | 8.07 |
| [`ci-021841-8a6ac6c3`](receipts/round-ci-021841-8a6ac6c3-result.json) | `Source_ReferenceIutCanLiftMobius` | `891ed66f991e` | succeeded | 0 | 61.16 | 58.88 (5.73 + 53.15) | 4.01 |
| [`ci-021842-03cb87e5`](receipts/round-ci-021842-03cb87e5-result.json) | `Source_ReferenceIutTorsionFaithful` | `9c51d7cd1ca2` | succeeded | 0 | 57.70 | 55.08 (5.35 + 49.73) | 3.97 |
| [`ci-021843-b961e0a7`](receipts/round-ci-021843-b961e0a7-result.json) | `Source_TripodTpdRamIdx` | `fc0dcffde300` | succeeded | 0 | 57.03 | 58.55 (9.48 + 49.07) | 4.15 |
| [`ci-021844-033323fe`](receipts/round-ci-021844-033323fe-result.json) | `Source_ReferenceHeightsLatticePointMapAddition` | `acd28d0bf99f` | succeeded | 0 | 56.99 | 55.86 (4.65 + 51.21) | 4.01 |
| [`ci-021847-bdbcde56`](receipts/round-ci-021847-bdbcde56-result.json) | `Source_ReferenceIutThetaLocalData` | `a431b549e1ad` | succeeded | 0 | 121.31 | 118.47 (7.96 + 110.51) | 7.54 |
| [`ci-021848-35662250`](receipts/round-ci-021848-35662250-result.json) | `Source_ReferenceIutCanLiftMobius` | `891ed66f991e` | succeeded | 0 | 58.58 | 55.80 (3.98 + 51.82) | 3.97 |
| [`ci-021849-53d7f2e8`](receipts/round-ci-021849-53d7f2e8-result.json) | `Source_ReferenceIutTorsionFaithful` | `9c51d7cd1ca2` | succeeded | 0 | 54.20 | 52.20 (5.31 + 46.89) | 3.98 |
| [`ci-021850-6b20449f`](receipts/round-ci-021850-6b20449f-result.json) | `Source_TripodTpdRamIdx` | `fc0dcffde300` | succeeded | 0 | 54.04 | 55.67 (9.60 + 46.07) | 4.15 |
| [`ci-021852-ac1e7fa2`](receipts/round-ci-021852-ac1e7fa2-result.json) | `Source_ReferenceIutCanLiftMobiusCommensurator` | `d371aae0414a` | succeeded | 0 | 100.00 | 97.39 (5.39 + 92.00) | 3.99 |
| [`ci-021854-08194afa`](receipts/round-ci-021854-08194afa-result.json) | `Source_TripodUnramified` | `2321121cc50e` | succeeded | 0 | 98.43 | 96.38 (5.40 + 90.98) | 4.18 |
| [`ci-021855-29503304`](receipts/round-ci-021855-29503304-result.json) | `Source_ReferenceIutThetaLocalData` | `a431b549e1ad` | succeeded | 0 | 225.64 | 222.92 (8.42 + 214.50) | 7.55 |
| [`ci-021861-93251ecc`](receipts/round-ci-021861-93251ecc-result.json) | `Source_ReferenceIutPointLocalTheta` | `b9fb8061afcf` | succeeded | 0 | 120.80 | 117.41 (6.15 + 111.26) | 7.52 |
| [`ci-021862-ed7db7d6`](receipts/round-ci-021862-ed7db7d6-result.json) | `Source_ReferenceIutCanLiftMobiusCommensurator` | `d371aae0414a` | succeeded | 0 | 58.77 | 55.88 (4.32 + 51.56) | 3.98 |
| [`ci-021863-4e968a40`](receipts/round-ci-021863-4e968a40-result.json) | `Source_TripodUnramified` | `2321121cc50e` | succeeded | 0 | 54.68 | 53.23 (4.56 + 48.67) | 4.17 |
| [`ci-021868-218756b5`](receipts/round-ci-021868-218756b5-result.json) | `Source_ReferenceIutCanLiftFixX` | `d02d2873e06b` | failed | 1 | 96.32 | 93.79 (5.59 + 88.20) | 7.57 |
| [`ci-021869-3b6db133`](receipts/round-ci-021869-3b6db133-result.json) | `Source_TripodTowerStepIII` | `867aae91d4db` | succeeded | 0 | 93.54 | 90.90 (5.64 + 85.26) | 7.57 |
| [`ci-021871-6f880c2d`](receipts/round-ci-021871-6f880c2d-result.json) | `Source_ReferenceHeightsTorsionArchimedean` | `5e1ed447988d` | failed | 1 | 43.10 | 41.41 (2.71 + 38.70) | 3.93 |
| [`ci-021875-64463767`](receipts/round-ci-021875-64463767-result.json) | `Source_ReferenceIutPointLocalTheta` | `b9fb8061afcf` | succeeded | 0 | 104.72 | 99.36 (6.40 + 92.96) | 7.57 |
| [`ci-021876-2e499dbc`](receipts/round-ci-021876-2e499dbc-result.json) | `Source_TripodTowerStepIII` | `867aae91d4db` | succeeded | 0 | 103.81 | 98.09 (6.09 + 92.00) | 7.57 |
| [`ci-021877-487a17ab`](receipts/round-ci-021877-487a17ab-result.json) | `ReviewTripodGoodReduction` | `c40d3a2f6a45` | succeeded | 0 | 114.76 | 110.19 (5.87 + 104.32) | 8.08 |
| [`ci-021884-70058d70`](receipts/round-ci-021884-70058d70-result.json) | `ReviewPointLocalTheta` | `aef659d69846` | succeeded | 0 | 141.66 | 130.64 (7.07 + 123.57) | 8.10 |
| [`ci-021885-759d4e11`](receipts/round-ci-021885-759d4e11-result.json) | `ReviewTripodTowerStepIII` | `f0e93101451a` | succeeded | 0 | 139.08 | 128.42 (6.53 + 121.89) | 8.09 |
| [`ci-021886-0a0b2a6b`](receipts/round-ci-021886-0a0b2a6b-result.json) | `Source_ReferenceIutCanLiftFixX` | `933eba4a40a9` | failed | 1 | 117.31 | 108.13 (5.93 + 102.20) | 7.57 |
| [`ci-021887-2c9398ec`](receipts/round-ci-021887-2c9398ec-result.json) | `Source_ReferenceHeightsTorsionArchimedean` | `8a9e1a365311` | succeeded | 0 | 55.63 | 52.18 (3.06 + 49.12) | 3.96 |
| [`ci-021897-2cc87a88`](receipts/round-ci-021897-2cc87a88-result.json) | `Source_ReferenceIutCanLiftFixX` | `659bf592a4fc` | failed | 1 | 126.19 | 122.21 (7.39 + 114.82) | 7.59 |
| [`ci-021898-8e4a2881`](receipts/round-ci-021898-8e4a2881-result.json) | `Source_ReferenceHeightsTorsionArchimedean` | `8a9e1a365311` | succeeded | 0 | 61.40 | 57.44 (4.21 + 53.23) | 4.00 |
| [`ci-021906-e744b110`](receipts/round-ci-021906-e744b110-result.json) | `Source_ReferenceHeightsTorsionBound` | `82ccb210fa06` | succeeded | 0 | 60.54 | 59.21 (2.89 + 56.32) | 3.90 |
| [`ci-021909-68a2fb4b`](receipts/round-ci-021909-68a2fb4b-result.json) | `Source_ReferenceHeightsTorsionBound` | `82ccb210fa06` | succeeded | 0 | 61.17 | 60.40 (2.81 + 57.59) | 3.94 |
| [`ci-021911-b40ef1a6`](receipts/round-ci-021911-b40ef1a6-result.json) | `Source_TripodCyclicBoundFromSource` | `6f3f049f62b0` | succeeded | 0 | 120.58 | 115.85 (5.98 + 109.87) | 7.42 |
| [`ci-021918-abdd1b9d`](receipts/round-ci-021918-abdd1b9d-result.json) | `Source_ReferenceIutCanLiftFixX` | `2787022b7238` | succeeded | 0 | 136.31 | 131.26 (7.42 + 123.84) | 7.59 |
| [`ci-021922-e0a843dc`](receipts/round-ci-021922-e0a843dc-result.json) | `Source_ReferenceIutCanLiftFixX` | `2787022b7238` | succeeded | 0 | 123.38 | 118.21 (8.06 + 110.15) | 7.59 |
| [`ci-021923-191e3814`](receipts/round-ci-021923-191e3814-result.json) | `Source_TripodCyclicBoundFromSource` | `6f3f049f62b0` | succeeded | 0 | 119.25 | 111.07 (6.39 + 104.68) | 7.51 |
| [`ci-021929-7709d914`](receipts/round-ci-021929-7709d914-result.json) | `ReviewHeightsTorsionBound` | `3df6a95caf5a` | succeeded | 0 | 127.26 | 122.95 (6.42 + 116.53) | 8.09 |
| [`ci-021930-9a866028`](receipts/round-ci-021930-9a866028-result.json) | `Source_ReferenceIutCanLiftFixX` | `2787022b7238` | succeeded | 0 | 109.72 | 104.50 (7.57 + 96.93) | 7.59 |
| [`ci-021931-6e6d6b06`](receipts/round-ci-021931-6e6d6b06-result.json) | `Source_ReferenceIutCanLiftFixX` (.olean) | `2787022b7238` | succeeded | 0 | 109.63 | 104.46 (7.12 + 97.34) | 7.59 |
| [`ci-021940-93a275bd`](receipts/round-ci-021940-93a275bd-result.json) | `Source_ReferenceIutCanLiftComplexAssembly` | `876a168af1aa` | succeeded | 0 | 134.84 | 126.99 (6.03 + 120.96) | 7.58 |
| [`ci-021941-ad2fc0d6`](receipts/round-ci-021941-ad2fc0d6-result.json) | `ReviewCanLiftFixX` | `3862409a0b8c` | succeeded | 0 | 151.66 | 143.69 (6.82 + 136.87) | 8.08 |
| [`ci-021935-909f8c9d`](receipts/round-ci-021935-909f8c9d-result.json) | `Source_ReferenceIutCanLiftComplexAssembly` | `876a168af1aa` | succeeded | 0 | 137.70 | 134.63 (5.90 + 128.73) | 7.44 |
| [`ci-021947-ff1caaa2`](receipts/round-ci-021947-ff1caaa2-result.json) | `Source_ReferenceIutCanLiftComplexAssembly` | `876a168af1aa` | succeeded | 0 | 129.22 | 128.00 (5.32 + 122.68) | 7.56 |
| [`ci-021953-47fff188`](receipts/round-ci-021953-47fff188-result.json) | `ReviewCanLiftComplexAssembly` | `cf58694fc972` | succeeded | 0 | 142.68 | 135.83 (5.12 + 130.71) | 7.85 |
| [`ci-021987-43324269`](receipts/round-ci-021987-43324269-result.json) | `Source_ReferenceIutTowerDifferentArithmetic` | `c7b372b9791c` | succeeded | 0 | 69.88 | 65.66 (7.23 + 58.43) | 4.13 |
| [`ci-021988-3edc625f`](receipts/round-ci-021988-3edc625f-result.json) | `Source_ReferenceIutTowerDifferentFormula` | `1581b2a2e23c` | succeeded | 0 | 60.14 | 56.87 (6.20 + 50.67) | 4.11 |
| [`ci-021991-7662100c`](receipts/round-ci-021991-7662100c-result.json) | `Source_TripodMultiplicativeDifference` | `44a452ffe233` | succeeded | 0 | 71.42 | 67.21 (4.98 + 62.23) | 4.14 |
| [`ci-021997-4aaf0ba6`](receipts/round-ci-021997-4aaf0ba6-result.json) | `Source_TripodMultiplicativeDifference` | `44a452ffe233` | succeeded | 0 | 75.53 | 71.49 (6.98 + 64.51) | 4.16 |
| [`ci-022001-1fee8709`](receipts/round-ci-022001-1fee8709-result.json) | `Source_TripodMultiplicativeUnipotence` | `cbb592bc379e` | succeeded | 0 | 77.34 | 75.40 (4.28 + 71.12) | 4.12 |
| [`ci-022008-42e93864`](receipts/round-ci-022008-42e93864-result.json) | `Source_TripodMultiplicativeUnipotence` | `cbb592bc379e` | succeeded | 0 | 74.78 | 74.09 (4.84 + 69.25) | 4.13 |
| [`ci-022010-a963a37c`](receipts/round-ci-022010-a963a37c-result.json) | `Source_TripodInertiaTransport` | `78a99a41563e` | timeout | unknown | 180.04 | unknown | unknown |
| [`ci-022014-09446e67`](receipts/round-ci-022014-09446e67-result.json) | `Source_TripodCyclicVeluArch` | `05606b5a9e4a` | succeeded | 0 | 172.91 | 165.90 (7.45 + 158.45) | 7.57 |
| [`ci-022015-3e3c904e`](receipts/round-ci-022015-3e3c904e-result.json) | `Source_TripodMultiplicativeSlopes` | `4f99bf7b86df` | succeeded | 0 | 78.43 | 79.77 (10.81 + 68.96) | 4.20 |
| [`ci-022016-55bae7de`](receipts/round-ci-022016-55bae7de-result.json) | `Source_TripodInertiaTransport` | `78a99a41563e` | failed | 1 | 156.62 | 151.14 (8.14 + 143.00) | 7.49 |
| [`ci-022023-8ecbd0a2`](receipts/round-ci-022023-8ecbd0a2-result.json) | `Source_TripodCyclicVeluArch` | `05606b5a9e4a` | succeeded | 0 | 136.71 | 135.14 (6.93 + 128.21) | 7.58 |
| [`ci-022033-6796478f`](receipts/round-ci-022033-6796478f-result.json) | `ReviewTripodCyclicVeluArch` | `e6eb986896b4` | succeeded | 0 | 139.44 | 137.36 (5.96 + 131.40) | 8.07 |
| [`ci-022035-a6f83117`](receipts/round-ci-022035-a6f83117-result.json) | `Source_TripodInertiaTransport` | `0a778981c23e` | failed | 1 | 113.85 | 110.70 (5.53 + 105.17) | 7.47 |
| [`ci-022044-baf5816d`](receipts/round-ci-022044-baf5816d-result.json) | `Source_TripodInertiaTransport` | `85c414c9323b` | succeeded | 0 | 121.92 | 120.15 (5.75 + 114.40) | 7.47 |
| [`ci-022048-c9a30a3f`](receipts/round-ci-022048-c9a30a3f-result.json) | `Source_TripodInertiaTransport` | `85c414c9323b` | succeeded | 0 | 135.32 | 134.87 (9.28 + 125.59) | 7.51 |
| [`ci-022049-e341f915`](receipts/round-ci-022049-e341f915-result.json) | `Source_TripodMultiplicativeDifference` | `44a452ffe233` | succeeded | 0 | 63.36 | 60.02 (6.04 + 53.98) | 4.14 |
| [`ci-022051-05edc933`](receipts/round-ci-022051-05edc933-result.json) | `Source_TripodMultiplicativeUnipotence` | `cbb592bc379e` | succeeded | 0 | 59.02 | 56.47 (5.21 + 51.26) | 4.13 |
| [`ci-022058-2c491a59`](receipts/round-ci-022058-2c491a59-result.json) | `Source_TripodInertiaUnipotent` | `7aaa2d21dfd6` | failed | 1 | 107.62 | 105.88 (5.85 + 100.03) | 7.54 |
| [`ci-022059-50033e38`](receipts/round-ci-022059-50033e38-result.json) | `Source_TripodTpdTorsionRep` | `29fd8ec33c8c` | failed | 1 | 52.24 | 52.42 (8.07 + 44.35) | 4.23 |
| [`ci-022068-ef5553f6`](receipts/round-ci-022068-ef5553f6-result.json) | `Source_TripodInertiaUnipotent` | `de97af115401` | succeeded | 0 | 94.38 | 93.78 (6.32 + 87.46) | 7.55 |
| [`ci-022074-4d57c233`](receipts/round-ci-022074-4d57c233-result.json) | `Source_TripodInertiaUnipotent` | `de97af115401` | succeeded | 0 | 97.03 | 96.02 (5.15 + 90.87) | 7.54 |
| [`ci-022087-e8155382`](receipts/round-ci-022087-e8155382-result.json) | `Source_TripodUnramified` | `cb5e9dedac80` | succeeded | 0 | 65.21 | 64.41 (3.40 + 61.01) | 4.17 |
| [`ci-022089-a540a1d0`](receipts/round-ci-022089-a540a1d0-result.json) | `Source_TripodUnramified` | `cb5e9dedac80` | succeeded | 0 | 73.50 | 72.86 (3.90 + 68.96) | 4.18 |
| [`ci-022092-641f0296`](receipts/round-ci-022092-641f0296-result.json) | `Source_TripodBadRamIdx` | `cd618d49936c` | timeout | unknown | 188.10 | unknown | unknown |
| [`ci-022100-79ef9118`](receipts/round-ci-022100-79ef9118-result.json) | `Source_TripodTpdTorsionRep` | `14c33a444f06` | succeeded | 0 | 76.27 | 77.74 (8.35 + 69.39) | 4.23 |
| [`ci-022105-ff9361d7`](receipts/round-ci-022105-ff9361d7-result.json) | `Source_TripodTpdTorsionRep` | `14c33a444f06` | succeeded | 0 | 56.51 | 57.67 (8.03 + 49.64) | 4.23 |
| [`ci-022108-55ef14ea`](receipts/round-ci-022108-55ef14ea-result.json) | `Source_TripodBadRamIdx` | `cd618d49936c` | failed | 1 | 100.62 | 99.83 (6.85 + 92.98) | 7.56 |
| [`ci-022116-17838ef4`](receipts/round-ci-022116-17838ef4-result.json) | `Source_TripodBadRamIdx` | `f3be4592de7e` | succeeded | 0 | 99.00 | 98.48 (6.53 + 91.95) | 7.55 |
| [`ci-022121-07369887`](receipts/round-ci-022121-07369887-result.json) | `Source_TripodBadRamIdx` | `f3be4592de7e` | succeeded | 0 | 96.56 | 96.30 (6.90 + 89.40) | 7.56 |
| [`ci-022125-19cce7ec`](receipts/round-ci-022125-19cce7ec-result.json) | `ReviewTripodBadRamIdx` | `9ed310945abd` | timeout | unknown | 755.05 | unknown | unknown |
| [`ci-022168-7011f51e`](receipts/round-ci-022168-7011f51e-result.json) | `Source_TripodTpdInertia` | `62935f6e8518` | failed | 1 | 126.72 | 128.44 (27.43 + 101.01) | 7.61 |
| [`ci-022174-4a8195b7`](receipts/round-ci-022174-4a8195b7-result.json) | `Source_TripodCyclicVeluPoints` | `3c539bb7accf` | failed | 1 | 102.89 | 103.96 (9.01 + 94.95) | 7.62 |
| [`ci-022183-c7d6f502`](receipts/round-ci-022183-c7d6f502-result.json) | `ReviewTripodRamificationTheorems` | `5b476b85953b` | succeeded | 0 | 149.65 | 147.85 (5.31 + 142.54) | 7.81 |
| [`ci-022210-8e1d476a`](receipts/round-ci-022210-8e1d476a-result.json) | `Source_TripodTpdInertia` | `0e12415b0e9a` | failed | 1 | 105.70 | 107.75 (10.68 + 97.07) | 7.61 |
| [`ci-022218-10804544`](receipts/round-ci-022218-10804544-result.json) | `Source_TripodCyclicVeluPoints` | `5fd6031bb02f` | failed | 1 | 100.20 | 100.58 (7.29 + 93.29) | 7.61 |
| [`ci-022222-f3a919cf`](receipts/round-ci-022222-f3a919cf-result.json) | `Source_TripodTpdInertia` | `1e5da1f5c211` | succeeded | 0 | 93.10 | 95.74 (10.57 + 85.17) | 7.62 |
| [`ci-022232-d1190d06`](receipts/round-ci-022232-d1190d06-result.json) | `Source_TripodCyclicVeluPoints` | `4205eec4043f` | succeeded | 0 | 93.16 | 95.16 (8.09 + 87.07) | 7.62 |
| [`ci-022238-ee692ddb`](receipts/round-ci-022238-ee692ddb-result.json) | `Source_TripodTpdInertia` | `1e5da1f5c211` | succeeded | 0 | 91.18 | 93.80 (10.70 + 83.10) | 7.62 |
| [`ci-022249-c543c091`](receipts/round-ci-022249-c543c091-result.json) | `Source_TripodCyclicVeluPoints` | `4205eec4043f` | succeeded | 0 | 96.44 | 98.13 (8.12 + 90.01) | 7.62 |
| [`ci-022255-2c5b55c1`](receipts/round-ci-022255-2c5b55c1-result.json) | `ReviewTripodTowerRamIdx` | `c02d29ad6b8b` | succeeded | 0 | 100.99 | 100.44 (5.46 + 94.98) | 8.09 |
| [`ci-022264-0b6cd23c`](receipts/round-ci-022264-0b6cd23c-result.json) | `ReviewTripodVeluPoints` | `b031d47dd1a5` | succeeded | 0 | 100.86 | 100.40 (5.45 + 94.95) | 8.09 |
| [`ci-022306-56e690f5`](receipts/round-ci-022306-56e690f5-result.json) | `Source_ReferenceIutTowerWildBound` | `651e5417981e` | failed | 1 | 82.68 | 81.67 (3.60 + 78.07) | 4.07 |
| [`ci-022311-9a20d92b`](receipts/round-ci-022311-9a20d92b-result.json) | `Source_TripodTpdDegree` | `4fc8ae1b8dbb` | succeeded | 0 | 118.98 | 116.10 (5.79 + 110.31) | 7.55 |
| [`ci-022313-c3a6c91d`](receipts/round-ci-022313-c3a6c91d-result.json) | `Source_TripodCyclicVeluDescent` | `60ffcaccf47b` | failed | 1 | 94.77 | 94.68 (7.51 + 87.17) | 7.60 |
| [`ci-022323-985b38a1`](receipts/round-ci-022323-985b38a1-result.json) | `Source_ReferenceIutTowerWildBound` | `c0ab2d8bc522` | succeeded | 0 | 40.83 | 40.18 (2.54 + 37.64) | 4.04 |
| [`ci-022327-24e76b6c`](receipts/round-ci-022327-24e76b6c-result.json) | `Source_TripodCyclicVeluDescent` | `9e1cdaae5914` | failed | 1 | 93.57 | 94.07 (8.03 + 86.04) | 7.60 |
| [`ci-022337-967b971f`](receipts/round-ci-022337-967b971f-result.json) | `Source_TripodCyclicVeluDescent` | `7fd99f2c22ab` | succeeded | 0 | 85.00 | 85.54 (7.84 + 77.70) | 7.60 |
| [`ci-022340-4fe7ef07`](receipts/round-ci-022340-4fe7ef07-result.json) | `Source_ReferenceIutTowerWildBound` | `c0ab2d8bc522` | succeeded | 0 | 46.26 | 45.39 (2.75 + 42.64) | 4.03 |
| [`ci-022344-f1081ac2`](receipts/round-ci-022344-f1081ac2-result.json) | `Source_TripodTpdDegree` | `4fc8ae1b8dbb` | succeeded | 0 | 91.18 | 90.57 (5.73 + 84.84) | 7.55 |
| [`ci-022346-6bc9f5b8`](receipts/round-ci-022346-6bc9f5b8-result.json) | `Source_ReferenceIutTowerReductionKernel` | `19007feab158` | succeeded | 0 | 29.14 | 28.16 (1.68 + 26.48) | 2.76 |
| [`ci-022348-8a787b6f`](receipts/round-ci-022348-8a787b6f-result.json) | `Source_TripodCyclicVeluDescent` | `7fd99f2c22ab` | succeeded | 0 | 93.76 | 93.60 (7.70 + 85.90) | 7.60 |
| [`ci-022356-38c5d13c`](receipts/round-ci-022356-38c5d13c-result.json) | `ReviewTripodVeluDescent` | `ce8f53b6cb94` | succeeded | 0 | 103.98 | 102.69 (4.73 + 97.96) | 7.80 |
| [`ci-022365-84ffdfdb`](receipts/round-ci-022365-84ffdfdb-result.json) | `Source_ReferenceIutTowerReductionKernel` | `19007feab158` | succeeded | 0 | 32.13 | 31.47 (1.57 + 29.90) | 2.79 |
| [`ci-022366-82933329`](receipts/round-ci-022366-82933329-result.json) | `Source_ReferenceIutTowerIntegralTorsion` | `ba030e90cbcf` | succeeded | 0 | 83.08 | 83.18 (6.37 + 76.81) | 7.57 |
| [`ci-022378-b611603a`](receipts/round-ci-022378-b611603a-result.json) | `Source_ReferenceIutTowerIntegralTorsion` | `ba030e90cbcf` | succeeded | 0 | 75.26 | 74.49 (4.92 + 69.57) | 7.55 |
| [`ci-022380-71bbc1ff`](receipts/round-ci-022380-71bbc1ff-result.json) | `Source_ReferenceIutTowerInertiaInvolution` | `91431d72e371` | succeeded | 0 | 76.41 | 78.43 (8.43 + 70.00) | 7.61 |
| [`ci-022382-817e0736`](receipts/round-ci-022382-817e0736-result.json) | `Source_ReferenceIutTowerInertiaInvolution` | `91431d72e371` | succeeded | 0 | 78.52 | 79.85 (8.45 + 71.40) | 7.59 |
| [`ci-022385-4490b584`](receipts/round-ci-022385-4490b584-result.json) | `Source_TripodTameTwo` | `0ea5aef5139d` | failed | 1 | 78.33 | 78.04 (6.15 + 71.89) | 7.61 |
| [`ci-022396-1ecb6f52`](receipts/round-ci-022396-1ecb6f52-result.json) | `Source_TripodTameTwo` | `21d46327b7cc` | succeeded | 0 | 86.38 | 86.53 (7.14 + 79.39) | 7.61 |
| [`ci-022399-527e6a18`](receipts/round-ci-022399-527e6a18-result.json) | `Source_TripodTameTwo` | `21d46327b7cc` | succeeded | 0 | 83.29 | 83.10 (6.48 + 76.62) | 7.61 |
| [`ci-022402-b5ce66ff`](receipts/round-ci-022402-b5ce66ff-result.json) | `Source_TripodWildRamIdx` | `9df98061d7e5` | failed | 1 | 79.31 | 78.34 (3.14 + 75.20) | 7.20 |
| [`ci-022406-aa16afa6`](receipts/round-ci-022406-aa16afa6-result.json) | `Source_TripodTameTwo` | `b7b4a7c7177c` | succeeded | 0 | 82.17 | 82.12 (6.75 + 75.37) | 7.61 |
| [`ci-022410-f598c120`](receipts/round-ci-022410-f598c120-result.json) | `Source_TripodWildRamIdx` | `9df98061d7e5` | succeeded | 0 | 82.24 | 81.74 (5.37 + 76.37) | 7.59 |
| [`ci-022412-f24083e4`](receipts/round-ci-022412-f24083e4-result.json) | `Source_TripodWildRamIdx` | `9df98061d7e5` | succeeded | 0 | 79.77 | 78.91 (5.37 + 73.54) | 7.58 |
| [`ci-022416-8f790241`](receipts/round-ci-022416-8f790241-result.json) | `ReviewTripodWildRamIdx` | `2ab1b5543792` | succeeded | 0 | 94.74 | 93.60 (5.17 + 88.43) | 7.80 |
| [`ci-022419-a354af65`](receipts/round-ci-022419-a354af65-result.json) | `Source_TripodTowerLocalFacts` | `b415e3798010` | failed | 1 | 80.77 | 80.15 (4.53 + 75.62) | 7.59 |
| [`ci-022422-92072e45`](receipts/round-ci-022422-92072e45-result.json) | `Source_TripodTowerLocalFacts` | `070eccb65a9c` | failed | 1 | 115.54 | 114.88 (5.20 + 109.68) | 7.59 |
| [`ci-022425-1c8a3663`](receipts/round-ci-022425-1c8a3663-result.json) | `Source_TripodTowerLocalFacts` | `9b43e19acc04` | succeeded | 0 | 105.15 | 104.69 (5.59 + 99.10) | 7.60 |
| [`ci-022427-91a544c2`](receipts/round-ci-022427-91a544c2-result.json) | `Source_TripodTowerLocalFacts` | `9b43e19acc04` | succeeded | 0 | 150.08 | 77.57 (5.39 + 72.18) | 7.62 |
| [`ci-022430-c2bb0aaa`](receipts/round-ci-022430-c2bb0aaa-result.json) | `Source_TripodP7` | `a1b368687cd2` | failed | 1 | 85.40 | 84.45 (5.10 + 79.35) | 7.57 |
| [`ci-022436-76b5a5d1`](receipts/round-ci-022436-76b5a5d1-result.json) | `Source_TripodP7` | `e14c86cc0842` | succeeded | 0 | 89.71 | 89.44 (5.73 + 83.71) | 7.66 |
| [`ci-022440-ab346cb5`](receipts/round-ci-022440-ab346cb5-result.json) | `Source_TripodP7` | `e14c86cc0842` | succeeded | 0 | 88.44 | 87.51 (4.67 + 82.84) | 7.65 |
| [`ci-022444-83f19d6e`](receipts/round-ci-022444-83f19d6e-result.json) | `ReviewTripodP7` | `ce88a8d509e4` | succeeded | 0 | 109.27 | 108.48 (5.42 + 103.06) | 8.11 |
| [`ci-022465-e6916c62`](receipts/round-ci-022465-e6916c62-result.json) | `Source_TripodCyclicVeluFinite` | `449c40579006` | succeeded | 0 | 104.73 | 104.29 (6.25 + 98.04) | 7.57 |
| [`ci-022476-2a77004d`](receipts/round-ci-022476-2a77004d-result.json) | `Source_TripodCyclicVeluFinite` | `449c40579006` | succeeded | 0 | 92.54 | 91.90 (6.40 + 85.50) | 7.56 |
| [`ci-022478-3f78166e`](receipts/round-ci-022478-3f78166e-result.json) | `Source_TripodCyclicVeluTate` | `4e4477215785` | failed | 1 | 97.71 | 96.82 (8.42 + 88.40) | 7.60 |
| [`ci-022485-66fa1083`](receipts/round-ci-022485-66fa1083-result.json) | `Source_TripodCyclicVeluTransport` | `bc2c472ec311` | failed | 1 | 86.10 | 85.73 (5.48 + 80.25) | 7.59 |
| [`ci-022486-e79c296a`](receipts/round-ci-022486-e79c296a-result.json) | `Source_ReferenceIutCanLiftCountableCoverField` | `249ee544cd40` | failed | 1 | 50.61 | 50.79 (5.42 + 45.37) | 2.89 |
| [`ci-022491-4a454cdf`](receipts/round-ci-022491-4a454cdf-result.json) | `Source_TripodCyclicVeluTransport` | `93e6b4f2b468` | failed | 1 | 142.40 | 140.49 (6.39 + 134.10) | 7.58 |
| [`ci-022500-414ae026`](receipts/round-ci-022500-414ae026-result.json) | `Source_TripodCyclicVeluTate` | `fd7988f66931` | failed | 1 | 93.53 | 93.91 (7.23 + 86.68) | 7.60 |
| [`ci-022505-d4e2d1d0`](receipts/round-ci-022505-d4e2d1d0-result.json) | `Source_ReferenceIutCanLiftCountableCoverField` | `c609a20096b1` | succeeded | 0 | 36.70 | 36.91 (5.45 + 31.46) | 2.88 |
| [`ci-022509-9c2db9c8`](receipts/round-ci-022509-9c2db9c8-result.json) | `Source_TripodCanonicalCorollary22` | `acfc3430c30b` | succeeded | 0 | 113.58 | 112.93 (5.20 + 107.73) | 7.65 |
| [`ci-022518-dcefa340`](receipts/round-ci-022518-dcefa340-result.json) | `Source_TripodCyclicVeluTransport` | `6250695c55cb` | succeeded | 0 | 99.79 | 99.43 (6.31 + 93.12) | 7.59 |
| [`ci-022521-7ca1f615`](receipts/round-ci-022521-7ca1f615-result.json) | `Source_TripodCyclicVeluTate` | `3ffd5addb32e` | failed | 1 | 96.49 | 97.10 (11.32 + 85.78) | 7.61 |
| [`ci-022527-974d0ff7`](receipts/round-ci-022527-974d0ff7-result.json) | `Source_ReferenceIutCanLiftCountableCoverField` | `c609a20096b1` | succeeded | 0 | 37.83 | 38.19 (6.65 + 31.54) | 2.89 |
| [`ci-022530-a9623071`](receipts/round-ci-022530-a9623071-result.json) | `Source_TripodCanonicalCorollary22` | `acfc3430c30b` | succeeded | 0 | 114.09 | 113.14 (5.75 + 107.39) | 7.65 |
| [`ci-022541-a2d2eb9e`](receipts/round-ci-022541-a2d2eb9e-result.json) | `Source_TripodCyclicVeluTransport` | `6250695c55cb` | succeeded | 0 | 93.63 | 93.18 (6.23 + 86.95) | 7.59 |
| [`ci-022547-86f02d7b`](receipts/round-ci-022547-86f02d7b-result.json) | `Source_TripodCyclicVeluTate` | `6123f2ab7497` | failed | 1 | 97.29 | 97.85 (8.54 + 89.31) | 7.62 |
| [`ci-022556-537d5b2f`](receipts/round-ci-022556-537d5b2f-result.json) | `Source_TripodCyclicVeluTate` | `5fde98153f95` | failed | 1 | 114.36 | 114.50 (8.71 + 105.79) | 7.61 |
| [`ci-022561-d4e2ce4d`](receipts/round-ci-022561-d4e2ce4d-result.json) | `ReviewTripodVeluFinite` | `035029783fd5` | succeeded | 0 | 165.64 | 164.28 (5.57 + 158.71) | 7.92 |
| [`ci-022572-9dbbddda`](receipts/round-ci-022572-9dbbddda-result.json) | `ReviewCanLiftCountableCoverField` | `7f187476cd65` | succeeded | 0 | 108.84 | 108.45 (6.53 + 101.92) | 7.86 |
| [`ci-022584-92ffefcd`](receipts/round-ci-022584-92ffefcd-result.json) | `ReviewTripodCanonicalCorollary22` | `aedec4986d1e` | succeeded | 0 | 109.34 | 108.60 (5.62 + 102.98) | 8.13 |
| [`ci-022590-a0cf4a02`](receipts/round-ci-022590-a0cf4a02-result.json) | `Source_TripodCyclicVeluTate` | `79fda000066f` | failed | 1 | 95.99 | 95.98 (7.42 + 88.56) | 7.60 |
| [`ci-022601-6f5952a9`](receipts/round-ci-022601-6f5952a9-result.json) | `Source_TripodCyclicVeluTate` | `2c5404705436` | failed | 1 | 100.02 | 99.96 (8.40 + 91.56) | 7.61 |
| [`ci-022606-f96f7b89`](receipts/round-ci-022606-f96f7b89-result.json) | `Source_ReferenceIutCanLiftConstantExtension` | `ae7c0789b5aa` | failed | 1 | 85.12 | 89.19 (55.51 + 33.68) | 5.32 |
| [`ci-022611-16e190cd`](receipts/round-ci-022611-16e190cd-result.json) | `Source_TripodCyclicVeluTate` | `6f7f9eba4f20` | failed | 1 | 106.48 | 107.07 (8.07 + 99.00) | 7.61 |
| [`ci-022621-486c8083`](receipts/round-ci-022621-486c8083-result.json) | `Source_TripodCyclicVeluTate` | `ebb77ce3211a` | succeeded | 0 | 96.62 | 96.53 (7.21 + 89.32) | 7.61 |
| [`ci-022624-7fcf2ec7`](receipts/round-ci-022624-7fcf2ec7-result.json) | `Source_ReferenceIutCanLiftConstantExtension` | `fd5925550259` | succeeded | 0 | 42.10 | 46.70 (13.00 + 33.70) | 3.49 |
| [`ci-022642-3cc0447c`](receipts/round-ci-022642-3cc0447c-result.json) | `Source_TripodCyclicVeluTate` | `ebb77ce3211a` | succeeded | 0 | 341.91 | 335.82 (8.17 + 327.65) | 7.61 |
| [`ci-022658-c94ec91e`](receipts/round-ci-022658-c94ec91e-result.json) | `Source_TripodCyclicVeluTate` | `ebb77ce3211a` | succeeded | 0 | 274.65 | 262.07 (9.82 + 252.25) | 7.63 |
| [`ci-022659-11d20da6`](receipts/round-ci-022659-11d20da6-result.json) | `Source_ReferenceIutCanLiftConstantExtension` | `fd5925550259` | succeeded | 0 | 99.98 | 95.32 (15.79 + 79.53) | 3.49 |
| [`ci-022662-6b98e797`](receipts/round-ci-022662-6b98e797-result.json) | `Source_TripodProviderRepresentation` | `cb017806bb8d` | timeout | unknown | 180.09 | unknown | unknown |
| [`ci-022669-4d6cbff6`](receipts/round-ci-022669-4d6cbff6-result.json) | `Source_TripodProviderRepresentation` | `cb017806bb8d` | failed | 1 | 184.45 | 177.30 (6.15 + 171.15) | 7.58 |
| [`ci-022670-0b60f6c5`](receipts/round-ci-022670-0b60f6c5-result.json) | `ReviewVeluTateAndCanLift` | `f6a3705d9af5` | succeeded | 0 | 192.40 | 184.66 (5.71 + 178.95) | 8.08 |
| [`ci-022671-ef6c0fda`](receipts/round-ci-022671-ef6c0fda-result.json) | `Source_TripodCyclicVeluLog` | `068295f74087` | succeeded | 0 | 177.29 | 170.96 (7.51 + 163.45) | 7.61 |
| [`ci-022685-a054b4f8`](receipts/round-ci-022685-a054b4f8-result.json) | `Source_TripodProviderRepresentation` | `38f5dd704e61` | succeeded | 0 | 222.41 | 214.96 (5.71 + 209.25) | 7.50 |
| [`ci-022695-812b673a`](receipts/round-ci-022695-812b673a-result.json) | `Source_TripodCyclicVeluLog` | `068295f74087` | succeeded | 0 | 232.45 | 231.42 (7.71 + 223.71) | 7.63 |
| [`ci-022696-82652122`](receipts/round-ci-022696-82652122-result.json) | `Source_ReferenceIutCanLiftConstantExtensionGalois` | `6187b5d8af79` | succeeded | 0 | 98.43 | 105.52 (20.12 + 85.40) | 3.50 |
| [`ci-022705-197c11df`](receipts/round-ci-022705-197c11df-result.json) | `Source_ReferenceIutCanLiftConstantExtensionGalois` | `6187b5d8af79` | succeeded | 0 | 86.96 | 99.24 (29.42 + 69.82) | 3.52 |
| [`ci-022706-7463dee8`](receipts/round-ci-022706-7463dee8-result.json) | `Source_TripodProviderRepresentation` | `38f5dd704e61` | succeeded | 0 | 194.87 | 190.62 (5.53 + 185.09) | 7.56 |
| [`ci-022707-a1e34206`](receipts/round-ci-022707-a1e34206-result.json) | `Thm_AbcAdaptation_Tripod_Cyclic_main_bound` | `310867d6061c` | timeout | unknown | 180.06 | unknown | unknown |
| [`ci-022718-824d934a`](receipts/round-ci-022718-824d934a-result.json) | `Thm_AbcAdaptation_Tripod_Cyclic_main_bound` | `310867d6061c` | failed | 1 | 261.40 | 261.07 (58.93 + 202.14) | 9.93 |
| [`ci-022719-08c2f20e`](receipts/round-ci-022719-08c2f20e-result.json) | `Source_ReferenceIutCanLiftConstantExtensionRamification` | `1a991524bac1` | failed | 1 | 107.79 | 132.34 (66.39 + 65.95) | 4.62 |
| [`ci-022720-25476fb9`](receipts/round-ci-022720-25476fb9-result.json) | `ReviewVeluLogCanLiftGaloisAndModRep` | `c3db9fc84213` | succeeded | 0 | 235.15 | 232.67 (5.21 + 227.46) | 7.89 |
| [`ci-022737-030eb4a9`](receipts/round-ci-022737-030eb4a9-result.json) | `Source_ReferenceIutCanLiftConstantExtensionRamification` | `61aedcbc150f` | succeeded | 0 | 106.90 | 120.50 (69.71 + 50.79) | 4.56 |
| [`ci-022738-eb000b49`](receipts/round-ci-022738-eb000b49-result.json) | `Source_TripodProviderRationality` | `a4aa77b6f0b6` | failed | 1 | 66.99 | 66.16 (3.60 + 62.56) | 4.18 |
| [`ci-022743-869a7b58`](receipts/round-ci-022743-869a7b58-result.json) | `Source_TripodProviderRationality` | `da615a51b2c6` | failed | 1 | 47.75 | 46.76 (3.17 + 43.59) | 4.18 |
| [`ci-022744-965f1203`](receipts/round-ci-022744-965f1203-result.json) | `Source_ReferenceIutCanLiftConstantExtensionRamification` | `61aedcbc150f` | succeeded | 0 | 90.09 | 102.65 (65.56 + 37.09) | 4.56 |
| [`ci-022749-b4f34e16`](receipts/round-ci-022749-b4f34e16-result.json) | `Source_TripodProviderRationality` | `93e7831eeba3` | succeeded | 0 | 67.47 | 64.30 (2.57 + 61.73) | 4.08 |
| [`ci-022750-59d570d8`](receipts/round-ci-022750-59d570d8-result.json) | `Source_ReferenceIutCanLiftConstantExtensionEtale` | `aec6451ef64d` | failed | 1 | 66.58 | 67.06 (15.17 + 51.89) | 3.45 |
| [`ci-022755-81767315`](receipts/round-ci-022755-81767315-result.json) | `Source_TripodProviderRationality` | `93e7831eeba3` | succeeded | 0 | 50.20 | 49.52 (2.62 + 46.90) | 4.16 |
| [`ci-022759-424cfbc4`](receipts/round-ci-022759-424cfbc4-result.json) | `ReviewCanLiftRamificationAndRationality` | `20f0bc58b701` | succeeded | 0 | 112.33 | 110.49 (4.92 + 105.57) | 7.85 |
| [`ci-022764-9bca17be`](receipts/round-ci-022764-9bca17be-result.json) | `Source_ReferenceIutCanLiftConstantExtensionEtale` | `1ac324dc3f03` | failed | 1 | 46.35 | 53.41 (14.59 + 38.82) | 3.53 |
| [`ci-022776-9b67f9ef`](receipts/round-ci-022776-9b67f9ef-result.json) | `Source_ReferenceIutCanLiftConstantExtensionEtale` | `5008e9f17794` | succeeded | 0 | 45.80 | 55.33 (18.21 + 37.12) | 3.58 |
| [`ci-022779-358d4cf9`](receipts/round-ci-022779-358d4cf9-result.json) | `Thm_AbcAdaptation_Tripod_Cyclic_main_bound` | `142d951004ca` | failed | 1 | 145.68 | 145.72 (7.60 + 138.12) | 7.62 |
| [`ci-022780-3d276d3f`](receipts/round-ci-022780-3d276d3f-result.json) | `Source_ReferenceIutCanLiftConstantExtensionEtale` | `5008e9f17794` | succeeded | 0 | 56.79 | 65.59 (19.06 + 46.53) | 3.57 |
| [`ci-022788-2d0c5545`](receipts/round-ci-022788-2d0c5545-result.json) | `Thm_AbcAdaptation_Tripod_Cyclic_main_bound` | `49d7e8620b26` | failed | 1 | 108.47 | 106.19 (7.23 + 98.96) | 7.62 |
| [`ci-022789-a679c21f`](receipts/round-ci-022789-a679c21f-result.json) | `ReviewCanLiftEtale` | `01baa8e75638` | succeeded | 0 | 119.62 | 114.60 (4.87 + 109.73) | 7.84 |
| [`ci-022799-28b9cc35`](receipts/round-ci-022799-28b9cc35-result.json) | `Thm_AbcAdaptation_Tripod_Cyclic_main_bound` | `f31a6c599d17` | succeeded | 0 | 98.41 | 98.71 (7.04 + 91.67) | 7.61 |
| [`ci-022801-6529fa30`](receipts/round-ci-022801-6529fa30-result.json) | `Thm_AbcAdaptation_Tripod_Cyclic_main_bound` | `f31a6c599d17` | succeeded | 0 | 95.91 | 93.90 (6.40 + 87.50) | 7.61 |
| [`ci-022802-e3b86255`](receipts/round-ci-022802-e3b86255-result.json) | `Source_ReferenceIutCanLiftConstantExtensionForward` | `1e9c4a4e82d4` | succeeded | 0 | 45.04 | 45.79 (11.03 + 34.76) | 3.43 |
| [`ci-022803-b8f97e7c`](receipts/round-ci-022803-b8f97e7c-result.json) | `Source_ReferenceIutCanLiftChangeParameter` | `ed0a5cd23216` | failed | 1 | 101.05 | 108.31 (73.42 + 34.89) | 3.58 |
| [`ci-022804-e216e65d`](receipts/round-ci-022804-e216e65d-result.json) | `Source_ReferenceIutCanLiftSignMultiplicity` | `df869118cc74` | failed | 1 | 90.15 | 98.73 (62.78 + 35.95) | 5.55 |
| [`ci-022808-047a35ae`](receipts/round-ci-022808-047a35ae-result.json) | `ReviewTripodVeluMain` | `03134f3eaffe` | succeeded | 0 | 123.22 | 122.55 (6.26 + 116.29) | 8.09 |
| [`ci-022813-a4544eaf`](receipts/round-ci-022813-a4544eaf-result.json) | `Thm_AbcAdaptation_Reference_Heights_exists_torsion_x_bound` | `28366becdd16` | succeeded | 0 | 44.02 | 40.74 (2.29 + 38.45) | 3.89 |
| [`ci-022814-c44ab3d7`](receipts/round-ci-022814-c44ab3d7-result.json) | `Thm_AbcAdaptation_Tripod_cyclicLocalGraphLine` | `6a7a330463eb` | succeeded | 0 | 86.61 | 83.93 (4.29 + 79.64) | 7.36 |
| [`ci-022815-02f661c5`](receipts/round-ci-022815-02f661c5-result.json) | `Source_ReferenceIutCanLiftChangeParameter` | `73032651ab5c` | failed | 1 | 188.56 | 205.17 (170.28 + 34.89) | 5.68 |
| [`ci-022819-34f5afb5`](receipts/round-ci-022819-34f5afb5-result.json) | `Thm_AbcAdaptation_Tripod_legendre_torsion_x_le` | `c4a74e4173f3` | succeeded | 0 | 43.05 | 40.03 (2.43 + 37.60) | 3.90 |
| [`ci-022820-4b309914`](receipts/round-ci-022820-4b309914-result.json) | `Source_ReferenceIutCanLiftSignMultiplicity` | `d43f05510e59` | succeeded | 0 | 48.59 | 53.16 (21.37 + 31.79) | 3.65 |
| [`ci-022821-252c5286`](receipts/round-ci-022821-252c5286-result.json) | `Source_ReferenceIutCanLiftConstantExtensionForward` | `1e9c4a4e82d4` | succeeded | 0 | 41.30 | 41.23 (10.70 + 30.53) | 3.43 |
| [`ci-022822-9f139553`](receipts/round-ci-022822-9f139553-result.json) | `Thm_AbcAdaptation_Tripod_cyclicBoundOdd` | `a7a45d3da3c5` | succeeded | 0 | 81.92 | 81.36 (4.76 + 76.60) | 7.59 |
| [`ci-022825-5942080c`](receipts/round-ci-022825-5942080c-result.json) | `ReviewTripodCyclicBound` | `47c81a679df6` | succeeded | 0 | 99.26 | 96.20 (5.53 + 90.67) | 8.10 |
| [`ci-022826-4ed1bcf3`](receipts/round-ci-022826-4ed1bcf3-result.json) | `Source_ReferenceIutCanLiftChangeParameter` | `297027c9b25b` | succeeded | 0 | 48.86 | 62.08 (30.73 + 31.35) | 3.55 |
| [`ci-022827-32a80b79`](receipts/round-ci-022827-32a80b79-result.json) | `Source_ReferenceIutCanLiftSignMultiplicity` | `d43f05510e59` | succeeded | 0 | 48.58 | 51.91 (20.31 + 31.60) | 3.61 |
| [`ci-022830-96a40723`](receipts/round-ci-022830-96a40723-result.json) | `Source_TripodCanonicalCorollary22` | `003af37bf85f` | succeeded | 0 | 83.96 | 82.27 (4.79 + 77.48) | 7.66 |
| [`ci-022831-fd4b0e80`](receipts/round-ci-022831-fd4b0e80-result.json) | `Source_ReferenceIutCanLiftChangeParameter` | `297027c9b25b` | succeeded | 0 | 47.16 | 63.59 (33.42 + 30.17) | 3.56 |
| [`ci-022835-61a98993`](receipts/round-ci-022835-61a98993-result.json) | `ReviewCanLiftCoverTransport` | `eafb87b978ba` | succeeded | 0 | 99.40 | 94.30 (4.43 + 89.87) | 7.85 |
| [`ci-022836-114956ad`](receipts/round-ci-022836-114956ad-result.json) | `Source_ReferenceIutCanLiftDescendedCover` | `9c54e9e7fa04` | failed | 1 | 68.07 | 83.11 (50.76 + 32.35) | 4.58 |
| [`ci-022837-af11d9dc`](receipts/round-ci-022837-af11d9dc-result.json) | `Source_TripodCanonicalCorollary22` | `003af37bf85f` | succeeded | 0 | 87.34 | 83.13 (4.67 + 78.46) | 7.57 |
| [`ci-022840-3258b7f9`](receipts/round-ci-022840-3258b7f9-result.json) | `ReviewCanonicalCorollary22Cyclic` | `7a926338aece` | succeeded | 0 | 99.80 | 98.32 (5.04 + 93.28) | 7.87 |
| [`ci-022841-4405a2a2`](receipts/round-ci-022841-4405a2a2-result.json) | `Source_ReferenceIutCanLiftDescendedCover` | `44b55e9dccf6` | succeeded | 0 | 72.87 | 88.79 (50.67 + 38.12) | 4.58 |
| [`ci-022847-23c017b4`](receipts/round-ci-022847-23c017b4-result.json) | `Source_ReferenceIutCanLiftDescendedCover` | `44b55e9dccf6` | succeeded | 0 | 71.49 | 86.49 (54.78 + 31.71) | 4.57 |
| [`ci-022848-fb8a5fe3`](receipts/round-ci-022848-fb8a5fe3-result.json) | `Source_ReferenceIutCanLiftQuadraticModel` | `92ffd2587e48` | failed | 1 | 89.19 | 89.56 (12.56 + 77.00) | 7.65 |
| [`ci-022849-42223f75`](receipts/round-ci-022849-42223f75-result.json) | `Source_ReferenceIutCanLiftRealization` | `0363f47d47a2` | failed | 1 | 76.93 | 77.45 (46.25 + 31.20) | 3.61 |
| [`ci-022857-2bd71c3a`](receipts/round-ci-022857-2bd71c3a-result.json) | `ReviewCanLiftDescendedCover` | `b5f513d90391` | succeeded | 0 | 101.37 | 99.80 (5.20 + 94.60) | 7.89 |
| [`ci-022858-2a5be950`](receipts/round-ci-022858-2a5be950-result.json) | `Source_ReferenceIutCanLiftQuadraticModel` | `2c6d31268e84` | failed | 1 | 96.98 | 100.11 (14.51 + 85.60) | 7.69 |
| [`ci-022863-2dc015f6`](receipts/round-ci-022863-2dc015f6-result.json) | `Source_ReferenceIutCanLiftQuadraticModel` | `d03df1a5ae85` | failed | 1 | 93.35 | 95.63 (13.95 + 81.68) | 7.70 |
| [`ci-022864-8e45067c`](receipts/round-ci-022864-8e45067c-result.json) | `Source_ReferenceIutCanLiftRealization` | `25d67a5d826d` | failed | 1 | 51.09 | 54.16 (19.98 + 34.18) | 3.63 |
| [`ci-022869-50e2e5b4`](receipts/round-ci-022869-50e2e5b4-result.json) | `Source_ReferenceIutCanLiftQuadraticModel` | `eafce0edb4ab` | succeeded | 0 | 105.27 | 109.71 (15.98 + 93.73) | 7.71 |
| [`ci-022870-3c9c8d72`](receipts/round-ci-022870-3c9c8d72-result.json) | `Source_ReferenceIutCanLiftRealization` | `8c25ec780b34` | succeeded | 0 | 41.67 | 44.65 (9.76 + 34.89) | 3.64 |
| [`ci-022876-b4db7b99`](receipts/round-ci-022876-b4db7b99-result.json) | `Source_ReferenceIutCanLiftQuadraticModel` | `eafce0edb4ab` | succeeded | 0 | 95.63 | 99.02 (17.31 + 81.71) | 7.73 |
| [`ci-022877-123f64ff`](receipts/round-ci-022877-123f64ff-result.json) | `Source_ReferenceIutCanLiftRealization` | `8c25ec780b34` | succeeded | 0 | 42.86 | 45.14 (11.21 + 33.93) | 3.64 |
| [`ci-022883-f2794060`](receipts/round-ci-022883-f2794060-result.json) | `Source_ReferenceIutCanLiftUnramifiedClosure` | `dabed72ad1be` | succeeded | 0 | 98.77 | 96.66 (16.76 + 79.90) | 7.72 |
| [`ci-022884-1f96e82a`](receipts/round-ci-022884-1f96e82a-result.json) | `ReviewCanLiftRealizationAndQuadraticModel` | `91e776c1a11e` | succeeded | 0 | 101.86 | 96.18 (6.37 + 89.81) | 8.08 |
| [`ci-022889-f4514897`](receipts/round-ci-022889-f4514897-result.json) | `Source_ReferenceIutCanLiftUnramifiedClosure` | `dabed72ad1be` | succeeded | 0 | 103.08 | 102.71 (18.78 + 83.93) | 7.76 |
| [`ci-022890-ca7a0cb4`](receipts/round-ci-022890-ca7a0cb4-result.json) | `Source_ReferenceIutCanLiftExtendedCover` | `bdc6f3f8fa51` | succeeded | 0 | 48.74 | 58.21 (26.25 + 31.96) | 3.59 |
| [`ci-022892-470be574`](receipts/round-ci-022892-470be574-result.json) | `Source_ReferenceIutPrimeCountingExplicit` | `48f32b5f83fa` | succeeded | 0 | 40.99 | 37.82 (2.34 + 35.48) | 3.94 |
| [`ci-022893-e0f2c3ff`](receipts/round-ci-022893-e0f2c3ff-result.json) | `Source_ReferenceIutCanLiftCoreCriterion` | `bfed0861f249` | succeeded | 0 | 79.95 | 77.16 (4.79 + 72.37) | 7.56 |
| [`ci-022894-6e421982`](receipts/round-ci-022894-6e421982-result.json) | `Source_ReferenceIutCanLiftExtendedCover` | `bdc6f3f8fa51` | succeeded | 0 | 45.46 | 53.33 (24.90 + 28.43) | 3.62 |
| [`ci-022899-6e73563b`](receipts/round-ci-022899-6e73563b-result.json) | `Source_ReferenceIutPrimeCountingExplicit` | `48f32b5f83fa` | succeeded | 0 | 39.24 | 36.05 (2.04 + 34.01) | 3.89 |
| [`ci-022900-64b43f34`](receipts/round-ci-022900-64b43f34-result.json) | `Source_ReferenceIutCanLiftCoreCriterion` | `bfed0861f249` | succeeded | 0 | 80.18 | 74.15 (4.78 + 69.37) | 7.54 |
| [`ci-022901-9e7b7555`](receipts/round-ci-022901-9e7b7555-result.json) | `Source_ReferenceIutCor312QPilotNormalization` | `ed1b010b3a3c` | failed | 1 | 80.04 | 73.68 (5.15 + 68.53) | 7.52 |
| [`ci-022905-43837a77`](receipts/round-ci-022905-43837a77-result.json) | `Source_ReferenceIutCanLiftCoreStar` | `59dbf69614b0` | failed | 1 | 87.39 | 95.07 (28.29 + 66.78) | 7.73 |
| [`ci-022906-bd4213ca`](receipts/round-ci-022906-bd4213ca-result.json) | `Source_ReferenceIutChebyshevExplicit` | `90fa992ba934` | succeeded | 0 | 34.67 | 33.21 (2.84 + 30.37) | 3.44 |
| [`ci-022907-fcc7953c`](receipts/round-ci-022907-fcc7953c-result.json) | `Source_ReferenceIutCor312QPilotNormalization` | `734c28846b5b` | succeeded | 0 | 77.01 | 71.89 (5.50 + 66.39) | 7.53 |
| [`ci-022909-af7dd6a8`](receipts/round-ci-022909-af7dd6a8-result.json) | `Source_ReferenceIutChebyshevExplicit` | `90fa992ba934` | succeeded | 0 | 33.67 | 32.18 (3.00 + 29.18) | 3.44 |
| [`ci-022910-5ab80b74`](receipts/round-ci-022910-5ab80b74-result.json) | `Source_ReferenceIutCor312QPilotNormalization` | `734c28846b5b` | succeeded | 0 | 79.17 | 75.30 (5.12 + 70.18) | 7.52 |
| [`ci-022911-3f6a3a0a`](receipts/round-ci-022911-3f6a3a0a-result.json) | `ReviewCanLiftCoreCriterionAndExtendedCover` | `d5129a459bd4` | succeeded | 0 | 90.55 | 85.37 (4.73 + 80.64) | 7.81 |
| [`ci-022914-3a6b1907`](receipts/round-ci-022914-3a6b1907-result.json) | `Source_ReferenceIutCanLiftCoreStar` | `c57157293e36` | failed | 1 | 86.18 | 94.97 (28.12 + 66.85) | 7.74 |
| [`ci-022915-599729ac`](receipts/round-ci-022915-599729ac-result.json) | `Source_TripodCanonicalCorollary22PrimeEstimates` | `0e168a69e5cf` | succeeded | 0 | 75.92 | 72.29 (4.90 + 67.39) | 7.64 |
| [`ci-022918-9ded0a79`](receipts/round-ci-022918-9ded0a79-result.json) | `Source_TripodCanonicalCorollary22PrimeEstimates` | `0e168a69e5cf` | succeeded | 0 | 81.43 | 79.96 (4.89 + 75.07) | 7.68 |
| [`ci-022926-2a7dcca5`](receipts/round-ci-022926-2a7dcca5-result.json) | `ReviewCorollary22PrimeEstimatesAndQPilot` | `5926a1b94345` | succeeded | 0 | 83.92 | 83.43 (5.25 + 78.18) | 8.14 |
| [`ci-022942-9cafaffb`](receipts/round-ci-022942-9cafaffb-result.json) | `Source_ReferenceIutCanLiftCoreStar` | `6bc5b9f96f93` | failed | 1 | 81.73 | 91.25 (25.00 + 66.25) | 7.78 |
| [`ci-022945-71d179dc`](receipts/round-ci-022945-71d179dc-result.json) | `Source_ReferenceIutCanLiftCoreStar` | `b87faf1a5444` | succeeded | 0 | 158.38 | 96.07 (21.37 + 74.70) | 7.73 |
| [`ci-022951-b5c0f3ca`](receipts/round-ci-022951-b5c0f3ca-result.json) | `Source_ReferenceIutCanLiftCoreStar` | `b87faf1a5444` | succeeded | 0 | 85.77 | 95.04 (25.29 + 69.75) | 7.76 |
| [`ci-022956-5db02b9d`](receipts/round-ci-022956-5db02b9d-result.json) | `Source_ReferenceIutCanLiftCountableRigidity` | `cd194346c7cd` | failed | 1 | 127.43 | 126.69 (7.62 + 119.07) | 7.60 |
| [`ci-022968-0c264d0d`](receipts/round-ci-022968-0c264d0d-result.json) | `Source_ReferenceIutCanLiftCountableRigidity` | `2bb133eff894` | succeeded | 0 | 93.64 | 93.51 (6.78 + 86.73) | 7.60 |
| [`ci-022977-1d051a00`](receipts/round-ci-022977-1d051a00-result.json) | `Source_ReferenceIutCanLiftCountableRigidity` | `2bb133eff894` | succeeded | 0 | 131.69 | 130.93 (6.76 + 124.17) | 7.60 |
| [`ci-022986-cf361e8d`](receipts/round-ci-022986-cf361e8d-result.json) | `Source_ReferenceIutCanLiftEmbeddingDescent` | `45c859224625` | failed | 1 | 150.96 | 148.91 (6.81 + 142.10) | 7.59 |
| [`ci-023007-722a5c99`](receipts/round-ci-023007-722a5c99-result.json) | `Source_ReferenceIutCanLiftEmbeddingDescent` | `ffc19400c926` | succeeded | 0 | 174.30 | 172.16 (5.96 + 166.20) | 7.56 |
| [`ci-023015-92216e88`](receipts/round-ci-023015-92216e88-result.json) | `Source_ReferenceIutCanLiftEmbeddingDescent` | `ffc19400c926` | succeeded | 0 | 150.92 | 149.04 (5.76 + 143.28) | 7.55 |
| [`ci-023023-b44f7634`](receipts/round-ci-023023-b44f7634-result.json) | `Source_ReferenceIutCanLiftLefschetz` | `c5cdb2c85f31` | succeeded | 0 | 102.11 | 101.63 (5.51 + 96.12) | 7.58 |
| [`ci-023037-1420731c`](receipts/round-ci-023037-1420731c-result.json) | `Source_ReferenceIutCanLiftLefschetz` | `c5cdb2c85f31` | succeeded | 0 | 96.95 | 95.74 (4.48 + 91.26) | 7.49 |
| [`ci-023046-3367d913`](receipts/round-ci-023046-3367d913-result.json) | `ReviewCanLiftLefschetz` | `0cd6d839e652` | succeeded | 0 | 124.51 | 121.13 (4.98 + 116.15) | 7.87 |
| [`ci-023065-98e0e8a4`](receipts/round-ci-023065-98e0e8a4-result.json) | `Source_ReferenceIutCor312QPilotLeftHandSide` | `1455ea9ba2a3` | succeeded | 0 | 127.94 | 126.18 (4.87 + 121.31) | 7.39 |
| [`ci-023074-ee35f7a3`](receipts/round-ci-023074-ee35f7a3-result.json) | `Source_ReferenceIutCor312UniversalAudit` | `faf70a96fe3a` | failed | 1 | 86.53 | 85.79 (5.14 + 80.65) | 7.53 |
| [`ci-023080-3ec504d9`](receipts/round-ci-023080-3ec504d9-result.json) | `Source_ReferenceIutCor312QPilotModuli` | `6b1b846cc5a0` | failed | 1 | 104.08 | 103.80 (7.32 + 96.48) | 7.54 |
| [`ci-023098-ad06ea9d`](receipts/round-ci-023098-ad06ea9d-result.json) | `Source_ReferenceIutCor312UniversalAudit` | `dd4c9dc061a3` | failed | 1 | 108.66 | 108.58 (12.07 + 96.51) | 7.58 |
| [`ci-023108-6c61bec9`](receipts/round-ci-023108-6c61bec9-result.json) | `Source_ReferenceIutCor312QPilotModuli` | `0b0dd3ec91f3` | succeeded | 0 | 102.43 | 102.06 (7.03 + 95.03) | 7.54 |
| [`ci-023115-3784965b`](receipts/round-ci-023115-3784965b-result.json) | `Source_ReferenceIutCor312QPilotModuli` | `0b0dd3ec91f3` | succeeded | 0 | 153.43 | 152.43 (7.90 + 144.53) | 7.54 |
| [`ci-023124-b4a11c04`](receipts/round-ci-023124-b4a11c04-result.json) | `Source_ReferenceIutCor312UniversalAudit` | `d408d42d54c9` | failed | 1 | 131.82 | 131.28 (7.00 + 124.28) | 7.56 |
| [`ci-023136-c76e9aad`](receipts/round-ci-023136-c76e9aad-result.json) | `Source_ReferenceIutCor312RepresentativeQPilot` | `b8b03805c07a` | failed | 1 | 111.11 | 111.95 (8.78 + 103.17) | 7.54 |
| [`ci-023146-92a4a68d`](receipts/round-ci-023146-92a4a68d-result.json) | `Source_ReferenceIutCor312UniversalAudit` | `a2237987ac11` | succeeded | 0 | 138.62 | 137.54 (6.79 + 130.75) | 7.54 |
| [`ci-023154-fe73209f`](receipts/round-ci-023154-fe73209f-result.json) | `Source_ReferenceIutCor312UniversalAudit` | `a2237987ac11` | succeeded | 0 | 134.47 | 133.78 (7.46 + 126.32) | 7.56 |
| [`ci-023160-024629d3`](receipts/round-ci-023160-024629d3-result.json) | `ReviewCor312UniversalAudit` | `30a262e9e753` | succeeded | 0 | 133.52 | 133.05 (6.32 + 126.73) | 8.10 |
| [`ci-023185-6914a085`](receipts/round-ci-023185-6914a085-result.json) | `Source_TripodP7` | `faac254ffddf` | succeeded | 0 | 136.90 | 135.59 (6.17 + 129.42) | 7.66 |
| [`ci-023198-fdc5012d`](receipts/round-ci-023198-fdc5012d-result.json) | `Source_TripodP7` | `7fbdd785c0f4` | succeeded | 0 | 126.37 | 125.52 (5.90 + 119.62) | 7.66 |
| [`ci-023203-60378860`](receipts/round-ci-023203-60378860-result.json) | `Source_TripodCanonicalCorollary22` | `a5b001d5bb5c` | succeeded | 0 | 117.81 | 116.34 (5.06 + 111.28) | 7.58 |
| [`ci-023210-c012f4af`](receipts/round-ci-023210-c012f4af-result.json) | `Source_TripodCanonicalCorollary22PrimeEstimates` | `6ecc34b3c619` | succeeded | 0 | 105.46 | 104.88 (4.96 + 99.92) | 7.67 |
| [`ci-023216-05d51023`](receipts/round-ci-023216-05d51023-result.json) | `Source_TripodStatementIIOnSourceP7` | `96950abe7cee` | succeeded | 0 | 91.30 | 90.65 (4.75 + 85.90) | 7.59 |
| [`ci-023221-806cefe2`](receipts/round-ci-023221-806cefe2-result.json) | `Source_TripodStatementIIOnSourceP7` | `96950abe7cee` | succeeded | 0 | 95.11 | 94.60 (5.46 + 89.14) | 7.68 |
| [`ci-023226-fcded28f`](receipts/round-ci-023226-fcded28f-result.json) | `ReviewSourceP7Corollary22StatementII` | `64a153920744` | succeeded | 0 | 105.42 | 104.93 (5.43 + 99.50) | 8.14 |
| [`ci-023231-19e3419e`](receipts/round-ci-023231-19e3419e-result.json) | `Source_ReferenceIutCor312RepresentativeQPilot` | `8b13b5749ee6` | succeeded | 0 | 97.31 | 98.18 (7.25 + 90.93) | 7.54 |
| [`ci-023238-e8c033ae`](receipts/round-ci-023238-e8c033ae-result.json) | `Source_ReferenceIutCor312RepresentativeQPilot` | `94481bbd6b9d` | succeeded | 0 | 129.40 | 130.35 (7.48 + 122.87) | 7.55 |
| [`ci-023245-51a64279`](receipts/round-ci-023245-51a64279-result.json) | `Source_ReferenceIutPointModuliMap` | `2209977b3732` | succeeded | 0 | 97.98 | 97.55 (5.37 + 92.18) | 7.57 |
| [`ci-023250-54dbcc3c`](receipts/round-ci-023250-54dbcc3c-result.json) | `Source_ReferenceIutPointModuliMap` | `2209977b3732` | succeeded | 0 | 96.72 | 95.57 (5.07 + 90.50) | 7.56 |
| [`ci-023254-f2147293`](receipts/round-ci-023254-f2147293-result.json) | `Source_ReferenceIutCor312QPilotLeftHandSide` | `1455ea9ba2a3` | succeeded | 0 | 102.36 | 101.22 (4.26 + 96.96) | 7.50 |
| [`ci-023258-e891f8b6`](receipts/round-ci-023258-e891f8b6-result.json) | `ReviewCor312QPilotSection` | `d072b0d18914` | succeeded | 0 | 128.25 | 127.34 (5.50 + 121.84) | 8.08 |
| [`ci-023268-d88b34a8`](receipts/round-ci-023268-d88b34a8-result.json) | `Def_AbcAdaptation_Tripod_FinitePlaceInertiaDegree` | `771e7114a677` | succeeded | 0 | 49.24 | 48.45 (2.39 + 46.06) | 3.81 |
| [`ci-023270-cf9327da`](receipts/round-ci-023270-cf9327da-result.json) | `Def_AbcAdaptation_Tripod_FinitePlaceInertiaDegree` | `771e7114a677` | succeeded | 0 | 48.13 | 47.38 (2.56 + 44.82) | 3.82 |
| [`ci-023273-ec878d83`](receipts/round-ci-023273-ec878d83-result.json) | `MultiplicativePlaceSolution` | `41f6c88ee7df` | failed | 1 | 5.99 | 5.02 (0.17 + 4.85) | 0.36 |
| [`ci-023275-cf063ad6`](receipts/round-ci-023275-cf063ad6-result.json) | `MultiplicativePlaceSolution` | `41f6c88ee7df` | succeeded | 0 | 58.39 | 57.55 (3.12 + 54.43) | 4.09 |
| [`ci-023280-88f7bee7`](receipts/round-ci-023280-88f7bee7-result.json) | `GoodReductionSolution` | `5c007c8c855a` | succeeded | 0 | 76.31 | 75.54 (2.98 + 72.56) | 4.03 |
| [`ci-023286-643b9760`](receipts/round-ci-023286-643b9760-result.json) | `ReviewMultiplicativePlaceSolution` | `4e53900b2b02` | succeeded | 0 | 97.80 | 96.50 (3.10 + 93.40) | 4.68 |
| [`ci-023291-ebe7c284`](receipts/round-ci-023291-ebe7c284-result.json) | `ReviewGoodReductionSolution` | `42b9d3870712` | succeeded | 0 | 52.40 | 51.32 (3.51 + 47.81) | 4.59 |
| [`ci-023299-65e8fe12`](receipts/round-ci-023299-65e8fe12-result.json) | `Source_ReferenceIutCanLiftPolynomialDegree` | `695c00166361` | succeeded | 0 | 31.45 | 30.51 (1.76 + 28.75) | 2.72 |
| [`ci-023305-2ffe021e`](receipts/round-ci-023305-2ffe021e-result.json) | `Source_ReferenceIutCanLiftPolynomialOrbifoldCount` | `52b4563b7437` | succeeded | 0 | 43.89 | 44.59 (3.75 + 40.84) | 2.82 |
| [`ci-023310-6ee7927c`](receipts/round-ci-023310-6ee7927c-result.json) | `Source_ReferenceIutCanLiftPolynomialOrbifoldCount` | `760165f4f7cc` | succeeded | 0 | 38.62 | 39.60 (4.34 + 35.26) | 2.83 |
| [`ci-023314-0210da97`](receipts/round-ci-023314-0210da97-result.json) | `Source_ReferenceIutCanLiftWeierstrassOrbifoldCount` | `c13385c1e1e7` | succeeded | 0 | 41.79 | 41.16 (2.76 + 38.40) | 3.52 |
| [`ci-023320-61f8cbb9`](receipts/round-ci-023320-61f8cbb9-result.json) | `Source_ReferenceIutCanLiftWeierstrassOrbifoldCount` | `c13385c1e1e7` | succeeded | 0 | 37.20 | 36.22 (2.35 + 33.87) | 3.46 |
| [`ci-023324-4a0a2990`](receipts/round-ci-023324-4a0a2990-result.json) | `ReviewCanLiftOrbifoldCount` | `7b3daa14c535` | succeeded | 0 | 97.24 | 95.88 (5.82 + 90.06) | 8.01 |
| [`ci-023346-02b8f7a4`](receipts/round-ci-023346-02b8f7a4-result.json) | `Source_ReferenceIutCor312PointRepresentativeWeight` | `ab37a7c1f3b1` | succeeded | 0 | 129.33 | 127.82 (6.28 + 121.54) | 7.57 |
| [`ci-023353-65caf5fb`](receipts/round-ci-023353-65caf5fb-result.json) | `Source_ReferenceIutCor312PointRepresentativeWeight` | `39491648b3a0` | succeeded | 0 | 110.66 | 109.84 (5.81 + 104.03) | 7.58 |
| [`ci-023357-6f06b3a0`](receipts/round-ci-023357-6f06b3a0-result.json) | `ReviewCor312PointRepresentativeWeight` | `85f6bf9c01b1` | succeeded | 0 | 95.19 | 94.48 (5.20 + 89.28) | 8.09 |
| [`ci-023362-895759bd`](receipts/round-ci-023362-895759bd-result.json) | `Source_ReferenceIutCor312ArchimedeanVolume` | `9c85353bb0f1` | failed | 1 | 81.89 | 81.57 (6.12 + 75.45) | 7.58 |
| [`ci-023369-8a64fc8d`](receipts/round-ci-023369-8a64fc8d-result.json) | `Source_ReferenceIutCor312ArchimedeanVolume` | `f023087bca87` | succeeded | 0 | 75.11 | 74.90 (6.42 + 68.48) | 7.58 |
| [`ci-023374-bc71f12b`](receipts/round-ci-023374-bc71f12b-result.json) | `Source_ReferenceIutCor312ArchimedeanVolume` | `f023087bca87` | succeeded | 0 | 107.91 | 107.49 (7.07 + 100.42) | 7.58 |
| [`ci-023384-21d4e243`](receipts/round-ci-023384-21d4e243-result.json) | `ReviewCor312ArchimedeanVolume` | `7eabba52646b` | succeeded | 0 | 93.67 | 93.07 (5.53 + 87.54) | 8.09 |
| [`ci-023403-6ac16647`](receipts/round-ci-023403-6ac16647-result.json) | `Source_ReferenceIutCanLiftFirstCoordinateRigidity` | `79d0a484c35d` | failed | 1 | 38.16 | 37.24 (2.32 + 34.92) | 3.93 |
| [`ci-023407-a3cb40e4`](receipts/round-ci-023407-a3cb40e4-result.json) | `Source_ReferenceIutCanLiftFirstCoordinateRigidity` | `09fcb900a8ee` | succeeded | 0 | 62.15 | 61.30 (3.04 + 58.26) | 3.99 |
| [`ci-023409-d0232724`](receipts/round-ci-023409-d0232724-result.json) | `Source_ReferenceIutCanLiftFirstCoordinateRigidity` | `09fcb900a8ee` | succeeded | 0 | 46.38 | 45.23 (2.42 + 42.81) | 3.91 |
| [`ci-023411-5ce2deb3`](receipts/round-ci-023411-5ce2deb3-result.json) | `Source_ReferenceIutCanLiftComplexAssembly` | `65d8e4c3e669` | succeeded | 0 | 127.54 | 125.94 (5.29 + 120.65) | 7.58 |
| [`ci-023417-776cb585`](receipts/round-ci-023417-776cb585-result.json) | `ReviewCanLiftFirstCoordinateRigidity` | `21be695d317f` | succeeded | 0 | 154.44 | 152.28 (5.53 + 146.75) | 8.09 |
| [`ci-023428-b24051a5`](receipts/round-ci-023428-b24051a5-result.json) | `Source_ReferenceIutConcreteLocalFinitePrincipalOrbit` | `f9b6aa58608b` | failed | 1 | 82.39 | 82.07 (8.20 + 73.87) | 4.18 |
| [`ci-023439-734f175e`](receipts/round-ci-023439-734f175e-result.json) | `Source_ReferenceIutConcreteLocalFinitePrincipalOrbit` | `da51ac87cf32` | succeeded | 0 | 72.55 | 72.72 (6.87 + 65.85) | 4.19 |
| [`ci-023442-aec36080`](receipts/round-ci-023442-aec36080-result.json) | `Source_ReferenceIutConcreteLocalFinitePrincipalVolume` | `a793f937088e` | failed | 1 | 91.78 | 96.95 (26.31 + 70.64) | 4.25 |
| [`ci-023453-02558773`](receipts/round-ci-023453-02558773-result.json) | `Source_ReferenceIutConcreteLocalFinitePrincipalVolume` | `7762bcad57a4` | failed | 1 | 93.41 | 93.27 (20.96 + 72.31) | 4.24 |
| [`ci-023460-65df3d83`](receipts/round-ci-023460-65df3d83-result.json) | `Source_ReferenceIutCor312GlobalVolume` | `4425a18941f2` | failed | 1 | 105.02 | 103.69 (4.71 + 98.98) | 7.47 |
| [`ci-023466-343ccaf5`](receipts/round-ci-023466-343ccaf5-result.json) | `Source_ReferenceIutCor312GlobalVolume` | `25f9e0139d9c` | failed | 1 | 104.77 | 105.98 (22.25 + 83.73) | 7.58 |
| [`ci-023494-ff68e44c`](receipts/round-ci-023494-ff68e44c-result.json) | `Source_ReferenceIutCor312GlobalVolume` | `c9137dfd67ba` | failed | 1 | 182.33 | 181.62 (27.62 + 154.00) | 7.59 |
| [`ci-023506-96013c92`](receipts/round-ci-023506-96013c92-result.json) | `Source_ReferenceIutConcreteLocalFinitePrincipalVolume` | `89d8cdf5e4c7` | succeeded | 0 | 98.49 | 94.71 (5.15 + 89.56) | 4.16 |
| [`ci-023516-4883e8e3`](receipts/round-ci-023516-4883e8e3-result.json) | `Source_ReferenceIutConcreteLocalFinitePrincipalVolume` | `89d8cdf5e4c7` | succeeded | 0 | 147.10 | 141.44 (5.07 + 136.37) | 4.14 |
| [`ci-023522-f4c700f6`](receipts/round-ci-023522-f4c700f6-result.json) | `ReviewCor312FinitePrincipalVolume` | `90d1b7ce63c7` | succeeded | 0 | 336.62 | 333.76 (7.84 + 325.92) | 8.07 |
| [`ci-023538-c82484a1`](receipts/round-ci-023538-c82484a1-result.json) | `Source_ReferenceIutCor312FiniteThetaHullVolume` | `0792cdf64bc5` | timeout | unknown | 180.13 | unknown | unknown |
