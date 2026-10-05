# JoshiTeich 来源登记

本文件登记 `ArithmeticTeichmullerSpaces/` 中声明的来源和验证状态。`refer/iut`
不是本工程的上游、Lake 依赖或证明来源；它只能作为逐文件 API 参考。

## 冻结环境

- Lean: `v4.35.0-rc3`, commit `470d5ce1400764999581fd26d5d72b00d990b0f4`
- mathlib4: local path `/home/admin-wsl/Coq/mathlib4`, commit
  `389347a7c1cfa76f6bd5be2ca35d4cb621610ad3`
- Lean project root: `ArithmeticTeichmullerSpaces/`
- Development rule: after development starts, these versions and the toolchain are frozen.

## JoshiTeich references

| source-id | Reference | Used by | Status |
| --- | --- | --- | --- |
| `JT-AHS` | `refer/JoshiTeich/index-Arithmetic Holomorphic Structures.md` | arithmetic holomorphic structures, untilt and tempered objects | specification |
| `JT-ATS-I` | `refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 1.md` | Berkovich/tempered invariance and adelic objects | specification |
| `JT-ATS-II` | `refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 2.md` | Tate data, `q` scaling and theta-pilot prototype | specification |
| `JT-ATS-II5` | `refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 2.5.md` | arithmeticoid, height and different/conductor interfaces | specification |
| `JT-ATS-III` | `refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md` | theta-link, log-shell and Corollary 3.12 interfaces | specification |
| `JT-ATS-IV` | `refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 4.md` | main bounds, Vojta and `abc` dependency chain | specification |

## Current Lean declarations

| source-id | Declaration | File | Status |
| --- | --- | --- | --- |
| `JT-M-NF-FINPLACE` | `NumberField.FinitePlace` | mathlib `NumberField/Completion/FinitePlace.lean` | imported mathlib type |
| `JT-M-RAT-RINGINT` | `Rat.ringOfIntegersEquiv` | mathlib `NumberTheory/NumberField/Basic.lean` | imported mathlib equivalence |
| `JT-M-DIFFERENT-IDEAL` | `differentIdeal`, `NumberField.absNorm_differentIdeal` | mathlib `NumberTheory/NumberField/Discriminant/Different.lean` | imported ideal and norm theorem |
| `JT-ATS-II5-ARITH-DIVISOR` | `FinitePlaceDivisor`, `logDegree` | `ArithmeticTeichmullerSpaces/Prologue/Arithmetic/Basic.lean` | D-adapter from II.5 `def:arith-deg-ideloid`, lines 1176-1182 |
| `JT-ATS-II5-HEIGHT` | `HeightData`, `HeightData.value_nonneg` | `ArithmeticTeichmullerSpaces/Prologue/Arithmetic/Basic.lean` | finite-place height interface from II.5 `def:heights`, lines 1657-1663 |
| `JT-ATS-IV-RAMIFICATION` | `RamificationProfile`, `differentLog`, `logTotal` | `ArithmeticTeichmullerSpaces/Prologue/Arithmetic/Basic.lean` | D-adapter from IV `pr:basic-ramification-data`, lines 1430-1440; `re:diff-rmk`, lines 1496-1502; `pr:tate-divisor`, lines 1542-1563; `th:diff-cond-thm`, lines 1661-1753 |
| `JT-M-PRETILT-UNTILT` | `PreTilt.untilt`, `PreTilt.mk_untilt_eq_coeff_zero`, `PreTilt.untilt_iterate_frobeniusEquiv_symm_pow` | mathlib `RingTheory/Perfectoid/Untilt.lean` | imported untilt map and reduction/Frobenius laws |
| `JT-M-FONTAINE-THETA` | `WittVector.fontaineTheta`, `WittVector.fontaineTheta_teichmuller` | mathlib `RingTheory/Perfectoid/FontaineTheta.lean` | imported Fontaine theta map and Teichmuller compatibility |
| `JT-ATS-PROLOGUE-PERFECTOID` | `untiltMap`, `thetaMap`, `UntiltingLaws`, `FontaineThetaLaws` and canonical law theorems | `ArithmeticTeichmullerSpaces/Prologue/Perfectoid/Untilts.lean` | D-adapter preserving explicit untilt, reduction, Frobenius and theta laws |
| `JT-ATS-PROLOGUE-PERFECTOID-DATA` | `PerfectoidData`, `PerfectoidLaws`, `canonicalPerfectoidData` and its law theorem | `ArithmeticTeichmullerSpaces/Prologue/Perfectoid/Data.lean` | bundled untilt/theta carrier with explicit law boundary |
| `JT-ATS-AUDIT-PERFECTOID` | `padicTwoPerfectoidData`, bundled law model, zero bundled countermodel and audit theorems | `ArithmeticTeichmullerSpaces/Prologue/Audit/PerfectoidModels.lean` | compiled non-degenerate `ℤ_[2]` model and law-violation witnesses |
| `JT-ATS-II-TATE-PARAMETER` | `TateParameterData`, `TateParameterLaws` | `ArithmeticTeichmullerSpaces/Prologue/Theta/Tate.lean` | D-interface for the finite-place Tate parameter function, nonzero parameter, and `0 < |q| < 1`; II `th:tate-parameter-as-a-function`, lines 609-630; III `pr:admissible-lifts-tate-params`, lines 1530-1539 |
| `JT-ATS-AUDIT-TATE` | `auditTateData_laws`, `auditTateData_violation` | `ArithmeticTeichmullerSpaces/Prologue/Audit/TateModels.lean` | compiled `q = 2` model at the genuine `(2)` place and zero-parameter countermodel |
| `JT-ATS-II-THETA-PILOT-SCALING` | `ThetaPilotData.scalingIndex`, `ThetaPilotScalingLaws` | `ArithmeticTeichmullerSpaces/Prologue/Theta/Pilot.lean` and `Interfaces/Carriers.lean` | D-interface for nonzero theta-pilot values and `j^2` norm scaling; II `pr:lift-vals`, lines 820-836; `pr:teichmuller-lift-B`, lines 968-975; III `th:adelic-theta-link`, lines 1139-1166 |
| `JT-ATS-AUDIT-THETA-PILOT` | `auditScalingTheta_laws`, `zeroScalingTheta_violates_laws` | `ArithmeticTeichmullerSpaces/Prologue/Audit/PilotModels.lean` | compiled two-index scaling model with exponents `1, 2` and norms `1/2, 1/16`, plus zero-value countermodel |
| `JT-ATS-III-THETA-SCALING-LINK` | `AdelicThetaLinkData.thetaBase`, `AdelicThetaLink.theta_scaling` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Carriers.lean`, `Interfaces/Contracts.lean` | D-integration of III `th:adelic-theta-link`, lines 1139-1166, with the sourced theta-pilot `j^2` law |
| `JT-ATS-III-DATA-001` | `ThetaPilotData`, `PacketHullData`, `AdelicThetaLinkData` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Carriers.lean` | D-composition of II `pr:lift-vals`, lines 820-836; II `pr:teichmuller-lift-B`, lines 968-975; III `th:adelic-theta-link`, lines 1139-1166; type-checked data layer |
| `JT-ATS-III-ARITHMETIC-LINK` | `AdelicThetaLinkData.heightData`, `AdelicThetaLinkData.ramification`, `AdelicThetaLinkData.qNorm`, `AdelicThetaLinkData.height` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Carriers.lean` | D-integration of II.5/IV arithmetic profiles; norm and height are sourced projections, not free functions |
| `JT-ATS-III-Q-PARAMETER-LOCAL` | `AdelicThetaLinkData.qParameter`, `FirstAxiom.q_parameter_nonzero`, `AdelicThetaLink.valuation_scaling` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Carriers.lean`, `Prologue/Interfaces/Contracts.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `pr:admissible-lifts-tate-params` lines 1530-1539 and `th:adelic-theta-link` lines 1139-1166; local `q_w` function over finite places, correcting the earlier global-parameter carrier |
| `JT-ATS-III-PERFECTOID-BRIDGE` | `PerfectoidPlaceData`, `PerfectoidPlaceLaws`, `PerfectoidBridgeData`, `PerfectoidBridgeLaws` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/PerfectoidBridge.lean` | D-interface making the number-field place, local `O`, prime `p`, coefficient map and Perfectoid laws explicit |
| `JT-ATS-III-PROLOGUE-INPUT` | `PrologueInputData`, `PrologueInputLaws` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Input.lean` | explicit bundle joining adelic link data and one Perfectoid bridge; common input laws remain separate from downstream volume contracts |
| `JT-ATS-III-CONTRACT-001` | `FirstAxiom` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Contracts.lean` | conditional proposition interface |
| `JT-ATS-III-CONTRACT-002` | `AdelicThetaLink` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Contracts.lean` | conditional proposition interface including explicit theta-pilot scaling, period mapping, and normalization; no independent Frobenius norm-square law |
| `JT-ATS-III-CONTRACT-003` | `ThetaLiftLog` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Contracts.lean` | conditional proposition interface |
| `JT-ATS-III-CONTRACT-004` | `PacketCollationHull` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Contracts.lean` | conditional proposition interface |
| `JT-ATS-III-CONTRACT-005` | `VolumeTransfer` | `ArithmeticTeichmullerSpaces/Prologue/Interfaces/Contracts.lean` | conditional proposition interface |
| `JT-ATS-AUDIT-MODEL-001` | `rationalTwoPlace`, `auditData` | `ArithmeticTeichmullerSpaces/Prologue/Audit/Models.lean` | compiled non-degenerate model data |
| `JT-ATS-AUDIT-MODEL-002` | satisfying and violating model theorems | `ArithmeticTeichmullerSpaces/Prologue/Audit/Models.lean` | compiled audit witnesses |
| `JT-ATS-AUDIT-ARITH-001` | `auditHeight`, `auditConductor`, `auditRamificationProfile` | `ArithmeticTeichmullerSpaces/Prologue/Audit/Models.lean` | compiled arithmetic model data and positivity witnesses |
| `JT-ATS-AUDIT-PERFECTOID-BRIDGE` | `padicTwoPlaceData`, `padicTwoBridgeData`, `padicTwo_bridge_model`, `zero_bridge_violates_laws` | `ArithmeticTeichmullerSpaces/Prologue/Audit/PerfectoidBridgeModels.lean` | compiled `(2)`-place/`ℤ_[2]` bridge model and bundled-law violation witness |
| `JT-ATS-AUDIT-PROLOGUE-INPUT` | `padicTwoInputData`, `padicTwo_input_laws`, `badInputData`, `badInput_violates_laws` | `ArithmeticTeichmullerSpaces/Prologue/Audit/InputModels.lean` | compiled common-law input bundle and nonzero-parameter violation witness |
| `JT-ATS-AUDIT-IMPORT` | public Prologue import audit and declaration checks | `ArithmeticTeichmullerSpaces/Prologue/Audit/ImportAudit.lean` | D-audit entry point; imports public Prologue modules and checks carriers, contracts, and model witnesses; excludes `Obligations` |
| `JT-ATS-V1-SCENE1-BOUNDARY` | `Act1Scene1.Scene1Input`, `Scene1Input.ofExplicit` | `ArithmeticTeichmullerSpaces/Act1Scene1/Boundary.lean` | D-boundary declaration; all Prologue data and contracts remain explicit parameters; no Corollary 3.12 statement or proof |
| `JT-ATS-III-COR312-TARGET` | `Act1Scene1.Corollary312Data`, `Corollary312`, `Corollary312SideConditions` | `ArithmeticTeichmullerSpaces/Act1Scene1/Corollary312.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `th:moccor-Mochizuki-form2` lines 3617-3632 and `cor:cor312` lines 3647-3650; exact inequality shape with explicit Scene1 realization slots; target specification, not a proof |
| `JT-ATS-III-SCENE1-VOLUME-BRIDGE` | `Corollary312VolumeData`, `Corollary312VolumeBound`, `corollary312_of_volume_lower_bound` | `ArithmeticTeichmullerSpaces/Act1Scene1/VolumeBridge.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `th:moccor-Mochizuki-form2` lines 3617-3632 and `cor:cor312` lines 3647-3650; complete logarithmic bridge from an explicit multiplicative theta-volume lower bound to the target inequality; the lower bound remains an explicit Scene1 input |
| `JT-ATS-III-SCENE1-Q-FAMILY` | `Corollary312SourceQIndex`, `Corollary312SourceQFactor`, `Corollary312QFamily`, `volumeBound_of_qFamily`, `corollary312_of_q_family_lower_bound` | `ArithmeticTeichmullerSpaces/Act1Scene1/QFamilyBridge.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `th:moccor-Mochizuki-form2` lines 3617-3632 and `cor:cor312` lines 3647-3650; explicit finite-place index equivalence and `qNorm^(1/(2*ell))` normalization, with the paper's `(p,w)` grouping left as a Scene1 identification obligation |
| `JT-ATS-III-SCENE1-QNORM-TATE` | `QNormTateCompatibility`, `qNorm_pos_lt_one_of_tate`, `Corollary312QFamily.ofTateCompatibility` | `ArithmeticTeichmullerSpaces/Act1Scene1/QNormTateBridge.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 2.md`, `th:tate-parameter-as-a-function` lines 609-630; supplementary `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `pr:admissible-lifts-tate-params` lines 1530-1539; explicit q-norm/Tate compatibility, with strict q-norm range derived from `TateParameterLaws` |
| `JT-ATS-III-SCENE1-VOLUME-NORMALIZATION` | `Corollary312VolumeNormalization`, `logVolume_nonneg_of_scene1`, `thetaVolume_pos_of_normalization`, `thetaVolume_le_one_of_normalization`, `corollary312_of_q_family_normalized_lower_bound` | `ArithmeticTeichmullerSpaces/Act1Scene1/VolumeNormalizationBridge.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `le:volume-lemma3` lines 3576-3583, `th:moccor-Mochizuki-form2` lines 3617-3632 and `cor:cor312` lines 3647-3650; local exponential sign normalization and nonnegativity transfer from explicit `VolumeTransfer` |
| `JT-ATS-III-SCENE1-TRANSFER-Q-LOWER` | `Corollary312TransferLogBound`, `logVolume_upper_bound_of_transfer_log_bound`, `thetaVolume_lower_bound_of_transfer_log_bound`, `corollary312_of_transfer_log_bound` | `ArithmeticTeichmullerSpaces/Act1Scene1/TransferQLowerBound.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `le:volume-lemma3` lines 3576-3583, `th:moccor-Mochizuki-form2` lines 3617-3632 and `cor:cor312` lines 3647-3650; complete finite-sum-to-product bridge, with the packet/hull log estimate explicit in Scene1 |
| `JT-ATS-III-SCENE1-TRANSFER-Q-ACCOUNTING` | `Corollary312TransferQAccounting`, `transferLogBound_of_qAccounting`, `corollary312_of_transfer_q_accounting` | `ArithmeticTeichmullerSpaces/Act1Scene1/TransferQAccounting.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `pr:general-cohomology-set-const` lines 3261-3271, `th:thetam-construction` lines 3296-3346, `le:volume-lemma3` lines 3576-3583 and `cor:cor312` lines 3647-3650; componentwise packet/hull-to-q accounting with explicit maps and finite conservation equality |
| `JT-ATS-III-SCENE1-ADELIC-THETA-BRIDGE` | `Corollary312Scene1Data`, `cor312_of_adelicThetaLink` | `ArithmeticTeichmullerSpaces/Act1Scene1/AdelicThetaLinkBridge.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `th:adelic-theta-link` lines 1139-1166, `pr:general-cohomology-set-const` lines 3261-3271, `th:thetam-construction` lines 3296-3346, `le:volume-lemma3` lines 3576-3583 and `cor:cor312` lines 3647-3650; explicit Scene1 assembly, with source construction outputs kept as separate inputs |
| `JT-ATS-V1-SCENE2-BOUNDARY` | `Act1Scene2.Scene2Input` | `ArithmeticTeichmullerSpaces/Act1Scene2/Boundary.lean` | D-boundary declaration; post-3.12 propositions are explicit slots only; no bridge theorem or `abc` result |
| `JT-ATS-AUDIT-OBLIGATIONS` | `registeredSourceIds`, constructor declaration and axiom checks | `ArithmeticTeichmullerSpaces/Prologue/Obligations/Audit.lean` | D-audit entry point; checks all four named `sorry` constructors and exposes their expected `sorryAx` dependencies without importing them into public interfaces |
| `JT-ATS-AUDIT-FIELD-COVERAGE` | field-level projection checks | `ArithmeticTeichmullerSpaces/Prologue/Audit/FieldCoverage.lean` | D-audit entry point; every public carrier and contract projection is checked against the grouped source mapping below |
| `JT-ATS-AUDIT-MODEL-COVERAGE` | satisfying/violating model matrix and arithmetic model obligations | `ArithmeticTeichmullerSpaces/Prologue/Audit/ModelCoverage.lean` | D-audit entry point; checks ten compiled interface pairs and three explicit Type-level model obligations |
| `JT-ATS-CANDIDATE-FROBENIUS-SQUARE-NORM` | `Candidate.FrobeniusSquareNormLaw` | `ArithmeticTeichmullerSpaces/Prologue/Candidate/FrobeniusSquare.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `th:adelic-theta-link` 1139-1166; rejected stronger reinterpretation of the paper's `j^2` valuation scaling |
| `JT-ATS-AUDIT-REJECT-FROBENIUS-SQUARE` | theta norm collapse, zero log-volume consequence, and nonempty packet/hull contradiction under the rejected candidate | `ArithmeticTeichmullerSpaces/Prologue/Audit/JointConsistency.lean` | `mathlib` `Data/Fintype/Lattice.lean` (`Finite.exists_max`, `Finite.exists_min`); contract semantics from `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `th:adelic-theta-link` 1139-1166, `def:additive-theta-pilot-object` 1492-1502, `le:volume-lemma3` 3576-3583, `cor:cor312` 3647-3650; rejection audit only |

### 字段级覆盖审计

`FieldCoverage.lean` 使用 Lean projection 名称逐项检查下列字段。每个字段组的语义
来源沿用对应的 declaration-level source-id；该表不把审计检查误记为数学证明。

| source-id | 字段组 | 文件 | 状态 |
| --- | --- | --- | --- |
| `JT-ATS-III-DATA-001` | `ThetaPilotData.index`, `indexFintype`, `value`, `norm`, `scalingIndex`, `frobenius`, `period`, `liftedLog`; `PacketHullData.packet`, `packetFintype`, `packetToPilot`, `packetWeight`, `hull`, `hullFintype`, `hullToPacket`, `hullWeight` | `Prologue/Interfaces/Carriers.lean` | projection audit passed |
| `JT-ATS-III-ARITHMETIC-LINK` | `AdelicThetaLinkData.places`, `qParameter`, `tate`, `theta`, `thetaBase`, `packetHull`, `heightData`, `ramification`, `logVolume`, `processionLength` | `Prologue/Interfaces/Carriers.lean` | projection audit passed |
| `JT-ATS-II5-ARITH-DIVISOR` | `FinitePlaceDivisor.support`, `exponent`, `exponent_ne_zero`; `HeightData.places`, `weight`, `weight_nonneg`, `value`, `value_eq` | `Prologue/Arithmetic/Basic.lean` | projection audit passed |
| `JT-ATS-IV-RAMIFICATION` | `RamificationProfile.conductor`, `different_log`, `conductor_log`, `different_log_nonneg`, `conductor_log_nonneg` | `Prologue/Arithmetic/Basic.lean` | projection audit passed |
| `JT-ATS-PROLOGUE-PERFECTOID` | `UntiltingLaws.one`, `reduction`, `frobenius_scaling`; `FontaineThetaLaws.teichmuller` | `Prologue/Perfectoid/Untilts.lean` | projection audit passed |
| `JT-ATS-PROLOGUE-PERFECTOID-DATA` | `PerfectoidData.untilt`, `theta`; `PerfectoidLaws.untilting`, `theta_compatibility` | `Prologue/Perfectoid/Data.lean` | projection audit passed |
| `JT-ATS-II-TATE-PARAMETER` | `TateParameterData.places`, `parameter`, `norm`; `TateParameterLaws.places_nonempty`, `parameter_nonzero`, `norm_eq`, `norm_pos`, `norm_lt_one` | `Prologue/Theta/Tate.lean` | projection audit passed |
| `JT-ATS-II-THETA-PILOT-SCALING` | `ThetaPilotScalingLaws.base_scalingIndex`, `value_nonzero`, `norm_positive`, `norm_scaling` | `Prologue/Theta/Pilot.lean` | projection audit passed |
| `JT-ATS-III-PERFECTOID-BRIDGE` | `PerfectoidPlaceData.place`, `data`; `PerfectoidPlaceLaws.perfectoid`; `PerfectoidBridgeData.coefficientMap`; `PerfectoidBridgeLaws.place_supported`, `local_laws` | `Prologue/Interfaces/PerfectoidBridge.lean` | projection audit passed |
| `JT-ATS-III-PROLOGUE-INPUT` | `PrologueInputData.link`, `placeData`, `bridge`; `PrologueInputLaws.first_axiom`, `tate_parameter`, `adelic_theta_link`, `perfectoid_bridge` | `Prologue/Interfaces/Input.lean` | projection audit passed |
| `JT-ATS-III-CONTRACT-001` | `FirstAxiom.places_nonempty`, `q_parameter_nonzero`, `q_norm_positive`, `height_nonnegative`, `theta_norm_positive`, `packet_weight_positive`, `hull_weight_positive` | `Prologue/Interfaces/Contracts.lean` | projection audit passed |
| `JT-ATS-III-CONTRACT-002` | `AdelicThetaLink.valuation_scaling`, `theta_scaling`, `period_map`, `normalization` | `Prologue/Interfaces/Contracts.lean` | projection audit passed; rejected candidate norm-square law is tracked separately |
| `JT-ATS-III-CONTRACT-003` | `ThetaLiftLog.log_shell`, `value_nonzero` | `Prologue/Interfaces/Contracts.lean` | projection audit passed |
| `JT-ATS-III-CONTRACT-004` | `PacketCollationHull.packet_supported`, `hull_supported`, `packet_weights_nonzero`, `hull_weights_nonzero` | `Prologue/Interfaces/Contracts.lean` | projection audit passed |
| `JT-ATS-III-CONTRACT-005` | `VolumeTransfer.transferred_volume` | `Prologue/Interfaces/Contracts.lean` | projection audit passed |

### 模型覆盖矩阵

`ModelCoverage.lean` 检查下列满足/违反 witness。`FinitePlaceDivisor`、`HeightData` 和
`RamificationProfile` 将不变量直接放在 Type 的构造字段中，因此登记为明确的模型义务，
不伪造一个不能 inhabit 这些字段的反模型。

| 接口 | 满足模型 | 违反模型 | 状态 |
| --- | --- | --- | --- |
| `FirstAxiom` | `firstAxiom_model` | `firstAxiom_violation` | compiled pair |
| `AdelicThetaLink` | `adelicThetaLink_model` | `adelicThetaLink_violation` | compiled pair |
| `ThetaLiftLog` | `thetaLiftLog_model` | `thetaLiftLog_violation` | compiled pair |
| `PacketCollationHull` | `packetCollationHull_model` | `packetCollationHull_violation` | compiled pair |
| `VolumeTransfer` | `volumeTransfer_model` | `volumeTransfer_violation` | compiled pair |
| `TateParameterLaws` | `auditTateData_laws` | `auditTateData_violation` | compiled pair |
| `ThetaPilotScalingLaws` | `auditScalingTheta_laws` | `zeroScalingTheta_violates_laws` | compiled pair |
| `PerfectoidLaws` | `padicTwo_perfectoid_model` | `zeroPerfectoidData_violates_laws` | compiled pair |
| `PerfectoidBridgeLaws` | `padicTwo_bridge_model` | `zero_bridge_violates_laws` | compiled pair |
| `PrologueInputLaws` | `padicTwo_input_laws` | `badInput_violates_laws` | compiled pair |
| Type-level arithmetic profiles | `auditHeight`, `auditConductor`, `auditRamificationProfile` | constructor obligations | explicit model obligation |

The Prologue boundary does not declare Corollary 3.12.  Its four construction theorems
are kept in `Prologue/Obligations` and are not imported by `Prologue/Interfaces`.

## IUT reference boundary

The reference checkout is `refer/iut` at commit `d9465c111ec4073709f67e9fccec7e3eb374a816`.
No IUT file is copied into the current tree and no Lean module imports `refer/iut`.
The checkout remains an API and statement reference only. Any future copied file must add
its source path, source commit, license, copyright notice, destination path and modification
summary before it is used.
