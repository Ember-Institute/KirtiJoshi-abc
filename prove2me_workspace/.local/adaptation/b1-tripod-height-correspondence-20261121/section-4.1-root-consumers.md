# 参考主组合链的数学输入与消费者

参考链以 `Iut.Tripod.classicalABC_of_variant_genuine'` 为入口，固定 `iut` 提交 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`。目标链从 `abc.goal.lt_constant_mul_fix` 沿已验收归约向下追踪。下表保留参考证明实际调用的数学输入，并给出对应的本地声明、验收回执或开放节点。 [参考根][root-source] · [平台依赖登记][root-registry]

| 参考消费者 | 实际数学输入 | 目标端对应与证据 |
| --- | --- | --- |
| `classicalABC_of_variant_genuine'` → `classicalABC_of_variant_genuine` → `classicalABC_of_variant` | `canLift27` 构造具体 étale 与缓和基本群。`classicalABC_of_variant_of_statementII_imp_I` 把这两个理论和 `h312` 交给 `abc_of_variant`，再用 `statementI_of_statementII` 和 `classicalABC_of_statementI`。 [真实根][root-source] · [基本群实例][source-genuine] · [具体组合][source-classical-bridge] | 本地 `canLift27` 已审查，`canonicalCorollary22HighHeightEstimate_of_canLift27_genuineTempered` 实际以该证明构造两种理论并调用规范 P7。该入口显式保留 `CurveProviders` 和同一 P7 族上的 `h312`。 [CanLift 与具体理论][arithmetic-ledger] · [本地入口][genuine-c2] |
| `classicalABCInt_of_statementI` → `classicalABC_of_int` | 将整数三元组送入有理点 `ratPt`。用次数为一、归一化不同理想为零、典范高度比较和根基导子界，将 `StatementI` 改写为整数 abc，再转到自然数。 [有理点应用][source-rational] · [自然数转换][source-classical] | 已验收的主路径为修正根 → `AbcAdaptation.classical` → `AbcAdaptation.classicalInt` → `AbcAdaptation.rationalHeight`。后者实际有 `StatementII`、`statementI_of_statementII` 和四个有理点投影子边。严格不等式和自然数根基转换已在修正根的归约中处理。 [修正根组合](../../../Solutions/Sol_abc_goal_lt_constant_mul_fix.lean) · [根图][root-registry] |
| `statementI_of_statementII` | `curves_statementII_of_statementII` 使用点域、次数、典范高度、不同理想、导子、紧致有界成员资格的转运。`Genl.Curves.statementII_implies_statementI` 通过证明包选择 `nonempty_covering` 和 `nonempty_belyiDescent`，再经 `statementI_of_curves_statementI` 回到三足点。 [参考转运][source-general-position] · [Genl 证明包][source-genl-package] | `statementI_of_statementII` 的 Fermat 归约已验收，由 `Fermat.heightNormalization`、`Fermat.liftDifferent` 和 `Fermat.canonicalEstimate` 三项供给。后者的二十项实际子边包含非临界 Belyi、尖点导子、紧致性、伴随与典范高度。通用来源的位置和本地特化见候选桥梁表。 [Fermat 组合回执][fermat-group] · [Fermat 几何归约][fermat-geometry] |
| `abc_of_variant` → `statementII_of_cor312` → `Corollary22Inputs.c2` | `abc_of_variant` 实际提交 `I`、`ex`、`cheb`、`pnt`、全称 `h312` 五项。`statementII_of_cor312` 以 `excCore_finite` 和 `northcott` 处理有限例外，应用 `c2` 与误差界，再以 `htCan_equiv` 换回典范高度。 [参考组合][source-main] · [Corollary 2.3][source-c23] | 平台 `statementII` 归约消费 `boundedDegreeFiniteness` 与 `highHeightEstimate`。`highHeightEstimate` 归约消费 `canonicalLegendreHeightComparison`、`canonicalCorollary22HighHeightEstimate` 和 `epsilonELargeHeight`，其中第 2 项开放。本地 `statementII_of_explicitPrimeEstimates_on_sourceP7` 以同一个曲线提供器接上这条归约。切比雪夫界与素数计数证书已有提供者。 [根图][root-registry] · [同一 P7 的陈述二][target-statementii] · [素数估计][prime-estimates] |
| `tripodTheory : Genl.HeightTheory` | `statementII_of_cor312` 实际在这一高度理论上量化三足点、`ptLE` 与 `cbsSet`，并消费其中的 `htCan`、`logDiff` 和 `logCond`。`statementII_iff`、`statementI_iff` 展开两个三足命题。一般曲线证明用另一实例 `Genl.Curves.theory`，两边由上面的转运连接。 [高度理论来源][source-height-theory] | 本地保留同一高度理论的 15 个字段。参考高度理论与两个陈述的类型和转运证据已归档，固定 Fermat 组合直接消费本地的 `StatementII` 和 `StatementI`。 [目标高度理论][target-height-theory] · [组合输入][fermat-group] |
| `curveInputs` → `CurveInputs.toCorollary22Inputs` | 锁定同一 `curveOf x` 的数据域、Tate 参数和模 ℓ 表示。原构造调用包括 `tripodProviders`、循环子群界 `CF`、核心例外集有限性、Northcott、3 与 5 挠点次数界、Legendre 高度、二进高度及两条导子比较。21 个字段中，模域次数、不同理想和两条导子比较经 P7 消费，局部高度、次数界、循环子群和 SL₂ 像等经 `c2` 消费。 [参考构造器][source-curve-inputs] · [目标转发定义][target-c22-fields] | 已私有发布构造器，21 个赋值已和从参考编译产物导出的声明比较，逐字段消费者已登记。本地 `curveInputs_from_source` 使用现有 `sl2Image_from_source`、两项挠点次数界和两条导子定理，显式接收同一 `P` 上的高度及曲线输入。 [实际构造][target-curve-inputs] · [21 个字段的来源、回执和消费者][curve-input-fields] |
| `tripodProviders` 与 `coreFiniteness`、`anabelianExistence` | `tripodProviders` 以挠点有限性、挠点基、`sqrt_neg_one`、`stable_reduction`、`six_torsion_rational`、`galois_deg_prime` 装入供应器。几何侧固定同一 `Pi1`、`Tp`，为局部数据的曲线供给核心有限性、轨形覆盖和相容的远 Abel／缓和理论。 [曲线供应器][source-providers] · [源 P7][source-p7] | 本地 `tripodProviders` 用 `CurveArithmetic.ofCore` 供应实际 `curveOf` 的逐点曲线算术，并用 `CurveProviders.ofArithmetic` 供应挠点有限性与模 ℓ 表示。CanLift、具体 étale 与缓和理论已用于规范入口的核心有限性和远 Abel 存在性。 [目标供应器][target-provider] · [几何组合][genuine-c2] |
| `concreteThetaDataExistence'` → `ConcreteThetaDataExistence.toThetaDataExistence` | 在同一点、同一素数上把 (P2)、(P3)、(P5)、(P6) 接入 `thetaData`、`qPilotInputs`、`concreteLocalTheory` 和 `thetaLocalData`。`towerArithmetic_of_towerLocalHyp` 实际消费同一塔的局部事实、三足域分歧界、挠点次数界及有理 2 挠点。输出同一个 `X` 的素数、`dmod` 界、q-pilot 高度、不同理想等式和两条导子比较，以及证书和 `Nonempty inv.LocalEstimate`。 [逐点构造][source-p7] · [塔算术][source-tower] · [P7 转换][source-p7-conversion] | 既有本地塔构造在同一模 ℓ 表示上供给野分歧界、好处非分歧和 `30ℓ` 界，逐点 P7 组合已实际消费塔算术。代表处与 q-pilot 归一化从同一数据读取。带素数下界的入口复用原见证并接收论文右端。 [局部塔账本][tower-local] · [逐点 P7 账本][p7-local] · [论文右端接合][paper-c22] |
| `c2` → `theorem110` → `LocalEstimate.rhs_le` | `c2` 在选定的 `X` 上调用 `inv.theorem110 cert est pnt (h312 X hPX)`。`rhs_le` 使用同一 `X` 的包络、θ 区域、逐包测度单调性、有限处与无穷处体积界，合计成 `X.rhsData.rhs` 的上界。 [c2 调用][source-c2] · [定理 1.10][source-110] · [局部体积求和][source-rhs-le] | 完整条件性 `rhs_le → theorem110 → c2` 已验收。旧具体主区域已有规范 P7 的严格反例。带论文右端的入口显式接收 `PaperRHSSupplyAtLeast`，以及对该族中满足素数下界的 `X` 成立的全称 `Corollary312Variant X`。 [条件组合的平台回执][c22-platform] · [反例][p7-counterexample] · [现行接口][paper-c22] |

当前开放义务如下，节点名可在根图或已有构造器中直接查到。 [平台依赖登记][root-registry]

- `AbcAdaptation.rationalHeight` 的四个投影子项为 `degreeOneProjection`、`heightComparisonProjection`、`logDifferentZeroProjection`、`radicalConductorProjection`。它们分别对应参考 `ratPt` 的次数、典范高度、不同理想和根基导子比较，均为现有平台开放叶。 [有理点证明][source-rational] · [投影根图][root-registry]
- `AbcAdaptation.Tripod.statementI_of_statementII` 继续沿已验收的 Fermat 归约。`Fermat.heightNormalization` 与 `Fermat.liftDifferent` 分别保留固定 Fermat 高度比较以及实际提升点域、`N²` 次数和归一化判别式界。`Fermat.canonicalEstimate` 的九个开放终端是 `affineIdentification`、`coordinatePoleMultiplicity_eq`、`canonicalHeightIdentification`、`cuspConductorHeightComparison`、`modelExists`、`noncriticalP1Minpoly`、`noncriticalP1Normalize`、`noncriticalP1RationalBranchSet`、`planeAdjunctionExists`。这九项使用登记中的既有路径，涵盖源证明的模型、几何、导子和非临界映射输入。 [Fermat 组合回执][fermat-group] · [几何子边][fermat-geometry] · [根图][root-registry]
- `AbcAdaptation.Tripod.canonicalCorollary22HighHeightEstimate` 的曲线侧需供应 `CurveProviders.ofArithmetic` 所接收的 `∀ x : Pt, (curveOf x (legendre_torsionFinite x.1 3 (by decide)) (legendre_torsionFinite x.1 5 (by decide))).CurveArithmetic`。同一 `F_λ` 上的 `stable_reduction_curveOf` 已覆盖所有有限处。`galois_deg_prime` 已证明对每个素数 `ℓ ≥ 7` 的 Galois 和次数互素条件。`CurveArithmetic.ofCore` 的六项派生字段和逐点供应器已通过本地审查。规范高高度推论 2.2 已有实际消费 `tripodProviders` 的特化，继续接收同一 P7 族上的全称比较。曲线供应器的五条声明和 22 处字段已通过参考与目标的跨版本内核对照。曲线供应链的独立打包与私有平台验收仍开放。 [曲线供应器跨版本对照](curve-input-assembly/provider-reference/SOURCE_LEDGER.md) [目标字段][target-provider] · [源稳定约化][source-stable] · [稳定约化审查](stable-reduction/SOURCE_LEDGER.md) · [源 Galois 条件][source-galois] · [本地 Galois 证明、供应器与读回](curve-galois/SOURCE_LEDGER.md) · [规范高高度特化](../../../Solutions/Source_TripodCanonicalCorollary22WithProviders.lean#L12) · [曲线字段账本][curve-input-fields]
- 规范高高度目标的论文侧需为每个 `K,d` 给出统一素数下界，或者在对应素数窗中取得同一个满足论文条件的素数。对该素数上的 P7 见证，`PaperRHSSupplyAtLeast` 负责论文 θ 区域、测度及 `LocalEstimate`，并保留原 q-pilot、次数、不同理想和导子关系。同一新右端还需 `∀ K d X, Paper K d X → minimum K d ≤ X.ℓ → Corollary312Variant X`，其中 q 项依照 Joshi 比较核对符号、代表处及权重。两项仍在同一现有开放高高度节点下。 [精确供应及比较类型][paper-c22] · [论文与素数下界账本][paper-ledger]

覆盖核对逐项检查了 `Main.lean:136` 的五个实参及 `CurveFacts.lean:492` 的完整构造输入，以及 `CurveInputs.toCorollary22Inputs` 的 16 个字段、P7 见证的各分量和 `theorem110` 实际接收的 `cert`、`est`、`pnt`、`h312`。从登记的 `abc.goal.lt_constant_mul_fix` 沿 `edges` 中 `SKETCH_ACCEPTED` 的 `children` 追踪，以 `platform_statuses` 对照终端。读取的登记 SHA-256 为 `0f10e1e0160bd2e12829fb3258edc3144e66794327e38b1e32e6478c9943f2ca`，共有 50 个可达节点和 38 个终端，22 个终端为 `Proved`，16 个为 `Open`。16 个开放终端由四个有理点投影、十一个 Fermat 终端和一个规范高高度终端组成。 其中有理点的次数一和归一化对数判别式为零已有本地解答，通过项目和公理审查，两个节点在平台登记中仍为 `Open`。 [本地证明、读回与回执](rational-degree-one/SOURCE_LEDGER.md)曲线供应和论文比较是该高高度目标的源式证明所保留的输入。 [参考组合][source-main] · [字段及消费者账本][curve-input-fields] · [P7 转换][source-p7-conversion] · [平台依赖登记][root-registry]

[root-source]: https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/ClassicalAbcGenuineCanLift.lean#L40
[source-genuine]: https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/ClassicalAbcGenuine.lean#L29
[source-classical-bridge]: https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/ClassicalAbc.lean#L307
[source-rational]: https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/ClassicalAbc.lean#L227
[source-classical]: https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Abc/Classical.lean#L51
[source-general-position]: https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/GeneralPosition.lean#L269
[source-genl-package]: https://github.com/lana-agents/genl/blob/ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf/Genl/Curves/ProofPackage.lean#L28
[source-main]: https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/Main.lean#L129
[source-c23]: https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Implication/Corollary23.lean#L56
[source-curve-inputs]: https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/CurveFacts.lean#L492
[source-providers]: https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/Providers.lean#L33
[source-p7]: https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/Main.lean#L86
[source-tower]: https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/Tower.lean#L87
[source-p7-conversion]: https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Concrete/Main.lean#L68
[source-c2]: https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Implication/Corollary22.lean#L528
[source-110]: https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Implication/Theorem110.lean#L234
[source-rhs-le]: https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Implication/LogVolumeBound.lean#L205
[source-stable]: https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/StableTwo.lean#L704
[source-galois]: https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/Galois.lean#L606
[root-registry]: ../platform-node-registry.json
[genuine-c2]: ../../../Solutions/Source_TripodCanonicalCorollary22FromGenuineTempered.lean#L17
[target-statementii]: ../../../Solutions/Source_TripodStatementIIOnSourceP7.lean#L17
[source-height-theory]: https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/Basic.lean#L332
[target-height-theory]: ../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_Theory.lean#L21
[target-c22-fields]: ../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean#L142
[target-curve-inputs]: ../../../Solutions/Source_TripodCurveInputsFromSource.lean#L40
[target-provider]: ../../../Solutions/Source_TripodProviderRepresentation.lean#L47
[arithmetic-ledger]: ../b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#squared-trace-integrality-and-canlift-proposition-27
[prime-estimates]: ../b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#explicit-prime-estimates-for-corollary-22
[tower-local]: ../b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#local-facts-on-the-actual-legendre-tower
[p7-local]: ../b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#pointwise-p7-with-tower-arithmetic-from-the-legendre-curve
[p7-counterexample]: ../b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#counterexample-to-the-concrete-source-p7-volume-comparison
[paper-c22]: c2-prime-bound/Source_TripodCanonicalCorollary22PaperRHS.lean#L66
[paper-ledger]: SOURCE_LEDGER.md#论文右端接入同一-p7
[curve-input-fields]: curve-input-assembly/curve-inputs-dependencies.md
[c22-platform]: ../rhs-le-full-proof-v59-20261116/delivery-summary-v63.json
[fermat-group]: ../fermat-general-position-20261113/source-consumer.json
[fermat-geometry]: ../fermat-proper-canonical-20261113/integration.json
