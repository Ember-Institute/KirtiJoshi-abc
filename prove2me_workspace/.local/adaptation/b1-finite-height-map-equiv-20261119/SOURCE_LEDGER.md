# 数域同构下有限高度不变性的来源与验收

`AbcAdaptation.Tripod.finHeight_mapEquiv` 对两个数域、一个域同构 $e\colon T\simeq T'$ 和任意 $y\in T$ 证明 $h_{\mathrm{fin},T'}(e(y))=h_{\mathrm{fin},T}(y)$。`FinitePlace.mapEquiv` 给出有限处双射，对应的绝对值满足 $|x|_{e_*v}=|e^{-1}(x)|_v$。按这个双射重排正部对数的和即得到不变性。 [主声明](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FiniteHeightMapEquiv.lean:131) · [有限高度定义](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_TripodCanonicalHighHeightInputs.lean:19)

## 定位与消费者

| 参考工程 | 目标中的使用 |
| --- | --- |
| `finHeight_mapEquiv` | `h_eq_finHeight_div` 沿三足域与点域之间的同构比较 $j$ 不变量的有限高度。 [来源](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/Height.lean:110) · [消费者](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_HeightNormalization.lean:28) |
| `FinitePlace.mapEquiv` 与 `FinitePlace.mapEquiv_apply` | 主定理用双射重排求和，用逐处等式核对求和项。`tpdPlace` 使用同一双射，`tpdPlace_gen` 和 `tpdPlace_gen_sub_one` 使用逐处等式。 [来源](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/TwoAdic.lean:50) · [三足处传输](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_TripodalPlaceTransport.lean:30) |
| `FinitePlace.mapEquiv_maximalIdeal`、`FinitePlace.mapEquiv_valuation` 与 `FinitePlace.mapEquiv_absNorm` | 极大理想的逆像描述用于比较赋值、理想绝对范数和剩余标数。逐处绝对值等式使用赋值及绝对范数等式。 [来源](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/TwoAdic.lean:57) · [范数与绝对值](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FiniteHeightMapEquiv.lean:91) · [剩余标数](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FinitePlaceResidueTransport.lean:31) |
| `mem_comap_pow_iff`、`intValuation_of_comap` 与 `valuation_of_comap` | 先用理想幂的成员关系核对环上的赋值，再传到分式域。有限处传输把分式域公式用于两数域的整数环。 [来源](/home/admin-wsl/Coq/abc/refer/iut/Iut/Cor312/ThetaData/GalCompletion.lean:180) · [消费者](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FiniteHeightMapEquiv.lean:94) |
| `toNNReal_congr` | 给定同一个离散赋值和相等的非零底数，证明得到的非负实数相同。逐处绝对值等式使用这条引理。 [来源](/home/admin-wsl/Coq/abc/refer/iut/Iut/Cor312/ThetaData/GalCompletion.lean:331) · [消费者](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FiniteHeightMapEquiv.lean:117) |

10 条手写声明的完整命令在参考提交、源端重放和目标文件中逐字一致。参考提交为 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，原工具链为 Lean 4.32.0。导出的源端表达式采用 Lean 4.35.0-rc3 和 Mathlib `389347a7c1cfa76f6bd5be2ca35d4cb621610ad3`。目标采用 Lean 4.33.1 和 Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`。文件摘要、命令范围和依赖锁见绑定记录。 [输入与回执](input-bindings.json)

## 已有验收

| MCP-CI 任务 | 墙钟秒 | CPU 总秒（用户态 + 系统态） | 峰值 RSS GiB |
| --- | ---: | ---: | ---: |
| 源端表达式导出 `ci-018560-1db29f6e` | 162.14 | 161.93（15.17 + 146.76） | 8.296 |
| 目标叶检查 `ci-019580-7e1afb67` | 38.52 | 38.10（2.70 + 35.40） | 4.035 |
| 目标 `.olean` 产物 `ci-019581-466eeaf8` | 38.07 | 37.14（2.39 + 34.75） | 3.932 |
| 聚合与公理审查 `ci-019582-8d08ff0e` | 209.94 | 209.09（118.00 + 91.09） | 8.535 |

四项任务均以退出码 0 结束。表内资源来自回执的 `result.resources`。峰值 PSS 和 `degraded` 均未记录。项目审查通过 Checks、ImportAudit、Act1Scene1 和 AxiomAudit。目标模块名下的 14 条声明都只使用 Lean 标准公理，主定理使用 `propext`、`Classical.choice` 与 `Quot.sound`。 [源端表达式回执](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/main-chain-open-20261116/b1-source-actual-closure-v112-result.json) · [目标聚合与公理回执](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/main-chain-open-20261116/b1-finite-height-map-equiv-review-v253-result.json)

## 跨版本审查

审查从完整表达式导出中读取 10 条手写声明及 `intValuation_of_comap` 引用的三条生成引理。将项目名称和依赖实例映射到已锁定的目标环境后，比较完整类型、绑定位置及值。两个证明项分别在目标内核中核对完整目标类型，再用证明无关性比较。`FinitePlace.mapEquiv` 的值按双射定义体核对。源端导出缺少 `Iut.FinitePlace.mapEquiv.eq_1`，该生成等式有目标端的公理审查回执。 [源端表达式子集](source-facts.jsonl) · [Lean 审查稿](AuditFiniteHeightMapEquivCorrespondence.lean) · [配置](review-config.json)

提交 `review/file` 时通过 `B1_FINITE_HEIGHT_MAP_EQUIV_REVIEW_CONFIG` 提供配置文件的绝对路径。配置中的 `sourceFactsFile`、`evidenceFile` 与 `resultFile` 使用实际工作区路径。

独占审查 `ci-023566-365b8789` 以退出码 0 完成。十三条声明的完整类型和值全部通过，公理均属于 Lean 标准公理。墙钟 263.30 秒，进程树峰值 RSS 4.74 GiB。源端未导出的 `Iut.FinitePlace.mapEquiv.eq_1` 仍由上文目标端审查覆盖。私有平台解答获 `ACCEPTED`，节点回读为 `Proved`。 [私有验收](../b1-height-platform-20261120/SOURCE_LEDGER.md#2026-11-21-有限高度解答验收) [审查回执](round-ci-023566-365b8789-result.json) · [完整表达式证据](cross-version-expressions.jsonl) · [审查结果](cross-version-result.json)

## 原文背景

望月新一在 IUT IV §2 推论 2.2(ii) 的证明中给出按剩余次数和剩余标数加权的高度和式。`finHeight_mapEquiv` 的直接出处为参考 Lean 工程。它供随后把曲线的高度公式写到三足点域。 [原文段落与页码](paper-context.json) · [参考高度归一化](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/Height.lean:603)

## 独立三语读回

主定理的独立英、中、日读回均与冻结的目标绑定。三语保留两个数域、域同构、任意元素、有限处绝对值的归一化及有限和的退化情形。英稿与两份译文均保留审读者的原文。 [读回与校对](independent-readback/README.md) · [原稿和输入摘要](independent-readback/provenance.json)
