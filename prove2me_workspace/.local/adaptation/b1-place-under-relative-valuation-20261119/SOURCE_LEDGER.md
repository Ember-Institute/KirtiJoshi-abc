# 下方有限处与相对赋值公式的来源对应

有限处 $w$ 的下方处由对应素理想收缩构造。相对赋值公式在 $w$ 位于 $v$ 上方的假设下，将 $k$ 中元素在 $v$ 处的乘法赋值取相对分歧指数次幂。有限高度换底用下方处确定纤维，再用赋值公式和剩余次数换算有限处绝对值。 [有限高度消费者](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodFiniteHeightExtension.lean:21) · [相对绝对值消费者](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRelativeAbsoluteValue.lean:17) · [完备化嵌入消费者](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutEmbedCompletion.lean:44)

## 手写声明

下表的源端声明位于 `Iut`，目标声明位于 `AbcAdaptation.Tripod`。八条目标命令与参考命令逐字一致。两个缩写命令各增加 `noncomputable`，定义右端相同。命令对应的文件摘要、行号、字节范围和完整文本均已保存。 [命令记录](command-spans.json) · [全部差异](command-differences.diff)

| 声明 | 参考声明 | 目标声明 | 源端实际表达式 |
| --- | --- | --- | --- |
| `primeUnder` | [PlaceUnder.lean](/home/admin-wsl/Coq/abc/refer/iut/Iut/Cor312/ThetaData/PlaceUnder.lean:31) | [Source_TripodPlaceUnder.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodPlaceUnder.lean:18) | 完整类型和定义值 |
| `placeUnder` | [PlaceUnder.lean](/home/admin-wsl/Coq/abc/refer/iut/Iut/Cor312/ThetaData/PlaceUnder.lean:39) | [Source_TripodPlaceUnder.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodPlaceUnder.lean:26) | 完整类型和定义值 |
| `placeUnder_maximalIdeal` | [PlaceUnder.lean](/home/admin-wsl/Coq/abc/refer/iut/Iut/Cor312/ThetaData/PlaceUnder.lean:42) | [Source_TripodPlaceUnder.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodPlaceUnder.lean:29) | 边界记录，待补导出 |
| `liesOver_placeUnder` | [PlaceUnder.lean](/home/admin-wsl/Coq/abc/refer/iut/Iut/Cor312/ThetaData/PlaceUnder.lean:49) | [Source_TripodPlaceUnder.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodPlaceUnder.lean:36) | 边界记录，待补导出 |
| `placeUnder_eq_of_liesOver_place` | [Height.lean](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/Height.lean:142) | [Source_TripodPlaceUnder.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodPlaceUnder.lean:40) | 完整类型和证明 |
| `relRamIdx` | [EmbedCompletion.lean](/home/admin-wsl/Coq/abc/refer/iut/Iut/Concrete/ThetaLocalConstruct/EmbedCompletion.lean:162) | [Source_TripodRelativeValuation.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRelativeValuation.lean:19) | 完整类型和定义值 |
| `relInertDeg` | [Ordp.lean](/home/admin-wsl/Coq/abc/refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean:189) | [Source_TripodRelativeValuation.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRelativeValuation.lean:23) | 完整类型和定义值 |
| `ramificationIdx'_ne_zero` | [ValuationTransfer.lean](/home/admin-wsl/Coq/abc/refer/iut/Iut/Cor312/ThetaData/ValuationTransfer.lean:66) | [Source_TripodRelativeValuation.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRelativeValuation.lean:31) | 完整类型和证明 |
| `valuation_algebraMap_eq_pow` | [ValuationTransfer.lean](/home/admin-wsl/Coq/abc/refer/iut/Iut/Cor312/ThetaData/ValuationTransfer.lean:72) | [Source_TripodRelativeValuation.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRelativeValuation.lean:37) | 完整类型和证明，重放证明增加指数换算 |
| `relRamIdx_ne_zero` | [Ordp.lean](/home/admin-wsl/Coq/abc/refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean:169) | [Source_TripodRelativeValuation.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRelativeValuation.lean:51) | 完整类型和证明 |

`primeUnder` 的源端完整类型有 `Field k`、`Field K`、`NumberField K` 和 `Algebra k K` 四个实例参数。三语读回按实际的量化范围写作任意域 $k$，其余九条均取数域 $k,K$。 [已有核表达式](source-facts-existing.jsonl) · [英文读回](readback.en.md) · [中文读回](readback.zh.md) · [日文读回](readback.ja.md)

## 生成声明和依赖

目标的 `Source_TripodPlaceUnder` 共有九个声明，包含上述五项、`primeUnder._proof_1` 至 `primeUnder._proof_3` 及 `placeUnder.eq_1`。前三个生成证明在源端闭包中有对应的边界记录。Lean 4.32 的既有来源清单记录了第四个生成等式。补导出将从实际重放环境读取四项的完整类型和证明。目标的 `Source_TripodRelativeValuation` 共有五个声明。 [边界记录](source-facts-boundaries.jsonl) · [Lean 4.32 来源清单](source-inventory-lean32.jsonl) · [补导出配置](source-export-config.json)

现有归档另保存 `Iut.FinitePlace.LiesOver` 的完整源端类型和值，其目标对应是 `AbcAdaptation.Reference.Iut.FinitePlace.LiesOver`。它的定义是下方素理想等于上方素理想的收缩。该对应作为两个模块的直接依赖单独核对。 [参考定义](/home/admin-wsl/Coq/abc/refer/iut/Iut/Cor312/ThetaData/Places.lean:52) · [目标定义](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Places.lean:67)

参考工程的固定来源提交记录为 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，原工具链为 Lean 4.32.0。源端实际表达式来自 Lean 4.35.0-rc3 重放。目标为 Lean 4.33.1。八条手写声明和一条有限处关系均从既有闭包逐行复制原始 JSON 字节，保留完整类型、定义值或证明、绑定信息、宇宙、直接引用及公理。每行的源端所有者与摘要记录在输入绑定中。 [输入与回执](input-bindings.json) · [已有核表达式](source-facts-existing.jsonl)

源端重放的 `valuation_algebraMap_eq_pow` 在原证明的最后一步前增加 `Ideal.ramificationIdx'_eq_ramificationIdx` 重写。重放库的 `valuation_liesOver` 使用 `P.ramificationIdx`，目标库使用 `p.ramificationIdx' P`。审查草稿以一条兼容定理证明源端签名，并核对它与完整源端类型定义等价。重放的完整根证明通过映射使用这一兼容定理。源端库定理、目标库定理及兼容定理的完整证据均纳入导出或审查输出。 [重放证明](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-source-replay-v104-20261117/source-project/B1SourceReplay.lean:363) · [目标库签名](/home/admin-wsl/Coq/mathlib4-0df444a/Mathlib/NumberTheory/RamificationInertia/Valuation.lean:57) · [审查草稿](AuditPlaceUnderRelativeValuationCorrespondence.lean:13)

## 既有验收

- 源端闭包任务 `ci-018560-1db29f6e` 成功，退出码为 0。墙钟 162.14 秒，CPU 161.93 秒（用户态 15.17 秒，系统态 146.76 秒），进程树峰值 RSS 8.30 GiB。 [源端回执](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/main-chain-open-20261116/b1-source-actual-closure-v112-result.json)
- 下方处叶任务 `ci-019588-7aa6d194` 和产物任务 `ci-019594-8287c320` 成功。相对赋值的初次叶任务 `ci-019590-01d28061` 退出码为 1，诊断指出两个缩写依赖了不可计算定义。加上 `noncomputable` 后，叶任务 `ci-019591-c3dfcd9f` 和产物任务 `ci-019596-8784af6c` 成功。 [输入与回执](input-bindings.json) · [首次失败回执](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/main-chain-open-20261116/b1-height-extension-relativevaluation-leaf-v254-result.json)
- `ci-019597-37260aa0` 通过 Checks、ImportAudit、Act1Scene1 和 AxiomAudit。两模块的十四项声明均只有 `propext`、`Classical.choice`、`Quot.sound`。现有两模块和有限处关系模块的源码及产物摘要与该回执匹配。墙钟 315.29 秒，CPU 314.27 秒（用户态 226.60 秒，系统态 87.67 秒），进程树峰值 RSS 8.54 GiB。 [目标审查回执](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/main-chain-open-20261116/b1-height-extension-base-review-v255-result.json) · [输入与回执](input-bindings.json)

## 审查交接

1. 由主智能体将草稿整合到实际工作区。移动目录后更新两份配置中的绝对路径。
2. 在已验收的源端重放环境中通过 MCP-CI 提交 `ExportPlaceUnderRelativeValuationFacts.lean`。设置 `B1_PLACE_UNDER_RELATIVE_VALUATION_SOURCE_CONFIG` 为 `source-export-config.json` 的绝对路径。配置要求补导出两个手写定理、四个生成声明及源端库的赋值定理，共七项完整记录。 [补导出草稿](ExportPlaceUnderRelativeValuationFacts.lean) · [补导出配置](source-export-config.json) · [源端环境回执](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/main-chain-open-20261116/b1-source-actual-closure-v112-result.json)
3. 使用 `merge_source_facts.py` 合并源端原始记录，生成目标审查读取的 `source-facts.jsonl`。它核对声明与模块所有者，要求完整表达式及标准公理，并按审查配置确定记录次序。 [合并脚本](merge_source_facts.py)
4. 在目标 Lean 4.33.1 环境中设置 `B1_PLACE_UNDER_RELATIVE_VALUATION_REVIEW_CONFIG`，通过 MCP-CI 独占提交 `AuditPlaceUnderRelativeValuationCorrespondence.lean`。审查覆盖十四项模块声明和一项有限处关系，另输出库定理的兼容证据。审查逐项核对完整类型、绑定位置、两份完整值在目标类型下的合法性、值的定义等价及公理。对定理值的定义等价使用 Lean 证明无关性，原表达式和直接引用差异均保留。 [目标审查草稿](AuditPlaceUnderRelativeValuationCorrespondence.lean) · [目标审查配置](review-config.json)

## 本轮验收

- Lean 4.35.0-rc3 首次补导出 `ci-023682-ce131e1f` 在 180 秒达到调度时限。重试 `ci-023696-e7bf13a2` 导出七条完整声明，退出码 0。墙钟 282.60 秒，进程树峰值 RSS 8.14 GiB。[首次回执](round-ci-023682-ce131e1f-result.json) · [补导出回执](round-ci-023696-e7bf13a2-result.json) · [补导出数据](source-facts-supplement.jsonl)
- Lean 4.33.1 首次目标审查 `ci-023718-01e171f2` 缺少源版本的 `Int.instPartialOrder`。重试通过 `Int.instLinearOrder.toPartialOrder` 给出同一偏序实例。审查 `ci-023736-749237d6` 核对十四条目标模块声明、一条有限处关系和库兼容定理。保留完整类型与证明项，公理集合均属于 `propext`、`Classical.choice`、`Quot.sound`。退出码 0，墙钟 51.51 秒，CPU 51.78 秒（用户态 5.35 秒、系统态 46.43 秒），峰值 RSS 4.69 GiB。 [失败回执](round-ci-023718-01e171f2-result.json) · [通过回执](round-ci-023736-749237d6-result.json) · [对应结果](cross-version-result.json)
- 十条手写声明已完成英、中、日读回。私有平台验收仍待取得。 [英文](readback.en.md) · [中文](readback.zh.md) · [日文](readback.ja.md)
