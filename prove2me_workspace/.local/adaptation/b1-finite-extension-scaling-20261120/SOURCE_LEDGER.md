# 有限扩张缩放链的跨版本来源对应

B1 的有限高度采用有限处正对数的未除次数之和。相对分歧指数和剩余次数之积给出上方处的局部次数。对下方处的完整纤维求和，该相对次数之和等于数域扩张次数。由此，有限处正对数的求和在扩张 (K/k) 后整体乘以 ([K:k])。该主定理由三足点域的高度归一化消费。由于该高度随后按绝对次数归一化，换算时必须保留完整的扩张次数。 [适配计划](/home/admin-wsl/Coq/abc/docs/开发计划.Prove2Me适配.md:143) · [高度归一化](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_HeightNormalization.lean:29)

## 声明与来源

参考工程 `refer/iut` 固定来源为 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，许可证为 Apache 2.0。源端实际表达式由 Lean 4.35.0-rc3 重放模块 `B1SourceReplay` 导出。目标为 Lean 4.33.1 和 Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`。组内包含七条相对次数塔声明、两条纤维和、两条绝对值公式及一条有限高度公式，共十二条。上下方有限处和相对赋值在上一单元中对应。 [输入绑定](input-bindings.json) · [固定参考工程](https://github.com/lana-agents/iut/tree/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8)

| 声明 | 固定参考 | 目标 |
| --- | --- | --- |
| `under_int_eq_under_int` | [Ordp.lean](/home/admin-wsl/Coq/abc/refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean:156) | [Source_TripodRelativeDegreeTower.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRelativeDegreeTower.lean:22) |
| `residueChar_eq_of_liesOver` | [Ordp.lean](/home/admin-wsl/Coq/abc/refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean:162) | [Source_TripodRelativeDegreeTower.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRelativeDegreeTower.lean:28) |
| `ramIdx_eq_mul` | [Ordp.lean](/home/admin-wsl/Coq/abc/refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean:172) | [Source_TripodRelativeDegreeTower.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRelativeDegreeTower.lean:35) |
| `inertDeg_eq_mul` | [Ordp.lean](/home/admin-wsl/Coq/abc/refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean:193) | [Source_TripodRelativeDegreeTower.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRelativeDegreeTower.lean:52) |
| `localDeg_eq_mul` | [Ordp.lean](/home/admin-wsl/Coq/abc/refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean:214) | [Source_TripodRelativeDegreeTower.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRelativeDegreeTower.lean:73) |
| `relLocalDeg` | [Height.lean](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/Height.lean:151) | [Source_TripodRelativeDegreeTower.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRelativeDegreeTower.lean:81) |
| `relLocalDeg_ne_zero` | [Height.lean](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/Height.lean:154) | [Source_TripodRelativeDegreeTower.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRelativeDegreeTower.lean:84) |
| `sum_localDeg_liesOver` | [Ordp.lean](/home/admin-wsl/Coq/abc/refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean:245) | [Source_TripodRelativeDegreeSum.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRelativeDegreeSum.lean:18) |
| `sum_relLocalDeg_liesOver` | [Height.lean](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/Height.lean:188) | [Source_TripodRelativeDegreeSum.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRelativeDegreeSum.lean:51) |
| `apply_algebraMap_eq_pow` | [Height.lean](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/Height.lean:163) | [Source_TripodRelativeAbsoluteValue.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRelativeAbsoluteValue.lean:17) |
| `posLog_apply_algebraMap_eq` | [Height.lean](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/Height.lean:182) | [Source_TripodRelativeAbsoluteValue.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRelativeAbsoluteValue.lean:36) |
| `finHeight_algebraMap` | [Height.lean](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/Height.lean:201) | [Source_TripodFiniteHeightExtension.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodFiniteHeightExtension.lean:21) |

十条目标题令与参考一致。`apply_algebraMap_eq_pow` 只更换了对数公式的命名空间。`finHeight_algebraMap` 在源端重放中用有限支撑证据直接取得成员等价，在目标端先把两个有限支撑证据分别引入局部上下文。两端均保留完整纤维及全部求和步骤。 [命令及行号](command-spans.json) · [证明命令差异](command-differences.diff)

## 核表达式审查

十二条源端记录均保存完整类型、定义值或证明、内核推得的值类型、绑定信息、宇宙、直接依赖和公理，按原始 JSONL 字节导出。目标审查应逐条检查完整类型的定义等价、两份完整证明项或定义值的内核类型、值的定义等价和公理。定理值适用证明无关性。先检查原始源值在兼容转换后确实具有目标类型，随后比较两份值。 [源端表达式](source-facts.jsonl) · [审查配置](review-config.json) · [审查草稿](AuditFiniteExtensionScalingCorrespondence.lean)

首轮目标跨版本审查 `ci-023732-52a7841e` 核对了十二条完整类型和其中八条完整值。其余四条值存在可定位的库接口迁移。复验草稿在相同载体上使用目标端无挠性和域非平凡性证明，恢复相对整数环无挠性别名的两个 `NumberField` 绑定，并按目标端定理签名交换剩余次数比较所需的类型与实例参数。修复只用于重放来源值。 [主工作区首轮结果](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-finite-extension-scaling-20261120/cross-version-result.json) · [当前修复](AuditFiniteExtensionScalingCorrespondence.lean)

## 三语读回

[中文](readback.zh.md) · [English](readback.en.md) · [日本語](readback.ja.md)

## 回执

| 任务 | 状态 | 退出码 | 墙钟秒 | CPU 秒（用户态 + 系统态） | 进程树峰值 RSS GiB |
| --- | --- | --- | --- | --- | --- |
| [`ci-018560-1db29f6e`](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/main-chain-open-20261116/b1-source-actual-closure-v112-result.json) | succeeded | 0 | 162.14 | 161.93（15.17 + 146.76） | 8.30 |
| [`ci-019604-10666b16`](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/main-chain-open-20261116/b1-height-extension-relativedegreetower-leaf-v256-result.json) | succeeded | 0 | 38.20 | 38.47（3.37 + 35.10） | 4.06 |
| [`ci-019610-3ab8e620`](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/main-chain-open-20261116/b1-height-extension-relativedegreesum-leaf-v256-result.json) | succeeded | 0 | 39.52 | 39.15（2.45 + 36.70） | 4.04 |
| [`ci-019615-d3bb0b5f`](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/main-chain-open-20261116/b1-height-extension-relativeabsolutevalue-leaf-v256-result.json) | succeeded | 0 | 40.06 | 39.16（2.32 + 36.84） | 3.91 |
| [`ci-019620-8ba656ad`](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/main-chain-open-20261116/b1-height-extension-finiteheightextension-leaf-v256-result.json) | failed | 1 | 42.76 | 42.10（2.53 + 39.57） | 3.99 |
| [`ci-019622-5072e1c9`](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/main-chain-open-20261116/b1-height-extension-finiteheightextension-leaf-v257-result.json) | succeeded | 0 | 35.90 | 35.15（2.42 + 32.73） | 3.94 |
| [`ci-019627-402f9dc7`](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/main-chain-open-20261116/b1-height-extension-scaling-review-v257-result.json) | succeeded | 0 | 553.51 | 552.74（454.03 + 98.71） | 8.54 |
| [`ci-023732-52a7841e`](/tmp/abc-iut-continuation-023658/ci-023732-52a7841e.result.json) | failed | 1 | 70.15 | 69.74（8.34 + 61.40） | 4.77 |

`ci-019620-8ba656ad` 的 rewrite 无法在旧目标命令中以隐式化简透明度识别 `Function.HasFiniteSupport` 与有限支撑的化简。改为先引入精确类型的有限支撑证明后，复验 `ci-019622-5072e1c9` 通过。聚合审查 `ci-019627-402f9dc7` 验收目标模块的全部十二条声明，均仅依赖 `propext`、`Classical.choice`、`Quot.sound`。当前目标源码和产物摘要与该聚合回执一致。上表墙钟、CPU 与进程树 RSS 来自相应回执，保留回执的 PSS 与宿主监控状态字段。 [失败诊断](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/main-chain-open-20261116/b1-height-extension-finiteheightextension-leaf-v256-result.json) · [输入绑定](input-bindings.json)

## 本轮验收

`ci-023810-a4620839` 在主工作区独占模式下通过 12 条声明的完整类型、定义值或证明项及公理审查。重放 `ramIdx_eq_mul` 时，重定位从源端的 `CharZero` 投影取回原 `NumberField` 实例，保留域与域结构参数。编译退出码为 0，墙钟 69.72 秒，CPU 69.46 秒（用户态 8.03 秒，系统态 61.43 秒），进程树峰值 RSS 为 4.85 GiB，PSS 未取得。私有平台验收仍开放。 [终态回执](round-ci-023810-a4620839-result.json) · [内核结果](cross-version-result.json) · [完整表达式](cross-version-expressions.jsonl)
