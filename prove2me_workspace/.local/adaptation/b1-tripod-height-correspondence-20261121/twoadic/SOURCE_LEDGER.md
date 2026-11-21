# 二进处高度界与构造器字段

固定来源为 refer/iut 提交 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，许可证为 Apache 2.0。Lean 4.35.0-rc3 源端重放与 Lean 4.33.1 目标端比较核对六项的完整类型和证明。目标审查从 `curveInputsOfSL2Image` 提取 `B_nonneg` 与 `heightEq_two_le` 的实际赋值，验证它们随同一供应曲线传入 `toCorollary22Inputs`。两个字段使用同一常数 `max (4 * K.c) 0`，局部高度按实际曲线域归一化。 [来源定理](../../../../../refer/iut/Iut/Tripod/TwoAdic.lean#L595) · [构造器](../../../../Solutions/Source_TripodCurveInputs.lean#L44) · [对应结果](cross-version-result.json) · [主定理三语读回](../../b1-twoadic-bound-v264/readbacks/two-adic-bound.md) · [字段和消费者三语读回](../../b1-twoadic-bound-v264/readbacks/curve-inputs-consumers.md)

`TwoAdicBoundHyp` 私有定义 `8e8bfc55-dff6-4673-a8ca-f1690de9eb2f` 已发布回读。`twoAdicBound` 解答 `6bb69978-4bcb-4304-884e-3d90d9e4d46d` 及 `curveInputs_twoAdic_fields` 解答 `b1e54210-e9a0-4d0a-83f2-53b04159f967` 均获 `ACCEPTED`。已核对两个节点的 `Proved` 状态、私有可见性、完整题面、环境和上传解答哈希。 [定义回读](platform/receipts/TwoAdicBoundHyp/published-item.json) · [主定理验收](platform/receipts/twoAdicBound/verification-result.json) · [字段验收](platform/receipts/curveInputs_twoAdic_fields/verification-result.json)

| 任务 | 退出码 | 墙钟秒 | CPU 秒（用户态 + 系统态） | 峰值 RSS GiB | 诊断 |
| --- | ---: | ---: | ---: | ---: | --- |
| [`ci-026318-903c76d4`](ci-026318-903c76d4.result.json) | 1 | 150.86 | 154.24（11.65 + 142.59） | 8.24 | 源端整数转换未先规范化，后续公理检查检出 sorryAx |
| [`ci-026364-8b27bd42`](ci-026364-8b27bd42.result.json) | 0 | 224.11 | 224.11（14.79 + 209.32） | 8.33 | 源端六项完整陈述与表达式通过 |
| [`ci-026382-65d4e4d7`](ci-026382-65d4e4d7.result.json) | 1 | 189.06 | 183.85（12.01 + 171.84） | 8.38 | twoAdicBound′ 的辅助实例映射不完整 |
| [`ci-026404-0e0459ab`](ci-026404-0e0459ab.result.json) | 1 | 74.95 | 75.27（12.84 + 62.43） | 8.60 | 两项原生字段检查尚未识别编译后的证明表达式 |
| [`ci-026417-b4f013a8`](ci-026417-b4f013a8.result.json) | 0 | 145.64 | 145.68（16.09 + 129.59） | 8.59 | 六项跨版本比较及原生字段与消费者转发通过 |
| [`ci-026416-08b346a6`](platform/ci-026416-08b346a6.result.json) | 1 | 64.50 | 69.14（10.50 + 58.64） | 4.20 | 平台拼包的实例及命名替换导致类型和重写失败 |
| [`ci-026439-f438aad0`](platform/ci-026439-f438aad0.result.json) | 0 | 39.07 | 44.29（11.76 + 32.53） | 4.20 | 修正组合后主定理题面、解答及公理检查通过 |
| [`ci-026440-b356a131`](platform/fields/ci-026440-b356a131.result.json) | 0 | 36.29 | 33.55（1.95 + 31.60） | 3.99 | 平台字段题面、解答及公理检查通过 |

任务使用独占工作区，输入版本为 `3da69dc8`，快照 ID 为空。物理内存为调度器的进程树 RSS，PSS 和 degraded 标记未知。通过的公理审查仅报告 `propext`、`Classical.choice` 和 `Quot.sound`。
