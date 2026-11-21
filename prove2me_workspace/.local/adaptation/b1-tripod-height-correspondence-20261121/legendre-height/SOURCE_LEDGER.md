# Legendre 与 Tate 高度的双向比较

固定来源为 `refer/iut` 提交 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，许可证为 Apache 2.0。给定同一 Legendre 曲线供应数据，比较把实际 Tate 局部高度除以六后与归一化 Weil 高度相比较。两个统一误差界分别为 $\log(2)/3$ 和 $c|V|+c+\log(2)/3$。现有构造器将比较传入 `htCan_equiv`，并用第二个界及点的次数上界构造 `northcott`。 [来源定义](../../../../../refer/iut/Iut/Tripod/CurveFacts.lean#L403) · [来源定理](../../../../../refer/iut/Iut/Tripod/Height.lean#L791) · [构造器](../../../../Solutions/Source_TripodCurveInputs.lean#L40) · [三语读回及消费者](readback-supplement.md)

源端 Lean `4.35.0-rc3` 重放原命令。目标端 Lean `4.33.1` 在内核中比较 `LegendreHeightHyp` 的定义与 `legendreHeight` 的完整类型和证明，并核对四条数值依赖的完整类型。三条数值估计复用目标模块中的别名，泛型 $j=0$ 引理以原命令重放。公理审查只报告 `propext`、`Classical.choice`、`Quot.sound`。 [源端表达式](source-facts.jsonl.gz) · [审查结果](cross-version-result.json) · [审查证据](cross-version-expressions.jsonl.gz)

定义包 `LegendreHeightHyp` 的私有节点为 `add2ff42-bd50-4c6b-a3e1-5e07563a095c`。解答 `cae8b374-7a45-4d67-97f4-eb212a10562d` 获 `ACCEPTED`，定理 `714cfc08-57af-474e-80d4-7ded74e9406f` 回读为 `Proved`。私有定义源码、定理题面、环境及解答哈希均已回读比对。 [平台定义](platform/receipts/LegendreHeightHyp/published-item.json) · [解答验收](platform/receipts/legendreHeight/verification-result.json) · [终态节点](platform/receipts/legendreHeight/final-item.json)

## MCP-CI 回执

| 任务 | 退出码 | 墙钟秒 | CPU 秒（用户态 + 系统态） | 峰值 RSS GiB | 诊断 |
| --- | ---: | ---: | ---: | ---: | --- |
| [`ci-026304-56aec5aa`](ci-026304-56aec5aa.result.json) | 0 | 142.02 | 145.99（25.04 + 120.95） | 9.77 | 来源中的弃用提示与 tactic 建议 |
| [`ci-026343-8940ddef`](ci-026343-8940ddef.result.json) | 0 | 258.95 | 257.58（148.62 + 108.96） | 8.90 | 两条声明及四条依赖类型通过 |
| [`ci-026378-41c5f4db`](platform/ci-026378-41c5f4db.result.json) | 0 | 77.99 | 77.26（4.14 + 73.12） | 4.70 | 私有平台组合定义与解答的公理检查通过 |

三个任务使用独占工作区 `3da69dc8`，快照 ID 为空。资源来自 MCP-CI 进程树，PSS 与 degraded 标记未知。
