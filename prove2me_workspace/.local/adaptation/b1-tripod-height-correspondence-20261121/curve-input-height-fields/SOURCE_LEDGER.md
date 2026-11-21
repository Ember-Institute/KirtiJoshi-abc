# 曲线输入构造器的三个高度字段

固定来源为 `refer/iut` 提交 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`，许可证为 Apache 2.0。源端保留 `height_eq`、`htCan_equiv`、`northcott` 的原赋值和构造器的比较及有限性参数。目标审查从已编译的 `curveInputsOfSL2Image` 提取三个字段，比较完整类型及证明，再代入 `legendreHeight P K` 和 `northcottHyp` 核对现有闭合字段定理。`toCorollary22Inputs` 将这些字段传给推论 2.2 的输入记录。 [来源构造器](../../../../../refer/iut/Iut/Tripod/CurveFacts.lean#L503) · [目标构造器](../../../../Solutions/Source_TripodCurveInputs.lean#L36) · [对应结果](cross-version-result.json) · [三语读回](platform/readback.md)

平台用一条合取定理供应三个字段。其 Northcott 证明使用第二个高度界，在高度上界 $H$ 和次数上界 $d$ 下调用已有的 `boundedDegreeFiniteness`。解答 `218300f8-af93-44f0-8bbd-e0c01756d806` 获 `ACCEPTED`，私有节点 `8b0d1b59-d3ed-4a5d-a1fa-2922741c5545` 回读为 `Proved`。已核对发布陈述、环境及实际解答哈希。通过的目标审查仅报告 `propext`、`Classical.choice`、`Quot.sound`。 [题面](platform/curveInputs_height_fields.problem.json) · [提交终态](platform/receipts/curveInputs_height_fields/verification-result.json) · [节点回读](platform/receipts/curveInputs_height_fields/final-item.json)

| 任务 | 退出码 | 墙钟秒 | CPU 秒（用户态 + 系统态） | 峰值 RSS GiB | 诊断 |
| --- | ---: | ---: | ---: | ---: | --- |
| [`ci-026365-90c09dc7`](ci-026365-90c09dc7.result.json) | 0 | 218.19 | 213.08（7.46 + 205.62） | 8.17 | 三条源字段已导出 |
| [`ci-026381-11473a1c`](ci-026381-11473a1c.result.json) | 0 | 77.45 | 76.63（4.93 + 71.70） | 4.74 | 三项源项、原生字段及闭合证明均通过 |
| [`ci-026403-4f7095b2`](platform/ci-026403-4f7095b2.result.json) | 1 | 4.58 | 4.04（0.25 + 3.79） | 0.37 | 平台稿的块注释开头写反 |
| [`ci-026415-acb065bc`](platform/ci-026415-acb065bc.result.json) | 0 | 62.92 | 60.43（2.28 + 58.15） | 3.99 | 修正注释后，平台类型与解答均通过 |

任务均使用独占工作区 `3da69dc8`，快照 ID 为空。PSS 与 degraded 标记未知。
