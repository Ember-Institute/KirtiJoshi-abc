# 三足域与有限高度归一化

固定来源为 refer/iut 提交 07cb1da58f6d428a670dbb5dd6093d428bcbcdd8，许可证为 Apache 2.0。对实际供应的 Legendre 曲线，三足中间域与点域同构。曲线的 $j$ 不变量来自三足中间域，经该同构成为点域上的 Legendre $j$。有限高度求和、扩张缩放和同构不变性一起给出曲线供应器高度等于 $j$ 不变量的有限高度除以点域次数。该公式由本地的 auxiliaryHeight 恒等式及双向高度比较消费。 [源定理](../../../../refer/iut/Iut/Tripod/Height.lean#L603) · [本地归一化](../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_HeightNormalization.lean#L23) · [本地消费者](../../../Solutions/Source_TripodProviderAuxiliaryHeight.lean#L16)

源端使用 Lean 4.35.0-rc3 重放并导出原始表达式，目标端为 Lean 4.33.1 和 Mathlib 0df444a360eaa60ab8c11dca51a86af692955474。归一化定理的源命令与目标命令逐字一致。迁移审查在完整内核类型和证明项上核对三足域识别、$j$ 传输和归一化主定理。$j$ 传输的公开绑定位置一致，展开表达式中的内部绑定位置有差异，完整类型通过内核定义相等。归一化证明中的域自作用实例在审查重放时由该域的标准忠实标量作用实例接替。在两份证明均通过完整目标类型检查后，使用证明无关性比较。 [域与 j 审查](field-and-j/cross-version-result-v3.json) · [归一化审查](normalization/cross-version-result-v2.json) · [旧稿和来源摘要](platform/dependencies.json)

CurveProviders.tate、localData、h 的完整类型和定义值也通过内核比较。实际 Tate 输入构造的完整跨版本重放仍开放。 [供应器审查](provider-height/cross-version-result.json)

平台复用了私有 FieldInvariant，并私有发布 FieldLegendreFacts、FieldIdentification、FieldTransport 和 JTransport。h_eq_finHeight_div 使用三项已证的有限高度公式。提交 93da123b-c25a-4eff-b7e3-dbeee8b2bd29 获 ACCEPTED，节点 3ba94824-130b-402a-bc95-e768360bb56d 回读为 Proved。 [平台依赖](platform/platform-import-readback.json) · [验收](platform/receipts/h_eq_finHeight_div/verification-result.json) · [节点终态](platform/receipts/h_eq_finHeight_div/final-item.json)

独立审读使用剥离注释后的 Lean 陈述与定义。三语保留局部 Tate 和式按曲线定义域次数归一化，以及有限 $j$ 高度按点域次数归一化。 [审读输入](blind/Target.lean.txt) · [中文](independent-readback/zh-Hans.md) · [English](independent-readback/en.md) · [日本語](independent-readback/ja.md)

## MCP-CI 回执

| 任务 | 退出码 | 墙钟秒 | CPU 秒（用户态 + 系统态） | 峰值 RSS GiB | 诊断 |
| --- | --- | --- | --- | --- | --- |
| [ci-026080-a7a01815](receipts/ci-026080-a7a01815.result.json) | 0 | 155.65 | 100.28（4.46 + 95.82） | 4.72 | 三个曲线供应器高度定义通过 |
| [ci-026081-96ebef55](receipts/ci-026081-96ebef55.result.json) | 1 | 155.16 | 100.89（5.18 + 95.71） | 4.81 | $j$ 传输陈述内部绑定位置不同 |
| [ci-026082-98e75d76](receipts/ci-026082-98e75d76.result.json) | 1 | 156.91 | 101.96（7.90 + 94.06） | 4.99 | 归一化定理证明引用已迁移的库实例及未导入的数域代数性实例 |
| [ci-026090-1e772788](receipts/ci-026090-1e772788.result.json) | 0 | 72.61 | 70.31（3.14 + 67.17） | 4.10 | 平台归一化解答及陈述通过 |
| [ci-026098-250e9320](receipts/ci-026098-250e9320.result.json) | 1 | 156.97 | 153.49（8.17 + 145.32） | 4.83 | 核对了 $j$ 传输完整类型，map_legendreJ 映射到错误的命名空间 |
| [ci-026099-0a6109f5](receipts/ci-026099-0a6109f5.result.json) | 0 | 163.06 | 158.94（13.79 + 145.15） | 5.03 | 归一化定理的完整类型和值通过 |
| [ci-026109-15534529](receipts/ci-026109-15534529.result.json) | 0 | 280.36 | 273.03（8.85 + 264.18） | 4.87 | 三足域识别和 $j$ 不变量传输的完整类型和值通过 |

回执均为独占工作区，快照 ID 为空。资源使用调度器的进程树 RSS，PSS 和 degraded 标记未知。通过的审查仅报告 propext、Classical.choice 和 Quot.sound。原生七模块的 Checks、ImportAudit、Act1Scene1 和 AxiomAudit 已由 ci-019679-3acf973e 验收，该任务覆盖 84 个声明。 [原生项目回执](../main-chain-open-20261116/b1-tripod-all-review-v260-result.json)

## 实际 Tate 输入的源端审查

独占审查 ci-026142-15bb9e12 在 Lean 4.35.0-rc3 核对了七条原始声明的完整类型和值，并生成十四份归一化证书。源端仅使用 Lean 标准公理。任务退出码为 0，墙钟 555.29 秒，CPU 467.74 秒（用户态 21.15 秒，系统态 446.59 秒），进程树峰值 RSS 为 9.23 GiB，PSS 未取得。诊断是引用参考工程的一条生成引理。目标端需继续核对同一七条声明。 [审查回执](tate-inputs-drafts/ci-026142-15bb9e12.result.json) · [源端证书](tate-inputs-drafts/source-common-core-certificates.json.gz) · [目标声明候选](tate-inputs-drafts/target-candidates.json)

完整表达式与大型证书以 gzip 归档。复现审查前将相应文件解压至配置记录的路径。 [三足域与 j 传输表达式](field-and-j/cross-version-expressions-v3.jsonl.gz) · [归一化表达式](normalization/cross-version-expressions-v2.jsonl.gz)
