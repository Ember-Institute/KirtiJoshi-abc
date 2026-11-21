# B1 局部高度与有限处的私有平台验收

2026-11-20 至 2026-11-21 从会话 `01a1ecf6-2a67-7292-a661-53696e834cf6` 的发布任务回读。所有已发布条目的标识、名称、陈述或定义体、自然语言陈述与来源均已核对。条目可见性为 `private`，Mathlib 修订为 `0df444a360eaa60ab8c11dca51a86af692955474`。

| 条目 | 平台条目 ID | 当前平台状态 | 解答回执 |
| --- | --- | --- | --- |
| 良好约化有限处的局部高度 | `0a09d4f8-e197-417e-9330-9b4b9351bf0a` | `Proved` | [`ACCEPTED`](good-reduction/verification-result.json) |
| 乘法约化有限处的局部高度 | `68782ac0-2e25-42fa-9690-efbe4d8b1a3f` | `Proved` | [`ACCEPTED`](multiplicative-place/verification-result.json) |
| 有限高度求和 | `e7ec8de2-9b70-4787-85e3-c22303ff9616` | `Proved` | [`ACCEPTED`](finite-height-sum/verification-result.json) |
| 下方有限处 | `59dfa846-1d49-4d6b-9205-27f46fc7d73f` | 私有定义已发布 | [条目](place-under/published-item.json) |
| 相对赋值 | `f2f7627a-9442-4303-a499-e06daf876398` | 私有定义已发布 | [条目](relative-valuation/published-item.json) |
| 有限处在数域同构下的搬运 | `edbb4902-d99d-4c8e-91b5-b54eda9cd0e6` | 私有定义已发布 | [条目](finite-place-map-equiv/published-item.json) |
| 有限高度在数域同构下的不变性 | `92e7ddc1-91ad-4c7b-aff5-e3295561cecc` | `Proved` | [`ACCEPTED`](finite-height-map-equiv/verification-result.json) · [终态](finite-height-map-equiv/final-item.json) |
| 有限处绝对算术 | `8527b187-2a2f-431f-b8c6-1b5ee4adf2b9` | 私有定义已发布 | [条目](absolute-place-arithmetic/published-item.json) |
| 相对次数塔 | `230f30e5-4d52-4a1c-a25b-1f832d6b3be5` | 私有定义已发布 | [条目](relative-degree-tower/published-item.json) |
| 数域有限扩张下的有限高度缩放 | `bc257ddc-faf2-4fe7-a1bf-bd0458023713` | `Proved` | [`ACCEPTED`](finite-height-extension/verification-result.json) · [终态](finite-height-extension/final-item.json) |
| Tate 输入供应 | `e8e269bd-328a-4d9d-b9a4-880db0c2d141` | 私有定义已发布 | [条目](tate-inputs/published-item.json) |
| 曲线供应器高度 | `3ac4b294-b315-40ed-a3c1-ba72b9a3fdab` | 私有定义已发布 | [条目](provider-height/published-item.json) |
| 惯性次数 | `2cc11291-2c10-460f-a701-3ba355e717b1` | 私有定义已发布 | [条目](inertia-degree/published-item.json) |

- 两条局部高度公式的跨版本审查为 `ci-023091-faa7fb06`。乘法约化和良好约化的独立审查分别为 `ci-023286-643b9760` 与 `ci-023291-ebe7c284`。 [跨版本回执](../b1-local-height-correspondence-20261119/round-ci-023091-faa7fb06-result.json) · [三语读回](../b1-local-height-correspondence-20261119/readback.md)
- 有限高度求和审查 `ci-023485-b07b9069` 核对了完整类型及两份证明项。 [来源和三语读回](../b1-finite-height-sum-20261119/SOURCE_LEDGER.md)
- 下方有限处和相对赋值审查 `ci-023736-749237d6` 核对了十条声明的完整类型、证明项与公理。 [来源和三语读回](../b1-place-under-relative-valuation-20261119/SOURCE_LEDGER.md)
- 同构不变性来源审查 `ci-023566-365b8789` 和独立三语读回已归档，私有解答已验收。 [来源和三语读回](../b1-finite-height-map-equiv-20261119/SOURCE_LEDGER.md)
- 曲线供应器高度三条定义已通过完整跨版本对应。实际 Tate 输入仍待完成跨版本重放。 [供应器审查](../b1-tripod-height-correspondence-20261121/provider-height/cross-version-result.json) [来源](../b1-tate-existence-v227-20261118/TATE_INPUTS_SOURCE_LEDGER.md) · [Tate 输入三语读回](../b1-tate-existence-v227-20261118/tate-inputs-supply-readback.md)

## 2026-11-21 有限高度解答验收

同构不变性复用旧会话的证明体。缩放链在有限处算术包中显式引用 `AbcAdaptation.Reference.Iut.residueChar`。本地合并审查也在相对次数塔的等式中显式引用同一声明，以复现单独导入次数塔时的名称解析。平台陈述首轮发布因预备导入未定义 `AbcAdaptation.Reference.Iut` 而失败。删除未使用的 `open` 后原定理陈述通过发布，原解答提交获验收。 [首轮发布](finite-height-extension/attempt-1/publish-result.json) · [缩放链来源和三语读回](../b1-finite-extension-scaling-20261120/SOURCE_LEDGER.md)

| 独占审查 | 退出码 | 墙钟秒 | CPU 秒（用户态 + 系统态） | 峰值 RSS GiB | 诊断 |
| --- | --- | --- | --- | --- | --- |
| [`ci-026039-3b746884`](finite-height-map-equiv/ci-026039-3b746884.result.json) | 1 | 138.82 | 136.19（3.93 + 132.26） | 4.03 | 类型核对别名遗漏了解答的两个显式参数 |
| [`ci-026046-97af949d`](finite-height-map-equiv/ci-026046-97af949d.result.json) | 0 | 122.52 | 119.91（3.90 + 116.01） | 4.03 | 同构不变性解答与平台类型一致 |
| [`ci-026061-bd97115d`](absolute-place-arithmetic/ci-026061-bd97115d.result.json) | 0 | 83.21 | 78.66（3.35 + 75.31） | 3.86 | 有限处算术包主公式 |
| [`ci-026063-dd342eaf`](finite-height-extension/ci-026063-dd342eaf.result.json) | 1 | 83.02 | 78.49（3.82 + 74.67） | 4.05 | 合并审查中的同名剩余标数导致相对比较和重写失败 |
| [`ci-026071-a7fb1869`](relative-degree-tower/ci-026071-a7fb1869.result.json) | 0 | 72.06 | 72.87（4.53 + 68.34） | 3.84 | 次数塔原包七条声明 |
| [`ci-026072-18d97c5c`](finite-height-extension/ci-026072-18d97c5c.result.json) | 0 | 86.66 | 87.10（4.90 + 82.20） | 4.08 | 缩放链的十二条声明及平台解答 |

各回执记录实际 Lean 文件参数、输入摘要及 `exclusive_worktree` 模式，快照 ID 均为空。表中资源取自回执 `result.resources`，PSS 与 degraded 标记均未知。四项通过的审查仅报告 `propext`、`Classical.choice` 和 `Quot.sound`。原数学模块的 Checks、ImportAudit、Act1Scene1 和 AxiomAudit 分别由 `ci-019582-8d08ff0e` 和 `ci-019627-402f9dc7` 验收。 [同构不变性项目审查](../main-chain-open-20261116/b1-finite-height-map-equiv-review-v253-result.json) · [缩放链项目审查](../main-chain-open-20261116/b1-height-extension-scaling-review-v257-result.json)
