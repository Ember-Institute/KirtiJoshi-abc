# B1 局部高度与有限处的私有平台验收

2026-11-20 从会话 `01a1ecf6-2a67-7292-a661-53696e834cf6` 的发布任务回读。所有已发布条目的标识、名称、陈述或定义体、自然语言陈述与来源均已核对。条目可见性为 `private`，Mathlib 修订为 `0df444a360eaa60ab8c11dca51a86af692955474`。

| 条目 | 平台条目 ID | 当前平台状态 | 解答回执 |
| --- | --- | --- | --- |
| 良好约化有限处的局部高度 | `0a09d4f8-e197-417e-9330-9b4b9351bf0a` | `Proved` | [`ACCEPTED`](good-reduction/verification-result.json) |
| 乘法约化有限处的局部高度 | `68782ac0-2e25-42fa-9690-efbe4d8b1a3f` | `Proved` | [`ACCEPTED`](multiplicative-place/verification-result.json) |
| 有限高度求和 | `e7ec8de2-9b70-4787-85e3-c22303ff9616` | `Proved` | [`ACCEPTED`](finite-height-sum/verification-result.json) |
| 下方有限处 | `59dfa846-1d49-4d6b-9205-27f46fc7d73f` | 私有定义已发布 | [条目](place-under/published-item.json) |
| 相对赋值 | `f2f7627a-9442-4303-a499-e06daf876398` | 私有定义已发布 | [条目](relative-valuation/published-item.json) |
| 有限处在数域同构下的搬运 | `edbb4902-d99d-4c8e-91b5-b54eda9cd0e6` | 私有定义已发布 | [条目](finite-place-map-equiv/published-item.json) |
| 有限高度在数域同构下的不变性 | `92e7ddc1-91ad-4c7b-aff5-e3295561cecc` | `Open` | [条目](finite-height-map-equiv/published-item.json) |
| Tate 输入供应 | `e8e269bd-328a-4d9d-b9a4-880db0c2d141` | 私有定义已发布 | [条目](tate-inputs/published-item.json) |
| 曲线供应器高度 | `3ac4b294-b315-40ed-a3c1-ba72b9a3fdab` | 私有定义已发布 | [条目](provider-height/published-item.json) |
| 惯性次数 | `2cc11291-2c10-460f-a701-3ba355e717b1` | 私有定义已发布 | [条目](inertia-degree/published-item.json) |

- 两条局部高度公式的跨版本审查为 `ci-023091-faa7fb06`。乘法约化和良好约化的独立审查分别为 `ci-023286-643b9760` 与 `ci-023291-ebe7c284`。 [跨版本回执](../b1-local-height-correspondence-20261119/round-ci-023091-faa7fb06-result.json) · [三语读回](../b1-local-height-correspondence-20261119/readback.md)
- 有限高度求和审查 `ci-023485-b07b9069` 核对了完整类型及两份证明项。 [来源和三语读回](../b1-finite-height-sum-20261119/SOURCE_LEDGER.md)
- 下方有限处和相对赋值审查 `ci-023736-749237d6` 核对了十条声明的完整类型、证明项与公理。 [来源和三语读回](../b1-place-under-relative-valuation-20261119/SOURCE_LEDGER.md)
- 同构不变性来源审查 `ci-023566-365b8789` 和独立三语读回已归档，私有解答待平台验收。 [来源和三语读回](../b1-finite-height-map-equiv-20261119/SOURCE_LEDGER.md)
- 实际 Tate 输入与曲线供应器高度的完整跨版本对应仍开放。 [来源](../b1-tate-existence-v227-20261118/TATE_INPUTS_SOURCE_LEDGER.md) · [Tate 输入三语读回](../b1-tate-existence-v227-20261118/tate-inputs-supply-readback.md)
