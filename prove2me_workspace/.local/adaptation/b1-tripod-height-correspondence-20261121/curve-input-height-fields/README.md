# §4.1 三足曲线高度字段

固定源为 `lana-agents/iut` 提交 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`。源端按 `CurveFacts.lean` 第 498–501 行选择 `P.h`、`P.curve`、`P.arith` 和 `P.tate`，在对应字段的完整类型下重放第 503、508 和 509 行的右侧。第 403 行的 `LegendreHeightHyp` 定义原样移入源端查询的上下文。 [字段赋值](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/CurveFacts.lean:492) · [字段类型](/home/admin-wsl/Coq/abc/refer/iut/Iut/Concrete/Existence.lean:390)

| 字段 | 源构造器右侧 | 现有目标辅助定理 |
| --- | --- | --- |
| `height_eq` | `fun _ _ => rfl`，局部高度由同一曲线的算术与 Tate 数据计算 | `curveInputs_height_eq P K d` |
| `htCan_equiv` | `hh : LegendreHeightHyp P K`，在 `K` 上比较 `(1/6) • P.h` 与 Weil 高度 | `curveInputs_htCan_equiv P K`，使用 `legendreHeight P K` |
| `northcott` | `northcott_of_equiv hN K d hh`，把 `P.h` 的上界 `H` 换成 Weil 高度的上界 `H / 6 + C` | `curveInputs_northcott P K d`，使用 `northcottHyp` 与 `legendreHeight P K` |

`height_eq` 依靠 `CurveProviders.h` 与 `localData` 的定义等式。归一化定理 `h_eq_finHeight_div` 已完成来源审查并通过私有平台验收，它供闭合的 `legendreHeight` 证明使用。源端第 508 行保留比较假设 `hh`，双向比较定理本身的完整证明另有跨版本审查。第 509 行仍保留 `hN : NorthcottHyp`，并使用 `Basic.lean` 第 451、457 行的限制与换高定理。目标的闭合实例 `northcottHyp` 来自既有 `boundedDegreeFiniteness`。构造器消费者 `toCorollary22Inputs` 将这些字段分别传给 `localData_height`、`htCan_equiv` 和 `northcott`。 [高度定义](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/CurveFacts.lean:390) · [归一化回执](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-tripod-height-correspondence-20261121/SOURCE_LEDGER.md) · [双向比较](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/Height.lean:791) · [Northcott 换高](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/Basic.lean:457) · [目标实例](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_NorthcottComparison.lean:25) · [消费者](/home/admin-wsl/Coq/abc/refer/iut/Iut/Concrete/Existence.lean:474)

## 草稿与验收输入

- `QueryTripodHeightFieldsSource.lean` 使用 dmod 已检查的 Lean `4.35.0-rc3` 源重放环境。它导出三条重放定理的完整内核类型、证明项和公理，输出位置由 `source-config.json` 指定。`source-environment.json` 记录编译环境及源码和工件哈希。
- `prepare-target-review.py` 读取源端的 `source-facts.jsonl`，生成 `target-review-config.json`。它保留原始 Lean 名称的数字分量，并将项目常量映射到现有目标声明。
- `AuditTripodHeightFieldSourceCorrespondence.lean` 在 Lean `4.33.1` 中读取 `curveInputsOfSL2Image` 的实际构造器应用，按 `CurveInputs` 元数据取字段，使用前序实参实例化字段类型。它在目标内核中比较迁移后的完整类型与证明，并检查 `rfl`、`hh` 和 `northcott_of_equiv hN K d hh` 的实际使用。它将 `hh` 和 `hN` 替换为已有证明，再与三个目标辅助定理核对。`target-environment.json` 记录相应目标哈希与缓存。

配置采用 `prove2me_workspace/.local/adaptation/b1-tripod-height-correspondence-20261121/curve-input-height-fields/` 作为存放目录。当前交付为审查草稿，Lean 回执由主会话取得。 [目标构造器](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCurveInputs.lean:26) · [目标辅助定理](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCurveInputsHeightFields.lean:22)
