# 三足曲线输入构造器

来源为 iut `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`。构造器和它的 21 个赋值来自 `CurveFacts.lean:492–520`。项目归档含同一记录的 `toCorollary22Inputs`，并用同一条曲线生成局部高度、选择素数和 P7 数据。 [源构造器](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/CurveFacts.lean:492) · [推论 2.2 消费者](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean:142) · [P7 与 ABC 调用](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/Main.lean:89)

| 字段 | 源构造器的供应 | 后续消费者 |
| --- | --- | --- |
| `h` | `P.h` | `Corollary22Inputs.h` |
| `curve` | `P.curve x` | 局部高度、SL₂ 像和 P7 的椭圆曲线 |
| `arith` | `P.arith x` | 同一曲线的局部高度和 P7 |
| `tate` | `P.tate x` | 同一曲线的局部高度、选素数和 P7 |
| `modRep` | `P.modRep x ℓ hℓ` | `Corollary22Inputs.SL2Image` 与 P7 的模 ℓ 表示 |
| `height_eq` | `rfl` | `Corollary22Inputs.localData_height` |
| `deg_le` | `deg_le` 应用 `hdeg3`、`hdeg5`，再用 `hx.2` | `Corollary22Inputs.localData_deg_le` |
| `dmod_le` | `dmod_le` 后接 `hx.2` | P7 模域次数 |
| `htCan_equiv` | `hh` | `Corollary22Inputs.htCan_equiv` |
| `northcott` | `northcott_of_equiv hN K d hh` | `Corollary22Inputs.northcott` |
| `B` | `max (4 * K.c) 0` | `Corollary22Inputs.B` |
| `B_nonneg` | `le_max_right _ _` | `Corollary22Inputs.B_nonneg` |
| `heightEq_two_le` | `hB x hx.1` | `Corollary22Inputs.heightEq_two_le` |
| `HasCyclicSubgroup` | `(P.curve x).HasCyclicSubgroup ℓ` | `Corollary22Inputs.HasCyclicSubgroup` |
| `TK` | `TK` | `Corollary22Inputs.TK` |
| `cyclic_bound` | `CF.cyclic` | `Corollary22Inputs.cyclic_bound` |
| `sl2_of` | `sl2Image P x ℓ hℓ` | `Corollary22Inputs.sl2_of` 和 P7 |
| `logDiff_eq` | `logDiff_eq x _ _` | P7 的正规化判别式恒等式 |
| `excCore_finite` | `hcore` | `Corollary22Inputs.excCore`、`excCore_finite` 和 P7 的 core 条件 |
| `logCond_ge` | `hge x` | P7 的第一条导子比较 |
| `logCond_le` | `hle x` | P7 的第二条导子比较 |

## 私有平台定义

`CurveFacts`、`LegendreHeightHyp`、`FieldIdentification` 和私有定理 `sl2Image`、`dmod_le`、`torsionCoords_finite` 是平台模块的直接项目导入。`CurveFacts` 带入实际 `CurveInputs` 和 `PrimeSelection_HeightParts`。后者已有 `LocalHeightData.heightEq`。二进处已发布单独定义包自身也声明 `heightEq`，构造器模块就地保留 `TwoAdicBoundHyp` 的原定义，并共用 `PrimeSelection_HeightParts` 的 `heightEq`。 [直接导入、条目 ID 和哈希](platform/dependencies.json) · [平台模块](platform/Def_AbcAdaptation_Reference_Iut_Tripod_CurveInputsAssembly.lean)

本地移植的 `CurveDegreeBound`、`DifferentDegree`、`NorthcottComparison` 的精确构造器所需声明由构造器平台模块提供。`logDiff_eq` 的整性前提用 `Algebra.IsIntegral.isIntegral` 供给，和源辅助引理的证明相同。`northcott_of_equiv` 用 `hh.2` 取得反向比较，和 `DiscrepancyEquiv.ge` 的定义相同。对 `hN` 的换高只需要 `NorthcottHyp` 的内容，`boundedDegreeFiniteness` 用在源构造器的调用者。

`sl2Image` 的条目状态为私有 `Proved`，提交回执为 `SKETCH_ACCEPTED`。其一般曲线 SL₂ 包含、像阶可除性、分歧指数可除性、Tate 结构、Tate 均匀化以及点方程、加法和满射七层供应对应的九条平台定理均已私有 `Proved`。平台稿读取平台的定理模块。本地审查稿使用已通过公理检查的 `Source_SL2ImageFromSource` 闭合证明和归档 `dmod_le` 的证明体。 [本地平台审查稿](platform/ReviewPlatformTripodCurveInputsAssembly.lean) · [SL₂ 私有终态](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/platform-sl2/modular-tate/AbcAdaptation.Tripod.sl2Image-current-item.json)

首个发布 job `80a13055-d329-491c-981a-9167e718c135` 缺少已证定理 `torsionCoords_finite` 的显式导入。补齐后，本地复审 `ci-026624-61b854a0` 退出码 0，墙钟 110.23 秒，CPU 112.95 秒（用户态 11.35 秒、系统态 101.60 秒），进程树峰值 RSS 7.57 GiB，PSS 和 degraded 标记未知。六条声明的公理检查仅含 Lean 标准公理。第二次发布 job `300d0400-2c74-4bce-9c1f-7e215d850681` 终态为 `PUBLISHED`。定义 ID 为 `030038fc-ada9-4a53-bdf0-5453969ee9a4`，可见性为私有，Mathlib 为 `0df444a360eaa60ab8c11dca51a86af692955474`。平台返回的定义 SHA-256 为 `ff25ce29ecb058d74c313ef409ef10f176cc43641a47c344f34e96bdec870dd5`。 [首次发布诊断](platform/receipts/attempt-1/publish-result.json) · [本地复审](platform/ci-026624-61b854a0.result.json) · [私有定义回读](platform/receipts/attempt-2/published-item.json)

## 调用者供应

| 参数 | 源调用 | 已核对状态 |
| --- | --- | --- |
| `hN` | `northcottHyp` | 私有 `boundedDegreeFiniteness` 为 `Proved`，ID `bfd60e2f-e299-4833-ab7e-03d2b7ccfd94` |
| `hh` | `legendreHeight P K` | 私有 `Proved`，ID `714cfc08-57af-474e-80d4-7ded74e9406f` |
| `hB` | `twoAdicBound P K` | 私有 `Proved`，ID `107a1761-3e17-4f1b-b82b-a6c9323eda0a` |
| `hdeg3`、`hdeg5` | `torsionDegreeBound_three'`、`torsionDegreeBound_five'` | 本地 `ci-020829-26f0c710` 通过类型及公理审查，私有归档尚无终态 |
| `hge`、`hle` | `logCondGe P`、`logCondLe P` | 本地 `ci-020829-26f0c710` 通过公理审查，私有归档尚无终态 |
| `CF` | `⟨cyclicBoundOdd P K d⟩`，取 `cyclicConst` 给定的常数 | 本地 `ci-022825-5942080c` 通过，私有归档尚无终态 |
| `hcore` | `coreFiniteness Pi1 P K d` | 本地 `coreFiniteness_of_modelAG` 通过 `ci-021147-606ee1da`，私有归档尚无终态，对任意 `AG` 仍使用原参数 |

上述尚无私有回执的供应只为闭合调用者所需。已经发表的 `curveInputs_height_fields`（`8b0d1b59-d3ed-4a5d-a1fa-2922741c5545`）和 `curveInputs_twoAdic_fields`（`68151c5f-d375-4ecf-a4de-ddda9fdf66ad`）分别给出三个高度字段和两个二进处证明字段，均为私有 `Proved`。

## 参考与目标审查

- `QueryTripodCurveInputsSource.lean` 从 Lean `v4.35.0-rc3` 的真实 `Iut.Tripod.CurveFacts.olean` 读取构造器。该模块及其依赖产物仍待补齐。
- `QueryTripodCurveInputsReplay.lean` 使用参考编译器和已验收的 `B1SourceReplay`。它重放实际记录、算术和原构造器正文，并显式给出单个 `∀ P, SL2ImageHyp P` 供应参数。该参数只用于第 17 个字段 `sl2_of`。回放证据带 `explicitSL2Supplier: true`。
- `AuditTripodCurveInputsTarget.lean` 用 Lean `v4.33.1` 审查实际目标记录。提供 `TRIPOD_CURVE_INPUTS_SOURCE_FACTS` 时，审查用闭合的目标 `sl2Image` 实例化参考回放参数，检查完整类型、21 个字段的依赖类型和值，以及直接供应引用。

两端都以 `TRIPOD_CURVE_INPUTS_FACTS` 指定绝对输出路径。参考端可沿用 `ci-026365-90c09dc7` 的工具链、`LEAN_PATH` 与外部依赖清单。各自从主工作区提交独占 MCP-CI review，`target: "file"`，首检 `60s` 和 `16GiB`。平台组合稿的本地审查只需 `ReviewPlatformTripodCurveInputsAssembly.lean` 和项目现有目标 `LEAN_PATH`。

本地原生构造器独占 `ci-026465-009c2a0e` 已通过，公理仅 `propext`、`Classical.choice`、`Quot.sound`。墙钟 252.51 秒，CPU 250.63 秒（用户态 5.53 秒、系统态 245.10 秒），峰值进程树 RSS 7.50 GiB，PSS 未知。较早的两次审查 `ci-020827-2725d6f7` 和 `ci-020829-26f0c710` 覆盖源实现入口与算术供应。项目针对这批原生模块的 Checks、ImportAudit、Act1Scene1 与 AxiomAudit 归档在 `ci-020844-3d5ac401`。 [原生独占回执](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-tripod-height-correspondence-20261121/curve-input-assembly/ci-026465-009c2a0e.result.json) · [原生模块台账](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md:200)

目标内核比较用显式 SL₂ 输入的参考重放核对了完整构造器类型和全部 21 个字段。目标用已验收的 `sl2Image` 实例化这个输入，再按实际记录的字段名、类型、赋值及所用声明检查。原始 `Iut.Tripod.CurveFacts.olean` 的独立审查需要补齐依赖产物。 [参考重放回执](ci-026542-7fccbe6b.result.json) · [目标比较回执](ci-026600-5a180380.result.json)

| MCP-CI 回执 | 源 SHA-256 前缀 | 退出码 | 墙钟秒 | CPU 秒（用户态 + 系统态） | 进程树峰值 RSS GiB | 诊断 |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| [ci-026567-4c08e11d](ci-026567-4c08e11d.result.json) | `54b5d95f72902034` | 1 | 140.18 | 140.63（7.70 + 132.93） | 8.01 | 比较脚本误用保留字 `matches` |
| [ci-026585-a8da55e8](ci-026585-a8da55e8.result.json) | `c8b6d29b0cc64a78` | 1 | 120.06 | 119.66（7.15 + 112.51） | 8.05 | 比较脚本引用了当前 Lean 不提供的 `when` |
| [ci-026600-5a180380](ci-026600-5a180380.result.json) | `9df449a0e75b492b` | 0 | 127.57 | 127.40（8.31 + 119.09） | 8.10 | 全部 21 字段匹配。两项公理检查只含 Lean 标准公理 |

目标比较在当前工作区独占运行，`actual_arguments` 是 `lean` 和 `AuditTripodCurveInputsTarget.lean` 相对路径。回执的 PSS 和 degraded 标记未知。

## 参考端容器与 θ 区域

`Iut.LocalTheory.container` 的有限支撑证明显式展开各张量分量的成员关系，再用奇未分歧处的 `logShell_eq_integral`。`Iut.LocalTheory.proj_productRegion` 在同一个张量族上显式定型 `Function.update` 的输入和目标。两段证明沿用已验收的移植稿，补丁落在参考端构建副本。 [参考补丁](reference-compatibility/Iut.Concrete.Container.patch) · [移植稿](../../../Solutions/Source_ReferenceIutConcreteContainer.lean#L134)

`Iut.ThetaLocalData.thetaPilot` 的有限支撑证明把胶囊索引显式写为 `Fin n`，用 `dif_pos p.2` 裁去素数判定分支，再按各张量分量应用 `thetaComponent_eq_integral`。 [参考补丁](reference-compatibility/Iut.Concrete.ThetaRegion.patch) · [移植稿](../../../Solutions/Source_ReferenceIutConcreteThetaRegion.lean#L192)

| MCP-CI 回执 | 输入 SHA-256 前缀 | 退出码 | 墙钟秒 | CPU 秒（用户态 + 系统态） | 峰值 RSS GiB | 诊断 |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| [ci-026664-4fc82916](reference-receipts/ci-026664-4fc82916.result.json) | `e269ee05fef10bbb` | 1 | 194.70 | 192.57（5.78 + 186.79） | 7.74 | 原 `Container.lean` 第 174、264、266、267 行的重写与更新证明失败 |
| [ci-026709-46482e3d](reference-receipts/ci-026709-46482e3d.result.json) | `adbe5f3a6c58f1ea` | 0 | 151.14 | 149.25（6.90 + 142.35） | 7.75 | 生成 `Container.olean`，原第 209、210 行有 `haveI` lint 提示 |
| [ci-026722-b0cb3fd3](reference-receipts/ci-026722-b0cb3fd3.result.json) | `9e30ce452b59b34b` | 0 | 151.97 | 149.46（5.76 + 143.70） | 7.63 | `container`、`proj_productRegion`、`vol`、`hull` 的公理审查通过 |
| [ci-026729-0eb0edb8](reference-receipts/ci-026729-0eb0edb8.result.json) | `ff4529ff0b041b7d` | 1 | 162.80 | 160.52（8.18 + 152.34） | 7.77 | 原 `ThetaRegion.lean` 第 251、261 行的有限支撑证明失败 |

这些任务均在当前工作区的 `prove2me_workspace` 独占执行，HEAD 为 `9cf23097`，快照 ID 为空。产物任务的实际参数是 `lean`、相应源文件和 `-o` 产物路径，审查任务直接检查所列审查文件。RSS 来自调度器的进程树采样，PSS 与 degraded 标记未知。四条声明仅依赖 `propext`、`Classical.choice` 和 `Quot.sound`。 [容器公理审查](ReviewReferenceContainer.lean)
