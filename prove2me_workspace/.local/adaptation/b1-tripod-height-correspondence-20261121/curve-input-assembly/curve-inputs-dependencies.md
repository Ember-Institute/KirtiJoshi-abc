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

`sl2Image` 的条目状态为私有 `Proved`，提交回执为 `SKETCH_ACCEPTED`。其一般曲线 SL₂ 包含、像阶可除性、分歧指数可除性、Tate 结构、Tate 均匀化以及点方程、加法和满射七层供应对应的九条平台定理均已私有 `Proved`。平台稿读取平台的定理模块。本地审查稿使用已通过公理检查的 `Source_SL2ImageFromSource` 闭合证明和归档 `dmod_le` 的证明体。 [本地平台审查稿](platform/ReviewPlatformTripodCurveInputsAssembly.lean) · [SL₂ 私有终态](../../b1-curve-field-arithmetic-20261118/platform-sl2/modular-tate/AbcAdaptation.Tripod.sl2Image-current-item.json)

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

- `QueryTripodCurveInputsSource.lean` 从 Lean `v4.35.0-rc3` 编译的 `Iut.Tripod.CurveFacts.olean` 读取构造器，导出其所属模块和 21 个字段。证据带 `explicitSL2Supplier: false`。
- `QueryTripodCurveInputsReplay.lean` 使用参考编译器和已验收的 `B1SourceReplay`。它重放实际记录、算术和原构造器正文，并显式给出单个 `∀ P, SL2ImageHyp P` 供应参数。该参数只用于第 17 个字段 `sl2_of`。回放证据带 `explicitSL2Supplier: true`。
- `AuditTripodCurveInputsTarget.lean` 用 Lean `v4.33.1` 核对完整类型、21 个字段的依赖类型和值，以及直接供应引用。实际模块证据中的 `sl2Image` 对应闭合的目标实现。使用回放证据时，该实现实例化回放参数。

两端都以 `TRIPOD_CURVE_INPUTS_FACTS` 指定绝对输出路径。实际模块审查使用参考产物覆盖目录，工具链、`LEAN_PATH` 和外部依赖见对应回执。各自从主工作区提交独占 MCP-CI review，`target: "file"`，首检 `60s` 和 `16GiB`。平台组合稿的本地审查只需 `ReviewPlatformTripodCurveInputsAssembly.lean` 和项目现有目标 `LEAN_PATH`。

本地原生构造器独占 `ci-026465-009c2a0e` 已通过，公理仅 `propext`、`Classical.choice`、`Quot.sound`。墙钟 252.51 秒，CPU 250.63 秒（用户态 5.53 秒、系统态 245.10 秒），峰值进程树 RSS 7.50 GiB，PSS 未知。较早的两次审查 `ci-020827-2725d6f7` 和 `ci-020829-26f0c710` 覆盖源实现入口与算术供应。项目针对这批原生模块的 Checks、ImportAudit、Act1Scene1 与 AxiomAudit 归档在 `ci-020844-3d5ac401`。 [原生独占回执](ci-026465-009c2a0e.result.json) · [原生模块台账](../../b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#pointwise-p7-with-tower-arithmetic-from-the-legendre-curve)

首次目标比较使用显式 SL₂ 输入的参考重放核对了完整构造器类型和全部 21 个字段。实际模块的比较见下方验收回执。 [参考重放回执](ci-026542-7fccbe6b.result.json) · [重放对应回执](ci-026600-5a180380.result.json)

| MCP-CI 回执 | 源 SHA-256 前缀 | 退出码 | 墙钟秒 | CPU 秒（用户态 + 系统态） | 进程树峰值 RSS GiB | 诊断 |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| [ci-026567-4c08e11d](ci-026567-4c08e11d.result.json) | `54b5d95f72902034` | 1 | 140.18 | 140.63（7.70 + 132.93） | 8.01 | 比较脚本误用保留字 `matches` |
| [ci-026585-a8da55e8](ci-026585-a8da55e8.result.json) | `c8b6d29b0cc64a78` | 1 | 120.06 | 119.66（7.15 + 112.51） | 8.05 | 比较脚本引用了当前 Lean 不提供的 `when` |
| [ci-026600-5a180380](ci-026600-5a180380.result.json) | `9df449a0e75b492b` | 0 | 127.57 | 127.40（8.31 + 119.09） | 8.10 | 全部 21 字段匹配。两项公理检查只含 Lean 标准公理 |

目标比较在当前工作区独占运行，`actual_arguments` 是 `lean` 和 `AuditTripodCurveInputsTarget.lean` 相对路径。回执的 PSS 和 degraded 标记未知。

## 参考端容器、θ 区域与局部估计

`Iut.LocalTheory.container` 的有限支撑证明显式展开各张量分量的成员关系，再用奇未分歧处的 `logShell_eq_integral`。`Iut.LocalTheory.proj_productRegion` 在同一个张量族上显式定型 `Function.update` 的输入和目标。两段证明沿用已验收的移植稿，补丁落在参考端构建副本。 [参考补丁](reference-compatibility/Iut.Concrete.Container.patch.gz) · [移植稿](../../../../Solutions/Source_ReferenceIutConcreteContainer.lean#L134)

`Iut.ThetaLocalData.thetaPilot` 的有限支撑证明把胶囊索引显式写为 `Fin n`，用 `dif_pos p.2` 裁去素数判定分支，再按各张量分量应用 `thetaComponent_eq_integral`。 [参考补丁](reference-compatibility/Iut.Concrete.ThetaRegion.patch.gz) · [移植稿](../../../../Solutions/Source_ReferenceIutConcreteThetaRegion.lean#L192)

`Iut.ThetaLocalData.logDK_eq_zero` 在分歧处的反证中，显式以 `residueChar_fiberPlace` 将坏特征集的成员关系搬到当前素数。 [参考补丁](reference-compatibility/Iut.Concrete.Invariants.patch.gz) · [移植稿](../../../../Solutions/Source_ReferenceIutConcreteInvariants.lean#L89)

`Iut.LocalTheory.packetVol_scaledIntegral` 使用已定型的 `scaledOne` 作非空见证。有限处 `Iut.TowerArithmetic.vol_finite` 把区域等式经 `congrArg` 传到包体积，无穷处 `vol_infinite` 直接使用同一包体积公式。 [参考补丁](reference-compatibility/Iut.Concrete.LocalEstimate.patch.gz) · [移植稿](../../../../Solutions/Source_ReferenceIutConcreteLocalEstimate.lean#L100)

容器与 θ 区域的六条声明只依赖 `propext`、`Classical.choice` 和 `Quot.sound`。两份 MCP-CI 审查均通过 `no_sorryAx` 检查。 [容器回执](reference-receipts/ci-026722-b0cb3fd3.result.json) · [θ 区域回执](reference-receipts/ci-026744-8bcc1160.result.json)

## 从参考模块实际导入并比较

补齐了 31 个参考产物，缓存使用原工具链及固定 Mathlib 和依赖版本。构造器原声明的文本保持不变。参考覆盖目录在 `CurveFacts.lean` 的 `sqrt_neg_one` 证明中用 `sqrtNegOne'_sq` 与 `pow_two` 直接传递等式。下游源查询直接导入 `Iut.Tripod.CurveFacts`，记录 `explicitSL2Supplier = false`。目标审查比较 14 个参数的完整类型及全部 21 个字段，对照参考端实际调用的 `Iut.Tripod.sl2Image` 与目标端的实现。两侧只依赖 `propext`、`Classical.choice` 和 `Quot.sound`。 [参考构造器](../../../../../refer/iut/Iut/Tripod/CurveFacts.lean#L492) · [参考补丁](reference-compatibility/Iut.Tripod.CurveFacts.patch.gz) · [参考导出](real-source-facts.json.gz) · [目标导出](target-from-real-source-facts.json.gz) · [请求脚本](render-reference-audit.py)

`LocalEstimate` 兼容补丁保持 24 个声明头。有限与无穷处使用包体积等式显式传递到目标。模 ℓ Galois 表示和 SL₂ 像补丁使用固定 Mathlib 的 `AddMonoidHom.domRestrict`。参考端另外审查了局部不变量和 `LocalEstimate` 三个被修改的定理及最终组装，公理只有 Lean 标准公理。 [LocalEstimate 补丁](reference-compatibility/Iut.Concrete.LocalEstimate.patch.gz) · [Galois 补丁](reference-compatibility/Iut.Concrete.ModEllRepGalois.patch.gz) · [SL₂ 补丁](reference-compatibility/Iut.Concrete.SL2Image.patch.gz)

以下列出参考产物闭包的各次编译和审查。耗时及物理内存取对应任务回执。PSS 和 degraded 标记未知。

| MCP-CI 回执 | 输入文件 | 输入 SHA-256 前缀 | 状态（退出码） | 墙钟秒 | CPU 秒（用户态 + 系统态） | 峰值 RSS GiB | 诊断 |
| --- | --- | --- | --- | ---: | ---: | ---: | --- |
| [ci-026634-ed3818b2](reference-receipts/ci-026634-ed3818b2.result.json) | `TheoremTwoOne.lean` | `c933b2f9638a446c` | failed (1) | 4.51 | 4.12（0.17 + 3.95） | 0.37 | 第 6 行，object file '/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-tripod-height-correspondence-20261121/curve-input-assembly/real-source-project/.lake/build/lib/lean/Genl/GeneralPosition/ProofPackage.olean' of module Genl.GeneralPosition.ProofPackage does not exist |
| [ci-026642-89e79057](reference-receipts/ci-026642-89e79057.result.json) | `TheoremTwoOne.lean` | `c933b2f9638a446c` | succeeded (0) | 44.16 | 43.99（3.89 + 40.10） | 3.19 | 无诊断 |
| [ci-026645-c4581396](reference-receipts/ci-026645-c4581396.result.json) | `Model.lean` | `112c37382ca2a1d6` | failed (1) | 167.96 | 163.20（8.85 + 154.35） | 7.78 | 第 152 行，Application type mismatch: The argument |
| [ci-026646-8b6fd075](reference-receipts/ci-026646-8b6fd075.result.json) | `TateTorsion.lean` | `35c4dfa793dc4c9e` | succeeded (0) | 164.46 | 161.03（10.64 + 150.39） | 7.78 | 第 37 行，automatically included section variable(s) unused in theorem `Iut.TateStructure.norm_q_lt_one`: |
| [ci-026647-5eac740c](reference-receipts/ci-026647-5eac740c.result.json) | `LocalTheory.lean` | `e3e4c9db67a8e69f` | succeeded (0) | 152.25 | 145.63（8.51 + 137.12） | 7.79 | 无诊断 |
| [ci-026648-0a40a16b](reference-receipts/ci-026648-0a40a16b.result.json) | `GalCompletion.lean` | `7346dbc613e67dfe` | failed (1) | 146.58 | 143.66（14.43 + 129.23） | 7.79 | 第 285 行，Tactic `rewrite` failed: Did not find an occurrence of the pattern |
| [ci-026649-4c296a49](reference-receipts/ci-026649-4c296a49.result.json) | `TateStructureTransport.lean` | `ec983fc95cc649f5` | failed (1) | 235.48 | 231.65（11.15 + 220.50） | 7.78 | 第 135 行，Type mismatch |
| [ci-026650-f00024cb](reference-receipts/ci-026650-f00024cb.result.json) | `UltrametricSqrt.lean` | `76614cfb3215dfbb` | succeeded (0) | 243.95 | 238.08（6.23 + 231.85） | 7.70 | 无诊断 |
| [ci-026651-cbb129e2](reference-receipts/ci-026651-cbb129e2.result.json) | `ValuationTransfer.lean` | `635e4e777680b539` | failed (1) | 164.43 | 155.84（6.56 + 149.28） | 7.75 | 第 77 行，Type mismatch |
| [ci-026653-19504555](reference-receipts/ci-026653-19504555.result.json) | `Corollary23.lean` | `9850a3e8ec1c3bb7` | succeeded (0) | 160.90 | 156.10（6.65 + 149.45） | 7.75 | 无诊断 |
| [ci-026654-583739a5](reference-receipts/ci-026654-583739a5.result.json) | `SL2Generation.lean` | `7d3fba9b834ec7b4` | succeeded (0) | 161.59 | 155.79（7.54 + 148.25） | 7.74 | 无诊断 |
| [ci-026664-4fc82916](reference-receipts/ci-026664-4fc82916.result.json) | `Container.lean` | `e269ee05fef10bbb` | failed (1) | 194.70 | 192.57（5.78 + 186.79） | 7.74 | 第 174 行，Tactic `rewrite` failed: Did not find an occurrence of the pattern |
| [ci-026667-cb0d7815](reference-receipts/ci-026667-cb0d7815.result.json) | `Model.lean` | `433e347b8c62e928` | succeeded (0) | 141.55 | 138.88（7.37 + 131.51） | 7.76 | 无诊断 |
| [ci-026669-c454e5bc](reference-receipts/ci-026669-c454e5bc.result.json) | `TateIsomorphism.lean` | `dae4a99bdaeb75ad` | succeeded (0) | 143.46 | 131.18（9.37 + 121.81） | 7.80 | 第 227 行，`mul_le_one₀` has been deprecated: No replacement, use constituent lemmas from proof. |
| [ci-026671-036234aa](reference-receipts/ci-026671-036234aa.result.json) | `GalCompletion.lean` | `0114fe3c913f371c` | succeeded (0) | 175.65 | 176.87（14.53 + 162.34） | 7.79 | 第 64 行，`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead |
| [ci-026677-c68a67b4](reference-receipts/ci-026677-c68a67b4.result.json) | `TateStructureTransport.lean` | `650ac313279181b8` | succeeded (0) | 124.68 | 121.27（8.68 + 112.59） | 7.77 | 第 110 行，automatically included section variable(s) unused in theorem `Iut.notMem_of_notMem`: |
| [ci-026678-46425521](reference-receipts/ci-026678-46425521.result.json) | `ValuationTransfer.lean` | `b4a21247944d3678` | succeeded (0) | 122.91 | 120.49（9.04 + 111.45） | 7.77 | 第 68 行，Try this: |
| [ci-026679-f6ce5762](reference-receipts/ci-026679-f6ce5762.result.json) | `TateStructureUnique.lean` | `c85b125ea63666a4` | succeeded (0) | 111.27 | 106.94（7.93 + 99.01） | 7.78 | 第 114 行，automatically included section variable(s) unused in theorem `Iut.negChange_smul_tateCurve`: |
| [ci-026688-b242a919](reference-receipts/ci-026688-b242a919.result.json) | `Torsion.lean` | `30bced78ad1a3fc1` | failed (1) | 124.76 | 124.70（18.28 + 106.42） | 7.79 | 第 96 行，Application type mismatch: The argument |
| [ci-026689-20a5d8cb](reference-receipts/ci-026689-20a5d8cb.result.json) | `TateFamilyGalois.lean` | `71f49caa4aa325f5` | succeeded (0) | 112.91 | 121.24（22.51 + 98.73） | 7.85 | 第 98 行，Try this: |
| [ci-026695-086c067d](reference-receipts/ci-026695-086c067d.result.json) | `LocalAut.lean` | `c13c8a6a5a5b3901` | succeeded (0) | 140.94 | 141.25（9.71 + 131.54） | 7.78 | 第 87 行，automatically included section variable(s) unused in theorem `Iut.map_curveLoc_localAut`: |
| [ci-026696-88a29d06](reference-receipts/ci-026696-88a29d06.result.json) | `TateFamilyOfSplit.lean` | `57a231687beeed0f` | succeeded (0) | 143.64 | 143.21（7.68 + 135.53） | 7.78 | 无诊断 |
| [ci-026697-07e9cf87](reference-receipts/ci-026697-07e9cf87.result.json) | `TateSign.lean` | `f28f320bf8803026` | failed (1) | 128.72 | 127.82（7.89 + 119.93） | 7.78 | 第 297 行，Tactic `rewrite` failed: Did not find an occurrence of the pattern |
| [ci-026703-de62111c](reference-receipts/ci-026703-de62111c.result.json) | `Torsion.lean` | `59f18d3ddb3bdb89` | succeeded (0) | 123.91 | 125.71（17.57 + 108.14） | 7.79 | 第 45 行，automatically included section variable(s) unused in theorem `Iut.AdmissiblePrimeData.bcK_injective`: |
| [ci-026709-46482e3d](reference-receipts/ci-026709-46482e3d.result.json) | `Container.lean` | `adbe5f3a6c58f1ea` | succeeded (0) | 151.14 | 149.25（6.90 + 142.35） | 7.75 | 第 209 行，Try this: |
| [ci-026717-eb10d069](reference-receipts/ci-026717-eb10d069.result.json) | `TateSign.lean` | `1146de0c4b5f0dff` | succeeded (0) | 127.28 | 127.13（9.31 + 117.82） | 7.79 | 第 165 行，Try this: |
| [ci-026722-b0cb3fd3](reference-receipts/ci-026722-b0cb3fd3.result.json) | `ReviewReferenceContainer.lean` | `9e30ce452b59b34b` | succeeded (0) | 151.97 | 149.46（5.76 + 143.70） | 7.63 | 无诊断 |
| [ci-026729-0eb0edb8](reference-receipts/ci-026729-0eb0edb8.result.json) | `ThetaRegion.lean` | `ff4529ff0b041b7d` | failed (1) | 162.80 | 160.52（8.18 + 152.34） | 7.77 | 第 251 行，unsolved goals |
| [ci-026735-8631b0ca](reference-receipts/ci-026735-8631b0ca.result.json) | `SqrtAtBadPlace.lean` | `a89c5873c14a0a3d` | succeeded (0) | 186.22 | 186.07（28.51 + 157.56） | 7.86 | 第 88 行，Try this: |
| [ci-026739-d0fc9fa6](reference-receipts/ci-026739-d0fc9fa6.result.json) | `ThetaRegion.lean` | `c74cdc24c7ce7fad` | succeeded (0) | 154.40 | 153.85（8.84 + 145.01） | 7.80 | 第 256 行，`dif_pos` has been deprecated: Use `dite_eq_left` instead |
| [ci-026743-d16ebfa9](reference-receipts/ci-026743-d16ebfa9.result.json) | `TateFamilyOfTorsion.lean` | `0d496a779fb0e8b4` | succeeded (0) | 140.07 | 141.10（11.89 + 129.21） | 7.81 | 无诊断 |
| [ci-026744-8bcc1160](reference-receipts/ci-026744-8bcc1160.result.json) | `ReviewReferenceThetaRegion.lean` | `a722f553e905bd59` | succeeded (0) | 125.26 | 123.86（4.90 + 118.96） | 7.63 | 无诊断 |
| [ci-026746-a3e2426f](reference-receipts/ci-026746-a3e2426f.result.json) | `Invariants.lean` | `adc5100b9cb75aba` | failed (1) | 124.88 | 125.05（7.40 + 117.65） | 7.79 | 第 172 行，Tactic `rewrite` failed: Did not find an occurrence of the pattern |
| [ci-026753-6b4a089d](reference-receipts/ci-026753-6b4a089d.result.json) | `Invariants.lean` | `09a954a54e20ab83` | succeeded (0) | 102.13 | 102.93（7.03 + 95.90） | 7.79 | 第 65 行，`if_true` has been deprecated: Use `ite_true` instead |
| [ci-026759-f3e480ad](reference-receipts/ci-026759-f3e480ad.result.json) | `LocalEstimate.lean` | `959bf4c0b2c79c1d` | failed (1) | 67.48 | 66.57（4.65 + 61.92） | 7.76 | 第 309 行，Tactic `rewrite` failed: Did not find an occurrence of the pattern |
| [ci-026764-a120ece9](reference-receipts/ci-026764-a120ece9.result.json) | `LocalEstimate.lean` | `31c3c8d46f19132a` | succeeded (0) | 65.46 | 65.10（6.07 + 59.03） | 7.79 | 第 66 行，`dif_pos` has been deprecated: Use `dite_eq_left` instead |
| [ci-026767-9d46e5ab](reference-receipts/ci-026767-9d46e5ab.result.json) | `Main.lean` | `8a357972e406e351` | succeeded (0) | 58.01 | 57.40（4.34 + 53.06） | 7.72 | 无诊断 |
| [ci-026769-5b8a4fd3](reference-receipts/ci-026769-5b8a4fd3.result.json) | `Existence.lean` | `7f13d5adf2ed0b72` | succeeded (0) | 60.29 | 59.78（6.10 + 53.68） | 7.81 | 第 210 行，`dif_pos` has been deprecated: Use `dite_eq_left` instead |
| [ci-026772-34a44f50](reference-receipts/ci-026772-34a44f50.result.json) | `CyclicSubgroup.lean` | `e8bd2657d9d5db53` | succeeded (0) | 77.74 | 72.96（4.81 + 68.15） | 7.73 | 无诊断 |
| [ci-026773-9b3066e4](reference-receipts/ci-026773-9b3066e4.result.json) | `TateInputsConstruct.lean` | `32d99a2aac402f7f` | succeeded (0) | 76.62 | 72.10（5.12 + 66.98） | 7.77 | 无诊断 |
| [ci-026774-c10bbb70](reference-receipts/ci-026774-c10bbb70.result.json) | `CurveOf.lean` | `bbe710b978f8b77f` | succeeded (0) | 75.80 | 71.58（5.76 + 65.82） | 7.79 | 第 91 行，`Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead |
| [ci-026777-56d6f968](reference-receipts/ci-026777-56d6f968.result.json) | `ModEllRepGalois.lean` | `33f4605102e7e82c` | failed (1) | 64.43 | 64.51（6.84 + 57.67） | 7.81 | 第 101 行，Application type mismatch: The argument |
| [ci-026781-ba7c86c2](reference-receipts/ci-026781-ba7c86c2.result.json) | `ModEllRepGalois.lean` | `f3961cd3a2c5f328` | succeeded (0) | 61.24 | 61.05（6.07 + 54.98） | 7.80 | 无诊断 |
| [ci-026783-d2fd6844](reference-receipts/ci-026783-d2fd6844.result.json) | `SL2Image.lean` | `fd69ae35a4f75909` | failed (1) | 58.38 | 58.37（6.28 + 52.09） | 7.81 | 第 145 行，Application type mismatch: The argument |
| [ci-026784-7886ac49](reference-receipts/ci-026784-7886ac49.result.json) | `SL2Image.lean` | `2a49549017f14b3f` | succeeded (0) | 63.47 | 65.25（8.32 + 56.93） | 7.85 | 第 131 行，Try this: |
| [ci-026789-7c8cd418](reference-receipts/ci-026789-7c8cd418.result.json) | `CurveFacts.lean` | `99c2785fdfdfb7a7` | failed (1) | 63.91 | 66.93（11.76 + 55.17） | 7.84 | 第 89 行，Tactic `rewrite` failed: Did not find an occurrence of the pattern |
| [ci-026796-7761eaff](reference-receipts/ci-026796-7761eaff.result.json) | `CurveFacts.lean` | `390b0f1a60251570` | succeeded (0) | 63.37 | 65.35（10.29 + 55.06） | 7.83 | 第 171 行，Try this: |
| [ci-026799-ece9fd78](reference-receipts/ci-026799-ece9fd78.result.json) | `QueryTripodCurveInputsSource.lean` | `f8b9716b565755f2` | succeeded (0) | 69.52 | 68.48（5.70 + 62.78） | 8.19 | 导出 21 个原构造器字段，六项公理输出通过 |
| [ci-026803-5d225cec](reference-receipts/ci-026803-5d225cec.result.json) | `AuditTripodCurveInputsTarget.lean` | `9df449a0e75b492b` | succeeded (0) | 60.86 | 60.53（6.96 + 53.57） | 8.08 | 完整类型和 21 个字段均匹配 |
