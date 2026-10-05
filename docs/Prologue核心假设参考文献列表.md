# Prologue/Core 核心假设参考文献列表

日期：2026-10-05

适用边界：`Prologue-R0`（P0.17 闸门冻结后的 Core）。本文件列出公开
`Prologue/Core` 接口所依赖的来源，不把候选声明、审计 witness 或四条 `Obligations`
构造定理误列为已证明核心数学。

## 1. 来源标记规则

来源栏只使用以下明确写法：

- `mathlib`：Lean/mathlib 已有的类型、定义或定理；必须同时写出具体文件和声明名；
- `JoshiTeich: <论文文件名>`：来自具体的 JoshiTeich 论文索引文件，并附章节、label
  或行号；不使用笼统的 `J` 代替论文名；
- `iut`：只有直接采用参考工程中的代码或 API 时使用。本版 Core 没有 `iut` 来源；
- `D-adapter`：本地组合定义。它必须同时列出所依赖的 `mathlib` 或具体
  `JoshiTeich` 论文，不能单独作为来源。

来源登记不等于证明。`specification` 表示论文中的对象或陈述，`D-adapter` 表示
本地接口组合，`conditional interface` 表示可作为显式参数使用的命题；只有标为
`proved` 的 mathlib 或本地定理才是已经完成的 proof term。

## 2. 冻结环境和主文献

### 2.1 工具链

| 来源 | 固定内容 |
| --- | --- |
| `mathlib` | Lean `v4.35.0-rc3`，mathlib commit `389347a7c1cfa76f6bd5be2ca35d4cb621610ad3` |
| `mathlib` | 本地依赖 `/home/admin-wsl/Coq/mathlib4`，由 `lake-manifest.json` 固定 |

### 2.2 JoshiTeich 主文献

| 具体文献 | 本版 Core 的用途 | 状态 |
| --- | --- | --- |
| `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 2.md` | Tate 参数、`q` 缩放、theta-pilot 原型 | specification |
| `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 2.5.md` | arithmeticoid、finite-place height、different/conductor 接口 | specification |
| `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md` | theta-link、log-shell、packet/hull、Corollary 3.12 的来源陈述 | specification |
| `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 4.md` | different/conductor 的 ramification profile；3.12 之后的主界链只作背景 | specification / 后续阶段 |
| `JoshiTeich: refer/JoshiTeich/index-Arithmetic Holomorphic Structures.md` | untilt、算术全纯结构和 Perfectoid 语义背景 | specification / 背景 |

`refer/iut` 既作为 API 和陈述参考，也允许对局部已证明事实进行逐项移植。本版没有
把 `iut` 作为 Lake 依赖；下表明确标出的声明记录了原文件、行号和本地 mathlib 适配
边界。

## 3. Arithmetic Core

| source-id | Core 声明 | 本地文件 | 来源 | 参考位置 | 状态和边界 |
| --- | --- | --- | --- | --- | --- |
| `JT-M-NF-FINPLACE` | `NumberField.FinitePlace` | `Prologue/Interfaces/Carriers.lean` | `mathlib` | `Mathlib/NumberTheory/NumberField/Completion/FinitePlace.lean` | imported mathlib type |
| `JT-M-RAT-RINGINT` | `Rat.ringOfIntegersEquiv` | `Prologue/Audit/Models.lean` | `mathlib` | `Mathlib/NumberTheory/NumberField/Basic.lean` | 仅用于实际模型和环整数识别 |
| `JT-M-DIFFERENT-IDEAL` | `differentIdeal`、`NumberField.absNorm_differentIdeal` | `Prologue/Arithmetic/Basic.lean` | `mathlib` | `Mathlib/NumberTheory/NumberField/Discriminant/Different.lean` | imported ideal/norm theorem |
| `IUT-COR312-RESIDUE-CHAR` | `Arithmetic.residueChar`、`Arithmetic.residueChar_prime` | `Prologue/Arithmetic/Basic.lean` | `iut` | `refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean`；`ThetaData/Places` residue-characteristic layer | ported local finite-place definition and primality proof; no `iut` import |
| `IUT-COR312-RESIDUE-NORM` | `Arithmetic.absNorm_eq_pow_residueChar` | `Prologue/Arithmetic/Basic.lean` | `iut` | `refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean:84-87` | ported finite-place norm identity; not a q-pilot/global-degree normalization theorem |
| `IUT-COR312-COMPLETION-NORM-ZPOW` | `Arithmetic.completionNorm_eq_residueChar_pow_of_valued` | `Prologue/Arithmetic/Basic.lean` | `iut` | `refer/iut/Iut/Concrete/ThetaLocalConstruct/Ordp.lean:97-103` | ported completion norm expansion over the local `adicCompletion`; the valuation certificate remains an explicit input |
| `JT-ATS-II5-ARITH-DIVISOR` | `FinitePlaceDivisor`、`logDegree` | `Prologue/Arithmetic/Basic.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 2.5.md` | `def:arith-deg-ideloid`，lines 1176--1182 | D-adapter；支持数据，不是 3.12 结论 |
| `JT-ATS-II5-HEIGHT` | `HeightData`、`HeightData.value_nonneg` | `Prologue/Arithmetic/Basic.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 2.5.md` | `def:heights`，lines 1657--1663 | finite-place height interface；archimedean 部分未被伪装补齐 |
| `JT-ATS-IV-RAMIFICATION` | `RamificationProfile`、`differentLog`、`logTotal` | `Prologue/Arithmetic/Basic.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 4.md` | `pr:basic-ramification-data` 1430--1440；`re:diff-rmk` 1496--1502；`pr:tate-divisor` 1542--1563；`th:diff-cond-thm` 1661--1753 | D-adapter；主界链仍属于 Scene2 |

## 4. Perfectoid Core

| source-id | Core 声明 | 本地文件 | 来源 | 参考位置 | 状态和边界 |
| --- | --- | --- | --- | --- | --- |
| `JT-M-PRETILT-UNTILT` | `PreTilt.untilt` 及 reduction/Frobenius 定理 | `Prologue/Perfectoid/Untilts.lean` | `mathlib` | `Mathlib/RingTheory/Perfectoid/Untilt.lean` | imported map and laws |
| `JT-M-FONTAINE-THETA` | `WittVector.fontaineTheta`、`fontaineTheta_teichmuller` | `Prologue/Perfectoid/Untilts.lean` | `mathlib` | `Mathlib/RingTheory/Perfectoid/FontaineTheta.lean` | imported Fontaine theta map and compatibility |
| `JT-ATS-PROLOGUE-PERFECTOID` | `untiltMap`、`thetaMap`、`UntiltingLaws`、`FontaineThetaLaws` | `Prologue/Perfectoid/Untilts.lean` | `D-adapter`；语义背景：`JoshiTeich: refer/JoshiTeich/index-Arithmetic Holomorphic Structures.md`；数学定理：`mathlib` | 本地 canonical law theorems；底层声明见上两行 | explicit law boundary；不是 IUT 复制 |
| `JT-ATS-PROLOGUE-PERFECTOID-DATA` | `PerfectoidData`、`PerfectoidLaws`、`canonicalPerfectoidData` | `Prologue/Perfectoid/Data.lean` | `D-adapter`；依赖 `mathlib` Perfectoid 声明和 `JoshiTeich: refer/JoshiTeich/index-Arithmetic Holomorphic Structures.md` 的语义背景 | `canonicalPerfectoidData_laws` | bundled carrier；构造定理无 `sorry` |
| `JT-ATS-III-PERFECTOID-BRIDGE` | `PerfectoidPlaceData`、`PerfectoidBridgeData`、对应 laws | `Prologue/Interfaces/PerfectoidBridge.lean` | `D-adapter`；`JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`；类型基础为 `mathlib` | 本地字段和 law 结构；精确 bridge 语义仍需 Act1/Act2 复审 | conditional interface；系数同态不能冒充完整桥接定理 |

## 5. Tate 和 theta-pilot Core

| source-id | Core 声明 | 本地文件 | 来源 | 参考位置 | 状态和边界 |
| --- | --- | --- | --- | --- | --- |
| `JT-ATS-II-TATE-PARAMETER` | `TateParameterData`、`TateParameterLaws` | `Prologue/Theta/Tate.lean` | `D-adapter`；`JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 2.md`；补充来源：`JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md` | II `th:tate-parameter-as-a-function` 609--630；III `pr:admissible-lifts-tate-params` 1530--1539 | conditional interface；包含非零和 `0 < norm < 1` 条件 |
| `JT-ATS-II-THETA-PILOT-SCALING` | `ThetaPilotData.scalingIndex`、`ThetaPilotScalingLaws` | `Prologue/Theta/Pilot.lean`、`Prologue/Interfaces/Carriers.lean` | `D-adapter`；`JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 2.md`；主链接来源：`JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md` | II `pr:lift-vals` 820--836；II `pr:teichmuller-lift-B` 968--975；III `th:adelic-theta-link` 1139--1166 | conditional interface；`j^2` scaling 是 Prop，不包含体积下界 |
| `JT-ATS-III-THETA-SCALING-LINK` | `AdelicThetaLinkData.thetaBase`、`AdelicThetaLink.theta_scaling` | `Prologue/Interfaces/Carriers.lean`、`Interfaces/Contracts.lean` | `D-adapter`；`JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md` | `th:adelic-theta-link` 1139--1166 | conditional interface；不包含 Corollary 3.12 |

## 6. Adelic theta-link 的载体和契约

| source-id | Core 声明 | 本地文件 | 来源 | 参考位置 | 状态和边界 |
| --- | --- | --- | --- | --- | --- |
| `JT-ATS-III-DATA-001` | `ThetaPilotData`、`PacketHullData`、`AdelicThetaLinkData` | `Prologue/Interfaces/Carriers.lean` | `D-adapter`；`JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 2.md` 与 `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md` | II `pr:lift-vals` 820--836、`pr:teichmuller-lift-B` 968--975；III `th:adelic-theta-link` 1139--1166 | Type carrier；字段来源已登记，不能计算出 3.12 |
| `JT-ATS-III-ARITHMETIC-LINK` | `AdelicThetaLinkData.heightData`、`ramification`、`qNorm`、`height` | `Prologue/Interfaces/Carriers.lean` | `D-adapter`；`JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 2.5.md` 与 `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 4.md` | 上述 Arithmetic Core 条目 | sourced projections；不是任意的 `K → ℝ` 占位符 |
| `JT-ATS-III-Q-PARAMETER-LOCAL` | `AdelicThetaLinkData.qParameter`、`FirstAxiom.q_parameter_nonzero`、`AdelicThetaLink.valuation_scaling` | `Prologue/Interfaces/Carriers.lean`、`Prologue/Interfaces/Contracts.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md` | `pr:admissible-lifts-tate-params` lines 1530--1539；`th:adelic-theta-link` lines 1139--1166 | Core carrier revision；`qParameter` 是随有限 place 变化的局部 `q_w`，不是全局单值参数 |
| `JT-ATS-III-Q-PARAMETER-REALIZATION` | `AdelicThetaLinkData.ofTateParameters`、`qNormTateCompatibility_of_tateParameters` | `Prologue/Interfaces/Carriers.lean`、`Act1Scene1/QNormTateBridge.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md` | `pr:admissible-lifts-tate-params` lines 1530--1539 | D-adapter；对由 Tate 参数族生成的载体，place/parameter 等式为定义等式；admissible-lift 的存在仍是开放构造义务 |
| `JT-ATS-III-PROLOGUE-INPUT` | `PrologueInputData`、`PrologueInputLaws` | `Prologue/Interfaces/Input.lean` | `D-adapter`；`JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`；底层 Perfectoid 来源为 `mathlib` 和 `JoshiTeich: refer/JoshiTeich/index-Arithmetic Holomorphic Structures.md` | 本地 bundle 组合；无单独 3.12 结论 | explicit input bundle；共同 laws 仍是条件参数 |
| `JT-ATS-III-CONTRACT-001` | `FirstAxiom` | `Prologue/Interfaces/Contracts.lean` | `D-adapter`；`JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 2.5.md`、`refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`、`refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 4.md` | height、q、theta、ramification 字段的组合来源 | conditional interface；不是全局 Lean axiom |
| `JT-ATS-III-CONTRACT-002` | `AdelicThetaLink` | `Prologue/Interfaces/Contracts.lean` | `D-adapter`；`JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md` | `th:adelic-theta-link` 1139--1166；相关 valuation 陈述 1170--1174 | conditional interface；只保留 sourced `j^2` theta scaling、period map 和 normalization；构造列在 `Obligations` |
| `JT-ATS-III-CONTRACT-003` | `ThetaLiftLog` | `Prologue/Interfaces/Contracts.lean` | `D-adapter`；`JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md` | `def:additive-theta-pilot-object` 1492--1502；`le:elem-lemma` 3398--3425 | conditional interface；log-shell relation remains explicit |
| `JT-ATS-III-CONTRACT-004` | `PacketCollationHull` | `Prologue/Interfaces/Contracts.lean` | `D-adapter`；`JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md` | `pr:general-cohomology-set-const` 3261--3271；`th:thetam-construction` 3296--3346 | conditional interface；finite support and nonzero weights only |
| `JT-ATS-III-CONTRACT-005` | `VolumeTransfer` | `Prologue/Interfaces/Contracts.lean` | `D-adapter`；`JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md` | `le:volume-lemma3` 3576--3583；`cor:cor312` 3647--3650 | conditional interface；目标相关性须在 3.12 形式化后复审 |

## 7. 不属于 Core 参考文献的条目

以下条目不能作为 Core 已证明来源：

- `Prologue/Obligations/Constructors.lean` 的四个构造定理。它们分别引用具体的
  `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md` 标签，但状态
  仍为 `open`，并且含已登记的 `sorry`；详见 `SORRY_LEDGER.md`。
- `Prologue/Audit/*` 的满足/违反模型。它们是审计证据，不是生产 Core 假设的来源。
- `Act1Scene1/Boundary.lean` 和 `Act1Scene2/Boundary.lean`。它们是下游边界声明，不
  反向提供 Prologue 数学事实。
- `iut`。本版没有从 `iut` 复制文件、导入模块或接受其数学结论；若未来直接复用
  `iut` 代码，来源栏必须原样写 `iut`，并另行登记原文件、提交和许可证。

### 7.1 被拒的 Candidate

| source-id | 候选声明 | 文件 | 具体来源 | 拒绝理由 |
| --- | --- | --- | --- | --- |
| `JT-ATS-CANDIDATE-FROBENIUS-SQUARE-NORM` | `FrobeniusSquareNormLaw D : Prop`, 即 `∀ i, D.theta.norm (D.theta.frobenius i) = D.theta.norm i ^ 2` | `Prologue/Candidate/FrobeniusSquare.lean` | `JoshiTeich: refer/JoshiTeich/index-Arithmetic Teichmuller Spaces 3.md`, `th:adelic-theta-link` 1139--1166 | 原文给出第 `j` 个分量的 `j^2` 赋值缩放和 Frobenius 稳定性，不给出该跨 Frobenius 的范数平方律；该律与正性、有限性联立会把所有范数压成 `1`，并与非空正 packet/hull 的体积传递冲突。 |

该候选只由 `Prologue/Audit/JointConsistency.lean` 导入作拒绝审计，`Interfaces`、
`Act1Scene1` 和 `Act1Scene2` 均不导入它。Core 中的 Frobenius 字段仍是载体数据，实际
的 `j^2` 关系由 `ThetaPilotScalingLaws` 单独承载。

## 8. 使用和变更规则

本列表与 `ArithmeticTeichmullerSpaces/SOURCE_LEDGER.md` 配合使用：后者是字段级来源
和状态的权威登记，本文件是 Core 假设的可读参考索引。任何 `Prologue/Core` 边界变更
必须遵守 `docs/开发计划.V1Act1.md` §0 的动态边界审计契约，并追加：

1. 具体的 JoshiTeich 论文文件名或 `mathlib` 文件/声明；
2. 新旧 revision、`change-id` 和声明的完整类型；
3. 忠实度、满足/违反模型、证明 owner 和导入影响；
4. 它减少的 Scene1 证明负担以及增加的前置信任负担。

在 `Corollary312` 的完整 Lean 类型、量词和归一化确定前，新的定量下界、`q` 项和
目标特有全局体积结论只能登记为 `Prologue/Candidate`，不能加入本列表的 Core 部分。
