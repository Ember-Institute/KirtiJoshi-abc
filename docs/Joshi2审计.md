# `refer/Joshi2` Source Audit

日期：2026-10-18

范围：本审计覆盖 `refer/Joshi2` 下的 9 份文献，目标是判断它们能否为当前 `ArithmeticTeichmullerSpaces` 项目的 Scene1 提供可追溯来源、接口设计依据或负面证据。本文件是只读 source audit，不修改 Lean 代码、Prologue 边界或 `SOURCE_LEDGER.md`。

## 结论

`refer/Joshi2` 对项目有用，但不能单独闭合 Scene1。最有价值的来源是：

1. `On Mochizuki's idea of Anabelomorphy and its applications.tex` 的 Tate divisor、perfectoid/untilt、theta-value、global Frobenius 和 holomorphoid 讨论。
2. `Algebraization of Mochizuki's anabelian variation of ring structures, perfectoid geometry and formal groups.tex` 的 monoid formal group、固定乘法结构的加法变形和 `A_inf` 类比。
3. `joshi-mochizuki-FAQ.md` 的作者路线说明，尤其是 holomorphoid、untilt、Tate parameter 变化、global Frobenius 和 product formula 的关系。

这些文献大多是 TeX/Markdown 论文或说明材料，不是本工程可直接导入的 Lean proof source。它们不能直接证明：

- `InitialThetaData/TateFamily` 的完整真实联合实例；
- 论文 `V_p^oss`、`\underline V^oss`、`L'` representative、重数和 fiber mass accounting；
- `H^1_e`、Bloch--Kato logarithm、crystalline/Frobenius 子空间；
- actual packet/hull volume 与论文 `thetaVolume` 的等式；
- 最终 Corollary 3.12 的无条件 proof term。

因此，本审计支持继续保留当前 `Prologue-R5` 和四个开放闸门。它没有发现可以在独立工程原则下直接从 `refer/Joshi2` 移植、并立即关闭某个最终闸门的形式证明。

## 与四个闸门的对应

| 闸门 | `Joshi2` 可提供的来源线索 | 仍缺的形式义务 | 判断 |
| --- | --- | --- | --- |
| G1：目标与归一化 | Tate divisor 的 `ord_w(q_w)`、扩域下相对分歧指数、`[M:Q]` 归一化；作者对 `-abs(log Vol)` 符号的说明 | raw、degree-normalized、paper-normalized 三层在同一 carrier 上的完整等式；q-term 符号最终冻结 | 可用于 source audit；不能直接成为 theorem |
| G2：真实来源模型 | untilt、Fargues--Fontaine 点、Tate parameter 函数、holomorphoid、global Frobenius 的概念链 | 实际 `PerfectoidBridgeLaws`、period、different/untilt、H¹ₑ/BK 和同一 `InitialThetaData` 的联合实例 | 强相关背景；无可直接移植 proof |
| G3：论文处集与重数 | Tate divisor/reduced Tate divisor 的处集语义和扩域公式；Tate curve uniformization | `V_p^oss`/`L'` 来源等式、代表选择、重数、residue-degree 和 q-pilot fiber mass-one | 有助于澄清目标；不能闭合 accounting |
| G4：theta-volume 与 Corollary | theta values 与局部 cohomology extension class 的关系；不同 untilt 的 Tate parameter 比较；global averaging 的动机 | theta-value locus 的 Lean 构造、packet/hull 到 `thetaVolume` 的定量身份、最终 target | 有设计价值；不能替代 theorem |

## 高相关文献

### Anabelomorphy、Tate 参数和 perfectoid 结构

文件：`refer/Joshi2/On Mochizuki's idea of Anabelomorphy and its applications.tex`

关键位置：

- §1 引言，约 407--422 行：anabelomorphy、固定 Galois 群和变化的 ring/arithmetic structure。
- 约 433--448 行：amphoric 与 non-amphoric quantity 的区分；特别是 discriminant/different、crystalline property、`H^1_f`/`H^1_e` 和 `L`-invariant 的不同状态。
- §1503 起：split multiplicative reduction 的 abelian/Tate uniformization；定理 `th:anabelomorphy-abelian-var` 和 Tate curve corollary。
- §1516--1557：Tate divisor、reduced Tate divisor、`ord_w(q_w)` 和扩域下 `ord_w(q_w)=e_{w|v} ord_v(q_v)`。
- §1565 起：idelic Tate divisor 和跨多个处的 averaging。
- §1626 起：anabelomorphic connectivity of number fields。
- §2082--2148：固定 tilt 的 untilts、perfectoid fields/spaces 和 Fargues--Fontaine 视角。
- §2343 起：theta values、局部 `H^1(G_{K_v}, Q_p(1))` extension classes、mixed Hodge 类比。

对当前项目最重要的可引用内容是 Tate divisor 的局部/全局归一化。它支持我们把以下对象分开记录：

- 局部 Tate order `ord_w(q_w)`；
- 相对分歧指数对扩域 order 的影响；
- 全局除以 `[M:Q]` 的 normalized arithmetic degree；
- 由处集选择造成的 reduced divisor 与完整 divisor 的区别。

这与项目已经证明的 completion norm、relative ramification、inertial/residue degree accounting 相容，并可作为 G1/G3 的文献依据。然而该文件没有给出项目所需的有限 subtype equivalence、`L'` representative map、weighted fiber sum 或 `thetaVolume` proof。它还明确展示了某些量并非 amphoric；因此不能把“Galois 群相同”当作完整 valuation、different 或 theta-volume 身份的证明。

### Monoid formal groups、untilts 和 `A_inf` 类比

文件：`refer/Joshi2/Algebraization of Mochizuki's anabelian variation of ring structures, perfectoid geometry and formal groups.tex`

关键位置：

- 摘要，约 182--205 行：universal monoid formal group、`p`-perfect monoid 的 Frobenius、Lubin--Tate formal groups、perfectoid untilts 和 global `A_inf` 类比。
- §1，约 259--305 行：固定乘法 monoid、变形加法 law 和 ring structure 的 algebraization 动机。
- §308 起：monoid formal group 的定义。
- §426 起：universal `M`-formal group theorem。
- §598 起：Frobenius morphism。
- §691 起：perfectoid rings/fields/Huber pairs 的应用。
- §750 起：number-field analog of Fontaine's `A_inf` 的构想。

它对项目的主要用途是接口设计：如果未来需要表示“固定 multiplicative carrier、变化 additive/ring structure”，该文献说明应把 monoid/action 放在显式结构中，而不能把某个加法结构隐藏成全局实例。它也为 untilt/period 数据应作为候选对象而非 Prologue Core 假设提供了设计依据。

它不能推出当前 Scene1 的 local q-factor、paper representative 或 packet/hull estimate。将 universal formal group theorem 直接加入 Core 会把一个广泛的代数化背景误当成 3.12 的具体 analytic law，违反动态边界审计契约。因此本项目不从该文献新增 Core/Candidate 字段。

### FAQ：路线图而非形式来源

文件：`refer/Joshi2/joshi-mochizuki-FAQ.md`

关键位置：

- Questions 1--14，约 11--115 行：Teichmuller analogy、untilts、Tate parameter 和 arithmetic holomorphic structure。
- Questions 23--25，约 169--190 行：global Frobenius/log-Link、全局 valuation scaling、product formula glue。
- Questions 33--37，约 235--300 行：holomorphoid、Fargues--Fontaine point、Tate parameter family、`A_inf`/Galois cohomology 两条 theta-value 路线。
- Questions 38 起，约 313--323 行：Arithmetic Teichmuller Space、global Frobenius 和 product-formula-as-a-period 的定位。

FAQ 对 source audit 很有帮助，因为它明确区分：

- 固定 elliptic curve 与改变 arithmetic holomorphic structure；
- 单个 untilt 的局部 Tate parameter 与多个 untilt 的 family；
- product formula 作为 global glue；
- Galois cohomology 路线与 `A_inf`/Fargues--Fontaine 路线。

但 FAQ 没有自足的 theorem statement/proof。它不能作为 Lean 定理的唯一来源，也不能把 `unitsSubspace` 改名为 H¹ₑ/BK。

## 中相关文献

### Fargues--Fontaine 反例文献

文件：`refer/Joshi2/The Absolute Grothendieck Conjecture is false for Fargues-Fontaine Curves.tex`

用途：负面来源审计。它提醒我们不能从 fundamental group 或一般 anabelian 数据推出过强的 Fargues--Fontaine curve scheme identity。对 G2 的 useful lesson 是：必须明确区分 topological/fundamental-group 信息、valued-field structure、untilt 和 scheme/period data。

不能提供当前项目的 theta-value、BK 或 volume proof。它适合作为未来“不可由 anabelomorphy 自动推出”的负面证据，不应进入当前 Scene1 导入图。

## 低相关文献：Frobenius、不稳定向量丛和 opers

以下五份文件研究正特征曲线上的 Frobenius pullback、Harder--Narasimhan stratification、opers、Quot-schemes 和 dormant operatic loci：

- `refer/Joshi2/Hitchin–Mochizuki_morphism,_opers_and_Frobenius-destabilized_vector_bundles_over_curves.md`：引言和 §2--§3 明确对象是正特征曲线、p-curvature、opers 和 Hitchin--Mochizuki morphism。
- `refer/Joshi2/Opers_of_higher_types,_Quot-schemes_and_Frobenius_instability_loci.md`：摘要和 §3--§8 研究 higher-type opers、Frobenius instability strata、Quot-schemes；部分结果明确是 conjectural。
- `refer/Joshi2/The_Degree_of_the_Dormant_Operatic_Locus.md`：§3--§7 研究 dormant `SL(r)` opers 的 scheme degree 和 Quot-scheme。
- `refer/Joshi2/moduli-of-vector-bundles-on-curves-in-positive-characteristics.md`：摘要和 §1 研究 genus-2、characteristic-2 的 rank-2 vector bundles。
- `refer/Joshi2/on-vector-bundles-destabilized-by-frobenius-pull-back.md`：摘要和 §4 研究 Frobenius destabilization、Harder--Narasimhan polygons 和 pre-opers。

这些材料可以解释 global Frobenius 的几何类比，但当前 Scene1 工作在数域有限处、Tate curves、perfectoid/untilt、Kummer/log 和 theta-volume accounting 上。它们没有可直接移植的代码，也没有当前四个闸门所需的 finite-place/q-factor/volume theorem。它们应留在背景参考或未来 Scene2 的文献范围，不应作为当前 G2/G4 的证明来源。

## 可移植性审计

| 来源类型 | `refer/Joshi2` 证据 | 独立工程结论 |
| --- | --- | --- |
| Lean proof | 目录中只有 `.tex` 和 `.md`，没有 Lean 源文件或 `.olean` | 无代码可移植 |
| 形式化 theorem API | 文献给出数学叙述和外部引用，但未给本项目的 carrier/type/proof term | 必须在本工程重新声明、证明或标记为条件输入 |
| H¹ₑ/BK | `On Mochizuki...` 讨论 `H^1_f/H^1_e` 的 amphoricity，但没有本项目所需的 BK comparison construction | 不能用作 H¹ₑ/BK proof source |
| Perfectoid/untilt | 给出 tilt/untilt、Fargues--Fontaine 和 Tate parameter 的概念链 | 可用于接口和 source audit；不能替代 `PerfectoidBridgeLaws` |
| Tate divisor | 给出 order、relative ramification 和 normalized arithmetic degree 的文献公式 | 可作为 G1/G3 来源；仍需本工程 finite-sum proof |
| Global Frobenius | FAQ 和 anabelomorphy 文献说明其作用和 geometric analogy | 不能直接构造本工程 global Frobenius 或 theta-volume consumer |
| Universal formal group | 有明确 theorem，但属于独立的代数化主题 | 只能作为 Candidate/interface 设计背景，不应晋升 Core |

## 对当前项目的建议

1. 将 `On Mochizuki...` 的 Tate divisor 段作为 G1/G3 的文献核对依据，特别核对 `[M:Q]`、relative ramification 和 reduced support 的方向。
2. 将其 perfectoid/untilt 和 theta-value 段与当前 `PerfectoidBridgeLaws`、`ThetaLiftLog`、Kummer/log shell 结构逐字段对照；若不能给出完整输入输出类型，就保留为 open obligation。
3. 不从 `Joshi2` 增加 Prologue/Core 假设，不把 monoid formal group universal property 当作 3.12 的 analytic law。
4. 不把 FAQ 或论文叙述当成 H¹ₑ/BK、`V_p^oss`/`L'`、或 `thetaVolume` 的 proof term。
5. 若未来实现这些来源，优先建立窄的 Scene1/Derived source adapters，并逐条记录论文位置、量词、carrier、依赖和未证明部分；不要把 `refer/Joshi2` 直接加入 Lean import graph。

## 审计结论

`refer/Joshi2` 改善了项目的来源理解，尤其是 Tate divisor 的全局归一化、untilt/Tate parameter 的语义和 global Frobenius 的作用；它也提供了几个重要的负面边界：anabelian/fundamental-group 信息不能自动恢复所有 valued-field、different、crystalline 或 theta-volume 数据。

在当前证据下：

- G1：可加强来源审计，但不能冻结最终归一化；
- G2：可完善接口语义，但真实 untilt、period、H¹ₑ/BK 仍 open；
- G3：Tate divisor 公式有帮助，但 `V_p^oss/L'` representative accounting 仍 open；
- G4：theta-value 和 perfectoid 讨论有路线价值，但 packet/hull 到论文 `thetaVolume` 仍 open。

本审计没有改变 Prologue revision，也没有改变四个形式冻结闸门状态。
