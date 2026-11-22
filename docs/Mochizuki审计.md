# `refer/Mochizuki` Source Audit

日期：2026-10-18

范围：审计 `refer/Mochizuki` 中的 IUT III、IUT IV 和 *Arithmetic Elliptic Curves in General Position*，重点核对 IUT III Corollary 3.12、其 IUT IV 的使用方式，以及 Joshi III 对应的具体陈述。若 Mochizuki 与 Joshi 的目标语义发生冲突，本项目按用户指定采用 Joshi 的陈述。

## 结论

IUT III **确实给出了 Corollary 3.12 的字面不等式**，所以“文献里完全没有具体句子”说得过强。它以 Theorem 3.11 的情形为前提，把左边定义为 Θ-pilot object 可能像的并集之 holomorphic hull 的 procession-normalized mono-analytic log-volume，把右边定义为 q-pilot object 的相应 log-volume，并断言

`-|log(Θ̲)| ≥ -|log(q̲)|`，等价地，`C_Θ ≥ -1`。

但这不是一个脱离 IUT 术语体系即可直接翻译成当前 Lean 类型的有限处集公式：陈述依赖 Theorem 3.11 的 theta-value 多重径向表示、Kummer 同构、Ind1–Ind3、Definition 3.8 的 pilot objects、Remark 3.9.5 的 holomorphic hull，以及 Remark 3.1.1 / Proposition 3.9 的归一化体积。IUT IV Theorem 1.10 进一步计算这些 log-volumes，但它仍以“处于 IUT III Corollary 3.12 的情形”为前提，并增加 good-reduction 假设。

对本工程而言，Joshi III 的 `th:thetam-construction`、`th:moccor-Mochizuki-form2` 和 `cor:cor312` 给出了应采用的可追溯目标表达：在明确的 `L,C,X,L'`、Initial Θ-data 和充分大的奇素数 `ℓ` 假设下，theta loci 的体积下界由 `w ∈ underline V^oss` 上的 `|q_w^(1/2ℓ)|^(ℓ*)` 乘积控制，再按 Mochizuki 的符号约定翻译为 Corollary 3.12。这个公式可以作为目标 statement；其完整 Lean 实现仍需要项目内逐项给出 carrier、locus、体积、权重和 q-factor 的定义与证明。

本次核对没有发现 IUT III/IV 与 Joshi III 在最终不等式的数学方向上构成明确矛盾。两者的展示层级、体积归一化和处集记账方式有差异；遇到这些差异时，项目目标采用 Joshi III 的明确定义和符号翻译，不从 Mochizuki 的简写或 IUT IV 的重新归一化推导另一套目标。

## 原文证据

| 来源 | 位置 | 对项目的证据与边界 |
| --- | --- | --- |
| IUT III | `Inter-universal_Teichmuller_Theory.md`，§3 Corollary 3.12，约行 4239–4287 | 原文先写明“Suppose that we are in the situation of Theorem 3.11”，然后定义 Θ 与 q 的 procession-normalized mono-analytic log-volume，并给出 `-|log(Θ̲)| ≥ -|log(q̲)|`。因此有明确的数学句子；其变量含义由此前的术语和构造承载，不能把这行单独当作全部形式化接口。证明约行 4287 起继续分解为步骤，依赖 Theorem 3.11 及此前的 log-volume / Kummer 结构。 |
| IUT III | 同文档，Theorem 3.11、Definition 3.8、Remark 3.1.1、Proposition 3.9、Remark 3.9.5 | 分别承载 theta-value loci 的构造、Θ/q pilot objects、按 `j ∈ F_l*` 平均的权重、packet/procession log-volume 和 holomorphic hull。Corollary 3.12 的句子需要这些定义共同解释；其 indeterminacies (Ind1)–(Ind3) 明列在 Corollary 的 Θ 一侧。 |
| IUT IV | `Inter-universal_Teichmuller_Theory_4.md`，§1 开头及 Theorem 1.10，约行 121、557 起 | §1 称其工作是对 IUT III Corollary 3.12 中 Θ-pilot log-volume estimates 给出更显式版本。Theorem 1.10 假设处于 Corollary 3.12 的情形，另要求若干 good-reduction 条件，并用 different、conductor、q-divisor 等算术量给出估计。它是 Corollary 的应用/显式化，不是对 Corollary 3.12 全部构造定义的替代。 |
| IUT IV | 同文档，Remark 1.7.1，约行 415–435 | 明确区分 IUT III normalized weights 相对于非归一化 log-volume 的定义与 IUT IV Proposition 1.4(i) 的 normalized log-volume；改用新的权重，并把指标写成“not necessarily distinct”的 `w_α` 集合。这是重要的 multiplicity 证据：项目不能只凭去重后的处集就认定与 packet-normalized volume 等价。 |
| Joshi III | `Arithmetic Teichmuller Spaces 3.tex`，§Initial Θ-data，label `ss:theta-data-fixing2`，行 1023 起 | 明确列出额外输入：`L/L_mod` Galois、`C[6]` 定义域、`ℓ ≥ 5` 且 `ℓ ∤ [L:L_mod]`、mod-`ℓ` 表示像包含 `SL₂`、`L'` 为表示核的固定域，以及 `V_Lmod ≅ underline V` 的双射。故“充分大的 ℓ”不能脱离这些选取和全局 Initial Θ-data 来理解。 |
| Joshi III | 同文档，`th:thetam-construction`，行 3296–3343 | 对每个 `z ∈ tildeΣ_{L'}` 构造 Mochizuki prime-strips、Hodge-theaters、Galois cohomology classes 及其 Bloch–Kato 对数像，并定义 theta-values locii 为相应集合的凸闭包和后续映像。该结果自称本质上对应 IUT III Theorem 3.11。其证明仅称其余断言可由既有事实组装，因此依赖链仍需按相邻定义审计。 |
| Joshi III | 同文档，`th:moccor-Mochizuki-form1/2`，行 3430、3617 起 | `form1` 给 theta-locus 的 sup-norm 下界；`form2` 给 `Vol(theta_M^I)` 和 `Vol(theta_J^I)` 的下界，右边都是 `∏_{w∈underline V^oss} |q_w^(1/2ℓ)|^(ℓ*)`。`form2` 的证明具体调用 holomorphic hull 与 convex closure 的对应、volume lemmas，以及构造出的 theta locus。 |
| Joshi III | 同文档，`cor:cor312`，行 3647–3650 | 明确把 `form2` 翻译为 Mochizuki Corollary 3.12 的符号约定：`-(1/ℓ*) |logVol(theta_M^I)| ≥ -Σ_{p,w∈underline V^oss_p ≠ ∅} log |q_w^(1/2ℓ)|_{L'_w}`。该行是本工程优先采用的 Corollary 目标文本；`p` 的分组、`w` 的代表和 `L'_w` 范数均按其前置定义解释。 |

## 形式化接口审计

| 闸门 | Mochizuki 可提供的来源 | Joshi 目标与仍需本工程定义的部分 |
| --- | --- | --- |
| G1：不等式与归一化 | IUT III 给出 `-|log Θ| ≥ -|log q|`；IUT IV 说明 procession weights 与 packet-normalized log-volumes，并重新表达权重。 | 以 Joshi `cor:cor312` 的负号和 `1/ℓ*` 系数为准。必须在同一 volume 对象上证明绝对值、log-volume、负号及缩放系数的关系；不能把 IUT IV 的重新归一化权重无证明地替换进去。 |
| G2：真实输入 | IUT III 的输入是 Theorem 3.11 背景下的 initial Θ-data、Hodge-theaters、prime-strips、Kummer / log-Kummer correspondences 和 theta-pilot objects。 | Joshi `ss:theta-data-fixing2` 使部分域扩张、torsion 和处集选择更显式。Lean 仍需表示这些数据的联合实例及相关结构定理；原文叙述不是现成的 Lean 实例。 |
| G3：处集与重数 | IUT III 的 q-pilot 由 bad-place q-parameters 产生；IUT IV 的重归一化明确允许有重复的 `w_α`。 | 采用 Joshi `underline V^oss`、`underline V^oss_p`、`L'_w` 和 `q_w` 的语义。需证明支持集、扩域上方的处、代表选择、重复次数及有限乘积/求和与项目 carrier 一致。仅有 support 等价不足以推出带重数公式。 |
| G4：theta locus 与体积 | IUT III 将 Θ-locus 描述为可能像的并集的 holomorphic hull，并以 multiradial representation 为载体。 | 采用 Joshi 构造的 Galois-cohomology/Bloch–Kato theta loci、凸闭包/holomorphic-hull 对应及 `form2` 的 volume 下界。项目需分别实现 locus 构造、紧性/有限性、volume 单调性和对 q-pilot 的比较；不可把“形式化句子已有”误作这些接口已在 Lean 中闭合。 |

## 冲突处理与可移植性

1. **目标语义固定为 Joshi。** 若 IUT III/IV 的隐含归一化、重复计数或符号约定与 Joshi III `th:moccor-Mochizuki-form2` / `cor:cor312` 不同，项目按 Joshi 的公式和定义继续；Mochizuki 来源只记录为历史对应和术语来源。
2. **当前核对到的是精确度差别，不是已证实的最终不等式冲突。** IUT III 与 Joshi 的最终下界方向一致。IUT IV 的权重条目说明 multiplicity 不能忽略，但仅凭该条目尚不足以断言两种最终公式相矛盾；项目应保留 Joshi 选择的 carrier 和记账方式。
3. **“没有具体形式化句子”需拆成两种含义。** 若指原文没有任何具体陈述，此说不成立：IUT III Corollary 3.12 有明确不等式，IUT IV Theorem 1.10 也给出附加假设下的显式估计。若指 Mochizuki 没有直接给出本工程所需 carrier、有限求和、重复处代表和 Lean 可消费的 q-product 接口，则原文该推论确实不是自足的；Joshi III 的 `form2`/`cor:cor312` 是更直接的目标规格。
4. **来源不是 proof term。** `refer/Mochizuki` 和 `refer/JoshiTeich` 是论文文本，不是可导入 Lean 的证明对象。Joshi 的陈述可以冻结目标 statement，但项目仍需证明或显式保留每个前提，包括 theta-data 的存在与选择、Bloch–Kato 构造（如目标路径使用它）、体积/hull 关系、权重求和和 q-factor accounting。

## 审计判定

`refer/Mochizuki` 对项目有直接来源价值：它确立 Corollary 3.12 的原始 log-volume 语义，并说明 Theorem 1.10 如何在额外条件下把该估计展开为算术不等式。但它单独不足以确定当前工程的 Lean-level finite-place API。Joshi III 提供了应优先形式化的具体版本和更明确的 theta-locus 构造链。当前 G1–G4 中，文献足以锁定目标方向及主要术语来源；carrier / multiplicity 对齐、volume 适配和完整输入模型仍属工程义务。本审计不改变这些义务的开放状态。
