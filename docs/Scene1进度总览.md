# Scene1 进度总览

### 状态判定

| 标记 | 状态 | 使用条件 |
| --- | --- | --- |
| 🟢 | 已闭合 | 本行精确义务已证明，所需实际输入已落实，相关验收已通过 |
| 🔵 | 条件性完成 | 定理及其显式条件已验证，但条件尚未从目标实际数据全部推出 |
| 🟡 | 部分完成 | 已有可引用子结果，仍缺构造、比较、身份等式或整单验收 |
| ⚪ | 未建立 | 尚无满足本行要求的已验收构造或证明 |
| 🔴 | 路线已排除 | 已证明某条具体路线不成立；必须保留排除范围及所用条件 |

“已闭合”只对该行声明的范围有效。局部构造闭合，不自动关闭所属最终闸门。
给定 `InitialThetaData` 后的实际适配，不等于从 arithmetic seed 构造出完整真实模型；
actual carrier 上的定理，不自动成为论文 carrier 上的定理。
必要充分条件已证明，也不表示实际数据满足该条件。

不按文件数、声明数、S1 编号或复选框数计算总完成百分比。
四个闸门的关闭数只表示验收状态，不表示工作量比例或剩余时间。

## 当前结论

| 项目 | 当前值 |
| --- | --- |
| 更新日期 | 2026-11-05（Asia/Shanghai） |
| 状态截点 | 2026-11-05 08:43（Asia/Shanghai）；已有 Lean 串行验收仍在运行，以下只计入截点前有终态的构建 |
| 最近完整验收单元 | `1b19bec`：独立标准 Fréchet Hausdorff completion 上的 Frobenius；14 项公开名称、原 inclusion/坐标相容及正逆范数幂律已通过叶和四入口验收 |
| 已推送版本与验收基线 | 状态截点的 HEAD 为 `1940db3`；`dd225b7` 已推送 bounded 正向/native 链，但初次聚合导入与逐名审计有缺口，完整交付验收正在补正；最近完整验收基线仍为 `1b19bec` |
| 当前工作单元 | 原 bounded localization、全半径 Carrier 和 Fréchet completion 三层 actual↔standard Frobenius 正逆交换图；各最终叶已有成功记录，新增逆映射接口、下游比较及整合补正尚未提交 |
| Scene1 整体 | **未完成；最终闸门关闭 0/4；15 项父义务全部开放** |
| 当前推进位置 | bounded 正向组合已改为四个 private theorem；逆函数法律上移到两侧原载体；全半径经原 inclusion、稠密性与连续性运输，Fréchet 经原 completion→Carrier 观察映射运输；三层正逆交换图均已有叶编译成功记录 |
| 当前验收缺口 | 主入口、漏登名称与来源台账已开始补正；串行脚本正在核验依赖叶，随后重跑 Scene1、Checks、Axioms、ImportAudit。三层比较的最终四入口尚无完整通过结论 |
| 尚未闭合的比较边界 | 三层 Frobenius 比较仍缺整合验收；旧 named `ambientInclusion/toAmbient` 方块及具体 named inclusion 恢复包装仍单独开放；论文 `B`、标量/Galois/Tate-log、period 与 H¹ₑ/BK 身份仍开放 |
| 内存优化结果 | 早期约 100 GiB 的整体 rho 比较已通过 presentation 路线完成值、闭包与完成比较；当前三层 Frobenius 最终叶峰值约 8.65–8.72 GiB，原载体、原映射和范数保留；旧 named ambient 包装仍未验收 |
| 最近完整单元验收 | `1b19bec` 新叶及四入口均退出 0；叶峰值 `5516340 KiB`（5.261 GiB），四入口最大峰值 `9577724 KiB`（9.134 GiB）；14 项公理审计无 `sorryAx` |
| 当前工作树验收 | bounded 正逆、Carrier 正逆、Fréchet 正逆均已有与当前源码匹配的成功叶记录；部分下游记录尚在本机等待归档，修改后的四入口正在排队验收，不能以旧版本入口成功代替 |
| 内存边界 | 单叶验收上限 16 GiB；当前监控停止线 15 GiB，总编译内存上限 100 GiB。低于内存线但超时的构建仍不算通过 |
| 尚未接通的主要连接 | 共同真实 geometry producer、global holomorphoid、论文 Fréchet `B`/ρ-norm、H¹ₑ/BK、paper representatives、跨来源 collation、theta locus/`thetaVolume` 与最终 Corollary 3.12 |
| Prologue 边界 | `R5`；四项 source laws 仍由 Scene1 producer 从共同真实来源证明 |

阅读顺序：先看四个闸门，再看当前路线，最后看最近单元变化与内存记录。
总体义务以[开发计划](开发计划.V1Act1Scene1.md)、[证明义务台账](具有明确参考来源指示的证明义务.md)
和[来源台账](../ArithmeticTeichmullerSpaces/SOURCE_LEDGER.md)为准。已验收单元的资源证据见
[Scene1Witt比较内存.jsonl](Scene1Witt比较内存.jsonl)；当前比较的部分后续运行尚仅保存在本机
`/tmp/abc-rho-builds`，下文单独标明，不计作完整单元验收。

## 四个最终验收闸门

G1–G4 对应[开发计划 §3](开发计划.V1Act1Scene1.md#3-未完成义务按最终闸门分解)。
每行的“已有结果”概括子结果，不表示该闸门已经关闭。

| 闸门 | 当前状态 | 已有结果 | 关闭所需的剩余工作 | 证据入口 |
| --- | --- | --- | --- | --- |
| **G1：目标与归一化冻结** | 🟡 部分完成 | raw/degree-normalized 换算、weighted source sum、grouped volume 会计、actual qProduct lower bound 和条件性最终消费者已有 | 在同一 paper carrier 上冻结 q-term、局部/全局次数、`p*`、`2ℓ`、无穷处项和最终目标，证明 paper normalization 身份 | [计划 G1](开发计划.V1Act1Scene1.md#g1目标符号和归一化) |
| **G2：共同真实来源模型装配** | 🟡 部分完成 | 给定 `InitialThetaData` 后，actual Tate/q-root、局部 tilt/Fontaine/Witt、perfectoid 局部法律及实际与标准 carrier 比较已有 | 从同一 arithmetic seed 产生 geometry、完整 `InitialThetaData/TateFamily`、holomorphoid、period/H¹ₑ/BK 和四项 source laws，完成论文 `B` 身份 | [计划 G2](开发计划.V1Act1Scene1.md#g2共同真实来源和-producer)；[父义务台账](具有明确参考来源指示的证明义务.md) |
| **G3：论文处集与重数会计** | 🟡 部分完成 | actual representatives、prime fibers、selected/omitted mass、Galois fiber 权重和 grouped volume 会计已有 | 识别论文处集和 `L'` representatives，闭合 multiplicity、residue/inertia degree、paper weights 与 mixed-moduli descent | [计划 G3](开发计划.V1Act1Scene1.md#g3论文处集代表和重数) |
| **G4：实际 theta-volume 与最终连接** | 🟡 部分完成 | ordinary-log/Kummer hull、Haar/cost、actual volume 比较、period-ring 和 Tate kernel 的局部链已有 | 接通 H¹ₑ/BK、theta-value、不同 untilt/holomorphoid、paper theta locus 与 `thetaVolume`，在同一归一化下完成最终 proof term | [计划 G4](开发计划.V1Act1Scene1.md#g4论文-theta-locusvolume-和最终-corollary) |

qLogTerm 的字面符号问题按既有决定暂作笔误处理，等待作者回复后再讨论。
本总览不把它列为当前停工项；G1 的其他归一化和来源义务仍保留。

四个闸门关闭后，还须通过[计划 §6 的构建与审计](开发计划.V1Act1Scene1.md#6-构建与审计规则)，
才能宣布 Scene1 完成。单个单元的编译、审计或推送通过，不等于最终验收完成。

## 当前证明路线

下图展示当前构造与待完成连接，不是完整 Lean 导入图。
实线表示已验收的构造连接；虚线表示仍需证明或装配。
绿色只覆盖节点写明的完整验收范围；黄色节点有局部结果，灰色节点尚未验收。

```mermaid
flowchart TD
    S["输入：arithmetic / Tate seed"]
    P["未建立：共同 geometry producer"]
    D["输入：给定 InitialThetaData"]
    T["已闭合：actual tilt 与独立标准 tilt<br/>整数环等价及 local-degree 范数幂律"]
    E["已闭合：bounded Witt 环等价<br/>独立 p-only 标准 rho value"]
    W["已闭合：标准 p-only 全半径<br/>completion carrier"]
    V["已闭合：完整 value_pow<br/>原 bounded 环与原范数；82ea173"]
    Q["已闭合：单半径 completion 等价<br/>双向连续与范数幂律；89f4cc5"]
    U["已闭合：全半径 product 等价<br/>native diagonal 相容"]
    A["已闭合：原全半径闭包 Carrier 等价<br/>双向连续与坐标范数幂律；f904d0b"]
    C0["已闭合：独立标准 Hausdorff 完成<br/>actual↔standard 比较及四入口审计"]
    M["已闭合：p-only 有理半径拓扑<br/>可度量性及 rho 乘法范数"]
    F0["已闭合：标准 bounded rho Frobenius<br/>自同构与 value 幂律"]
    F1["已闭合：固定半径 Frobenius<br/>completion 等价与范数幂律"]
    F2["已闭合：Product 与原闭包 Carrier<br/>标准全半径 Frobenius；四入口通过"]
    F3["已闭合：独立标准 Fréchet Frobenius<br/>原 inclusion、坐标与范数幂律；1b19bec"]
    FC["部分完成：actual↔standard Frobenius<br/>bounded / Carrier / Fréchet 正逆叶均通过<br/>最终四入口整合验收中"]
    F["已闭合：actual period ring<br/>completion、Frobenius、theta 与 Tate kernel"]
    H["已闭合：actual H¹ / ordinary log<br/>hull 与局部定量界"]
    B["未建立：论文 Fréchet B 身份<br/>global holomorphoid、H¹ₑ/BK"]
    R["部分完成：actual representatives<br/>paper 处集、重数与跨来源 collation"]
    L["未建立：paper theta locus<br/>及 thetaVolume 身份"]
    C["待完成：Corollary 3.12<br/>G1–G4 与整体审计"]

    S -.-> P
    P -.-> D
    D --> T
    T --> E
    E --> W
    E --> V
    V --> Q
    W --> U
    Q --> U
    U --> A
    A --> C0
    C0 --> M
    E --> F0
    F0 --> F1
    F1 --> F2
    F2 --> F3
    C0 --> F3
    E -.-> FC
    F3 -.-> FC
    F -.-> FC
    FC -.-> B
    M -.-> B
    D --> F
    D --> H
    V -.-> B
    F -.-> B
    H -.-> B
    D --> R
    B -.-> R
    R -.-> L
    B -.-> L
    L -.-> C

    classDef done fill:#dcfce7,stroke:#15803d,color:#14532d;
    classDef partial fill:#fef3c7,stroke:#b45309,color:#78350f;
    classDef open fill:#f3f4f6,stroke:#6b7280,color:#111827;
    class T,E,W,V,Q,U,A,C0,M,F0,F1,F2,F3,F,H done;
    class R,FC partial;
    class S,D,P,B,L,C open;
```

当前 value 路线已通过局部化 presentation 和系数范数比较证明完整商值幂律。
它没有把旧 named `ambientInclusion` 方块作为已证明前提；该方块仍单独开放。
全半径 product 等价已经限制到两侧原始闭包 `Carrier`，保留完整半径族、原范数和
`ρ ↦ ρ ^ localDeg(w)`；之后两侧原始 Fréchet completion 也已通过环等价、一致等价、
有理半径收敛判据及四入口审计。标准 p-only 有理半径拓扑、可度量性和 rho 乘法范数已闭合。

标准 bounded rho localization 上的 Frobenius 自同构及 `ρ ↦ ρ^p` 值幂律已通过四入口。
`035da86` 将其延伸到固定半径完成、全半径 Product 和原闭包 Carrier，三叶、四入口及
48 项逐名审计均已通过。`1b19bec` 又通过原 completion/Carrier 等价，在原标准 Fréchet
completion 上构造连续环自同构，证明正逆 inclusion、坐标和范数幂律，并完成四入口验收。

当前 actual↔standard 比较已越过此前具体参数专门化的阻塞。bounded 正向证明以四个
private theorem 保存 choice action、naturality、comparison composition 和最终组合；
bounded 逆向证明消费上游保存的两侧原逆函数法律。全半径 Carrier 用通用 inclusion 方块、
稠密性与连续性延拓；Fréchet 用原 completion→Carrier 映射的相容性和单射性运输。
三层正逆交换图都有成功叶记录，原映射、载体、范数及半径重参数均保留。

`dd225b7` 的初次四入口虽然退出 0，但聚合未导入最终 bounded 链，审计也漏登部分名称。
该缺口已记录在来源台账，当前正在补齐并重跑最终验收。因此当前三层比较仍标为部分完成；
局部 Frobenius 相容也不关闭论文 `B`、holomorphoid 或 H¹ₑ/BK 身份。

### 关键子结果与缺口

| 路线位置 | 状态 | 已证明范围或验收缺口 | 所属闸门／证据 |
| --- | --- | --- | --- |
| 条件性最终定理 | 🔵 条件性完成 | `cor312_of_scene1_data` 与 canonical actual-hull consumer 已有证明；完整真实输入、来源法律和 paper identity 仍须产生 | G1/G2/G4；[计划 §2.3](开发计划.V1Act1Scene1.md#23-scene1-条件性消费者与会计) |
| Actual Tate/q-root 与局部会计 | 🟢 已闭合 | 给定数据后的 q 参数、q-order、根、有限支撑和 raw/degree-normalized 恒等式已有 | G1/G3；[Scene1 聚合](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1.lean) |
| Actual representatives 与处集会计 | 🟢 已闭合 | actual carrier 内的 representative image、prime support、finite fibers、omitted mass 和 grouped volume 已有；paper 身份另计 | G3；[计划 §2.3](开发计划.V1Act1Scene1.md#23-scene1-条件性消费者与会计) |
| Actual period-ring 与 Tate kernel | 🟢 已闭合 | actual bounded Witt/ρ-norm、completion、Frobenius、theta、twisted integral representatives、full Tate kernel 与实际正合列已有 | G2/G4；[period-ring 边界](#period-ring-路线的边界) |
| Actual H¹、ordinary log 与 hull | 🟢 已闭合 | actual rational H¹、带 integral 来源的 Kummer 像、ordinary log、tensor hull、Haar/cost 和实际定量界已有 | G4；[父义务台账](具有明确参考来源指示的证明义务.md) |
| 标准 tilt 与 integer-ring bridge | 🟢 已闭合 | 标准 fraction field 的范数、完备性、代数闭性、拓扑比较和整数环 bridge 已有；比较保留 local-degree 范数幂律 | G2；`GeometricTiltNorm.lean`、`IutInitialThetaPadicTiltTopology.lean` |
| 独立标准 bounded Witt rho value | 🟢 已闭合 | 仅依赖 p 的 expansion、localization、presentation-independent value、指定半径范围内有限性、零点分离和素数校准已提交 | G2/G4；`7e40f65`；[标准 value](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/PadicWittRhoValue.lean) |
| 标准 p-only 全半径 completion carrier | 🟢 已闭合 | 由单半径标准 completion 组装全半径产品 carrier，含坐标范数、稠密嵌入、分离性和坐标收敛；叶、Scene1、Checks、Axioms、ImportAudit 已通过 | G2/G4；`b2ac96f`；[全半径 carrier](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/PadicWittAllRadiusCompletion.lean) |
| 实际↔标准全半径 product 等价 | 🟢 已闭合 | 沿 `ρ ↦ ρ ^ localDeg(w)` 组装各半径 completion 等价，给出全乘积双向连续环等价；原 diagonal 相容随后通过 native 接口接通 | G2/G4；`213751d`、`f904d0b`；[product 等价](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaPadicWittRhoProductEquiv.lean) |
| 原 actual↔standard 全半径闭包比较 | 🟢 已闭合 | 原 `Carrier` 间的环等价、双向连续、homeomorphism、原 inclusion 的 diagonal 底层值公式、双向 evaluate 与坐标范数幂律均已验收；没有替换共同闭包 | G2/G4；`f904d0b`；[原载体比较](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaPadicWittAllRadiusComparison.lean) |
| 独立标准全半径 Source 与 Hausdorff completion | 🟢 已闭合 | p-only 原一致结构、分离性、完成与原闭包比较、连续环同态延拓及唯一性已通过叶和四入口；来源与资源已归档 | G2/G4；[Source](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/PadicWittFrechetSource.lean)、[完成比较](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/PadicWittFrechetComparison.lean)；`3a60371` |
| Actual↔standard 全半径完成比较 | 🟢 已闭合 | 双向连续环等价、一致等价、homeomorphism、原 inclusion 底层值、半径相容、范数幂律与收敛判据已通过四入口；保留实际与标准原载体 | G2/G4；[实际完成比较](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaPadicWittFrechetComparison.lean)；`3a60371` |
| 独立 p-only 半径拓扑与可度量性 | 🟢 已闭合 | 有理半径夹逼完整 `(0,1)` 范数族；标准 carrier、Source 与 Hausdorff completion 的原拓扑可度量，actual 比较消费该独立判据 | G2/G4；`fdfb6b7`；[拓扑模块](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/PadicWittFrechetTopology.lean) |
| 独立标准 rho 乘法范数 | 🟢 已闭合 | 原 bounded `value`、fixed-radius Source/Completed 范数和 all-radius `coordinateSeminorm` 的精确乘法等式均已证明并通过四入口 | G2/G4；`959d595`；[乘法模块](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/PadicWittRhoMultiplicativeNorm.lean) |
| 独立标准 bounded rho Frobenius | 🟢 已闭合 | 原 bounded localization 上的 p-only Frobenius 环自同构、ambient/presentation 相容及 `ρ ↦ ρ^p` 的 value/realValue 幂律已通过四入口 | G2/G4；`fabaa1b`；[bounded Frobenius](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/PadicWittRhoFrobenius.lean) |
| 标准固定半径与全半径 Frobenius 延拓 | 🟢 已闭合 | 固定半径 completion 等价、范数幂律、全半径 Product 自同构与原 all-radius Carrier 限制已通过三叶、四入口和 48 项逐名审计 | G2/G4；`035da86`；[fixed-radius](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/PadicWittRhoFrobeniusCompletion.lean)、[Product](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/PadicWittProductFrobenius.lean)、[Carrier](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/PadicWittAllRadiusFrobenius.lean) |
| 独立标准 Fréchet Frobenius | 🟢 已闭合 | 原 Hausdorff completion 上的连续环自同构、正逆 inclusion/坐标相容和 `ρ ↦ ρ^p` 范数幂律；14 项逐名审计、叶及四入口通过，仅依赖 p 与素性 | G2/G4；`1b19bec`；[Fréchet Frobenius](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/PadicWittFrechetFrobenius.lean) |
| Actual↔standard bounded Frobenius | 🟡 部分完成 | 原 bounded 正向/native 交换律及原逆映射交换律均有成功叶记录；初次聚合覆盖和漏名已发现并补正，最终整合验收待完成 | G2/G4；[当前三层比较与验收边界](#当前三层比较与验收边界) |
| Actual↔standard 全半径 Carrier Frobenius | 🟡 部分完成 | 原 inclusion 方块经稠密性与连续性延拓，正逆交换图叶已通过；保留原 Carrier、环等价和范数；尚缺整单验收 | G2/G4；[Carrier 比较叶](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaPadicWittAllRadiusFrobeniusComparison.lean) |
| Actual↔standard Fréchet Frobenius | 🟡 部分完成 | 经原 completion→Carrier 映射及单射性证明正逆交换图，叶已通过；原 Hausdorff completion 不变；尚缺整单验收 | G2/G4；[Fréchet 比较叶](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaPadicWittFrechetFrobeniusComparison.lean) |
| 共享 carrier 比较与 `ambientEquiv` | 🟢 局部闭合 | 系数、field-Witt 和 fraction ambient 等价已有 proof term；相关叶有低于 16 GiB 的成功记录，范围不含 bounded ambient inclusion 方块 | G2/G4；`d4a05cd`；[ambient 等价叶](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaPadicWittRhoAmbientEquiv.lean) |
| 原 inclusion 后的系数范数幂律 | 🟢 叶验收通过 | `coefficient_inclusion_norm_pow` 已在默认预算下通过独立叶编译；新接口直接保存两侧 inclusion 后的系数范数 | G2/G4；[系数范数叶](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaPadicWittRhoCoefficientNorm.lean) |
| 分子、分母与商值幂律 | 🟢 叶验收通过 | `numerator_value_pow`、`denominator_value_pow`、`quotient_value_pow` 分别通过默认预算叶编译；最终局部化值定理也已在 `82ea173` 通过 | G2/G4；[商值叶](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaPadicWittRhoQuotientValue.lean) |
| 两侧 localization presentation 值公式 | 🟢 叶验收通过 | actual arbitrary-contraction 与 standard Away presentation 的值公式已有成功编译记录 | G2/G4；[presentation 叶](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittRhoLocalizationPresentation.lean) |
| Actual→standard 完整 rho 幂律 | 🟢 已闭合 | 原 bounded `ringEquiv` 上的 `value_pow` 在默认 heartbeat 下通过，保留原范数、标准独立收缩元和半径 rho^localDeg；聚合、审计和推送已完成 | G2/G4；`82ea173`；[最终值声明](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaPadicWittRhoValuePow.lean) |
| 旧 named `ambientInclusion` / `toAmbient` 比较 | ⚪ 未建立 | 已测试的具体交换图仍未通过；ambient 环等价和新系数范数叶不能代替该命名映射的相容证明 | G2/G4；[计划中的构建边界](开发计划.V1Act1Scene1.md#2026-11-03named-ambient-inclusion-的内核阻塞已复核) |
| 原标准 named inclusion 的具体恢复包装 | ⚪ 未建立 | 在具体 `ringFun` 像上恢复原标准 named inclusion 的独立点态包装仍有 Kernel timeout；p-only 上游的全函数 diagonal 身份和原闭包比较已经验收，两者范围须区分 | G2/G4；[来源台账](../ArithmeticTeichmullerSpaces/SOURCE_LEDGER.md)的原闭包比较边界 |
| 论文 `B`、H¹ₑ/BK 与 global holomorphoid | ⚪ 未建立 | actual/local 及 p-only 载体构件尚未识别为论文要求的 carrier、拓扑、子空间及比较映射；bounded Frobenius 也未替代该身份 | G2/G4；[父义务台账](具有明确参考来源指示的证明义务.md) |
| Paper representatives、theta locus 与 `thetaVolume` | 🟡 部分完成 | actual 会计和 hull 可复用；paper carrier、跨来源 transport、locus/volume 身份及最终共同装配仍缺 | G2/G3/G4；[计划 §3](开发计划.V1Act1Scene1.md#3-未完成义务按最终闸门分解) |

“已闭合”只覆盖本行的精确范围。已提交的 bounded、单半径、全半径 product、原闭包与
Fréchet completion 单元及独立标准 Frobenius 延伸均有聚合和审计证据；当前 actual↔standard
Frobenius 单元尚未完成整单验收。这些局部结果不关闭论文 `B` 身份或父义务。
`integralKummerSubmodule` 是带 integral 来源的有理像载体；特定像类非零不表示一般 integral H¹
系数映射单射。actual ordinary log 仍须与论文 Bloch–Kato log 比较。

### Period-ring 路线的边界

| 层次 | 状态 | 已有结果 | 仍保留的目标 |
| --- | --- | --- | --- |
| Actual bounded Witt 与 ρ-norm | 🟢 已闭合 | 有界 Witt ring、半径 norm、乘法性和 completion 构造已有 | 与论文对象、来源及归一化的身份 |
| 全半径 completion、Frobenius 与 theta | 🟢 已闭合 | actual completion、各半径求值、Frobenius、theta、Tate-log 和 principal-unit period 局部链已有 | 论文 `B`/ρ-norm、holomorphoid 与 H¹ₑ/BK 身份 |
| Twisted integral 代表与 Tate kernel | 🟢 已闭合 | 指定实际 twisted 解可缩放到原始 `A_inf`；full Tate kernel、唯一实际 `ℚₚ` 标量分类与正合列已有 | 论文 carrier、topology 及来源比较 |
| Actual ρ=1 `B⁺` candidate | 🟢 已闭合 | actual 单位球 candidate 的 Frobenius 自同构和 `PadicInt` 结构已有 | 论文 `B⁺` 标记、Galois 作用、global holomorphoid 与标量相容 |
| 环带指数延拓 | 🟡 部分完成 | overlap 法律、闭区间有界逼近和条件性消费者已有 | 精确 Witt 代表或全半径延拓；固定正内半径的单位界不足以推出整性 |
| Actual / standard bounded rho 比较 | 🟢 已闭合 | 原环等价上的完整 `value_pow`、单半径 completion、双向连续和完成范数幂律已验收 | 旧 named ambient 方块和具体原 inclusion 包装仍单独开放 |
| 原全半径闭包 carrier 比较 | 🟢 已闭合 | p-only carrier、半径重参数、product 等价、native diagonal 相容及原闭包等价均已验收 | 标量/Frobenius/period transport 和论文 `B` 身份 |
| 全半径 Hausdorff completion 比较 | 🟢 已闭合 | 独立标准完成、通用延拓与 actual 比较已通过四入口；独立 p-only 可度量性随后单独通过 | 论文 `B`、标量/Frobenius/period 与 H¹ₑ/BK 身份仍开放 |
| 独立标准 Frobenius 全链 | 🟢 已闭合 | bounded、固定半径、Product、原闭包至原 Fréchet completion 的自同构和相应幂律已分单通过四入口 | actual 相容、标量/Galois/Tate-log/period 与论文 `B` 身份另计 |
| Actual↔standard Frobenius transport | 🟡 部分完成 | 原 bounded、全半径 Carrier、Fréchet 三层正逆交换图均已有成功叶记录 | 补齐来源与逐名登记，完成覆盖全部新证明的四入口验收；论文身份另计 |

Joshi II 的原型为 `B_{C_p^flat,ℚₚ}`、`φ=p`；Joshi III 也允许 `B_E`、tensor 和局部化变体。
选择哪一种载体仍须证明它与实际 holomorphoid、theta-value 来源及权重相容。
当前 p-only 链没有自动给出一般 `E` 的 ramified Witt、Lubin–Tate 或 `φ=π` 身份，
也不能因此断言论文只允许一般 `E` 路线。来源见[计划中的论文载体变体边界](开发计划.V1Act1Scene1.md#2026-11-04原生-completion-coe-接口与论文载体变体边界)。

### 已排除路线：避免重复投入

| 具体路线 | 状态与排除范围 | 当前保留方向 | 证据 |
| --- | --- | --- | --- |
| 从任意抽象 AG/TG 接口自动产生 universal geometry producer | 🔴 反模型排除仅凭现有抽象字段无条件产生 witness；不评价真实 orbicurve | 为真实 geometry 证明 cartesian、covering 和 local 来源法律 | [计划 2026-10-23](开发计划.V1Act1Scene1.md#2026-10-23任意无约束-agtg-的统一-producer-反模型) |
| Actual contracting q-root 直接充当旧 theta base | 🔴 q-root 范数小于 1，与旧 period/normalization/transfer 的非负 logVolume 要求冲突 | 另一 theta lift、different untilt 或 negative-log cost | 计划 N1；S1.243/S1.321 |
| Signed Haar log-volume 直接等同旧 `VolumeTransfer` | 🔴 正长度 ordinary-log hull 的 signed log-volume 为负，排除指定直接身份 | 证明 actual `-log(volume)` cost 的 paper identity | 计划 N2；S1.321/S1.322/S1.406 |
| 指定 representative certificates 与 reference q-pilot equality 联合使用 | 🔴 已证明指定证书组合与 selected/reference strict gap 不相容 | 从 paper source 重审 representatives、omitted mass 和 degree/weight | [计划 2026-10-29](开发计划.V1Act1Scene1.md#2026-10-29canonical-degree-one-representative-certificate-的乘积不相容性) |
| 固定正内半径上的单位界直接推出 `A_inf` 整性 | 🔴 实际环带反例排除只凭该单位界取得 integral 代表；不排除附带 Frobenius 方程的识别 | 使用实际 Frobenius 方程，或构造全半径延拓 | [计划 2026-10-30](开发计划.V1Act1Scene1.md#2026-10-30固定环带的双侧单位界不足以推出-a_inf-整性) |

这些结果只排除表中具体路线，不构成 Corollary 3.12 的反例。
内核超时和超内存属于构建失败证据，不标为数学上的“路线已排除”。

## 最近单元变化与内存记录

| 单元 | 新增结果 | 验收状态 | 保留边界 |
| --- | --- | --- | --- |
| `82ea173`：bounded rho 值比较 | 经系数范数、numerator、denominator、quotient 和原局部化 presentation，证明原环等价上的完整 `value_pow` | 🟢 已验收并推送 | 旧 named ambient 方块另计 |
| `f904d0b`：原全半径闭包比较 | 标准 diagonal 身份上移到 p-only 源叶，product transport 限制到两侧原 `Carrier` | 🟢 已验收并推送 | 具体旧 named inclusion 包装及论文身份仍开放 |
| `3a60371`：全半径完成比较 | 独立标准 Source/Hausdorff completion、原闭包比较、通用延拓及 actual↔standard 完成等价 | 🟢 四入口验收并推送 | 额外结构相容与论文来源身份另计 |
| `fdfb6b7`、`959d595` | 独立 p-only 有理半径拓扑、可度量性及原 rho 范数的精确乘法律 | 🟢 四入口验收并推送 | 不关闭论文载体身份 |
| `fabaa1b`：标准 bounded Frobenius | 原标准 localization 自同构及 value/realValue 的 `ρ ↦ ρ^p` 幂律 | 🟢 四入口验收并推送 | 不自动给 actual 比较 |
| `035da86`：固定/全半径 Frobenius | 原 fixed-radius completion、Product、闭包 Carrier 上的延拓与组装 | 🟢 三叶、四入口及 48 项逐名审计通过并推送 | actual 相容及论文身份另计 |
| `1b19bec`：标准 Fréchet Frobenius | 在原 Hausdorff completion 上构造连续环自同构，兼容原 inclusion、坐标与正逆范数幂律 | 🟢 叶、四入口及 14 项逐名审计通过并推送 | actual 相容、标量/Galois/Tate-log、period/BK 与论文身份仍开放 |
| `dd225b7`：bounded 正向/native Frobenius | 四个 theorem 边界组合原 choice 自然性，再接回原 bounded 函数 | 🟡 叶已通过并推送；整合验收补正中 | 初次四入口未覆盖最终链且漏登名称；旧四入口成功不能作为完整交付验收 |
| 当前工作树：三层正逆 Frobenius 比较 | bounded 逆函数法律上移；Carrier 用 inclusion/稠密性；Fréchet 用原观察映射；三层最终叶均通过 | 🟡 叶已通过；最终四入口验收中 | 部分来源/资源待归档，修改后的聚合与审计尚无完整终态 |

已验收的完整值目标为：令 `d = localDeg(w)`、`B = InitialThetaPadicBoundedWittComparison`，
对 `ρ ≠ 0`、`ρ ≠ ⊤` 及原 actual bounded Witt 元素 `x`，证明

```text
PadicWittRhoValue.value p ρ (B.ringEquiv D w x) ^ d
  = InitialThetaWittRhoValue.value D w (ρ ^ d) x
```

原全半径闭包和 Fréchet completion 上的相应范数幂律也已分别验收。
最新标准 Fréchet Frobenius 的坐标与范数公式为

```text
R_(ρ^p)(φ(x)) = φ_ρ(R_ρ(x))
‖R_(ρ^p)(φ(x))‖ = ‖R_ρ(x)‖^p
```

这里 `R` 是原标准 completion 的 `radiusMap`，`φ_ρ` 是已验收的固定半径完成等价；
正逆公式均已证明。三层 actual↔standard 比较的交换公式也已有成功叶记录，最终整合验收仍待完成。

### 当前三层比较与验收边界

令 `E` 为对应层原 actual→standard 比较，`φₐ`、`φₛ` 为两侧原 Frobenius。
当前 bounded、全半径 Carrier 和 Fréchet 三层均有以下正逆公式的成功叶记录：

```text
E (φₐ x) = φₛ (E x)
E (φₐ⁻¹ x) = φₛ⁻¹ (E x)
```

native 函数接口直接调用原等价，并保存原函数身份；通用方块的前提由同一实际数据上的
已证公式消除，没有增加自由比较证书。当前路线将原先集中在具体声明头部的转换负荷
移到上游函数法律及下游纯函数组合。

| 层次 | 已通过的具体范围 | 当前剩余验收 |
| --- | --- | --- |
| bounded localization | 正向/native law；标准逆函数左逆律、actual 逆函数右逆律；由正向律推出原逆映射交换 | 最新源接口已重编译通过，须由最终四入口覆盖 |
| 全半径原闭包 Carrier | inclusion 方块；原稠密像上的相容延拓；正逆交换图 | 最终叶有准确双 SHA 成功记录；串行脚本核验相关依赖并归档 |
| Fréchet Hausdorff completion | 原 completion→Carrier 桥接；原标准观察映射单射性；正逆交换图 | 最终叶有准确双 SHA 成功记录；须完成聚合和逐名公理审计 |
| 整单交付 | 聚合导入和已发现漏登名称已补入工作树；36 项已推送模块的来源登记已补 | 新增模块来源/资源归档、最终四入口、公理输出复核、提交与推送 |

旧的 concrete header、直接重写和 bundled 包装多次在约 11.6 GiB 触发 Kernel
deterministic timeout；对应目标现已有上述替代证明。旧失败仍保留为资源证据，
不作为当前数学缺口，也不据此确定 Kernel 实现错误。旧 named ambient 方块仍是独立目标。

### 受控构建与资源证据

构建使用 CPU `0-13`、`LEAN_NUM_THREADS=14`、Lean `-j1`、热缓存和默认 heartbeat，
每 0.5 秒采样进程组 RSS；15 GiB 是监控停止线，16 GiB 是单叶验收上限，
总编译内存上限为 100 GiB。GiB 按 `KiB / 1048576` 换算。
资源值只覆盖对应源码和依赖版本的那次运行；无终态、超时或报错均不计为通过。

最近完整验收基线 `1b19bec` 的五次记录均退出 0，已归档到
[资源 JSONL](Scene1Witt比较内存.jsonl) 和[来源台账](../ArithmeticTeichmullerSpaces/SOURCE_LEDGER.md)：

| 构建记录 label | 范围 | 耗时 | 峰值 RSS（KiB / GiB） | 结果 |
| --- | --- | --- | --- | --- |
| `standard_frechet_frobenius_leaf` | 标准 Fréchet Frobenius 叶 | 72.6 秒 | `5516340` / 5.261 | 通过 |
| `standard_frechet_frobenius_scene1` | Scene1 聚合 | 150.5 秒 | `9368324` / 8.934 | 通过 |
| `standard_frechet_frobenius_checks` | Checks | 160.8 秒 | `9577724` / 9.134 | 通过 |
| `standard_frechet_frobenius_axioms` | Axioms | 163.0 秒 | `9553636` / 9.111 | 通过 |
| `standard_frechet_frobenius_importaudit` | ImportAudit | 161.5 秒 | `9440740` / 9.003 | 通过 |

该基线的 14 项公理审计并集仅为 `propext`、`Classical.choice`、`Quot.sound`，
没有 `sorryAx`。这份结论不替代当前工作树的最终公理审计。

### 当前单元：已结束的代表性运行

“工作树 JSONL”表示已归档但尚未提交；“本机”表示记录目前仍在
`/tmp/abc-rho-builds/<label>.json`，同目录保存日志与 RSS 样本。
以下成功记录的源码 SHA256 已与当前对应源码核对；Carrier/Fréchet 的双 SHA 一致且
`source_changed_during_run=false`。最终脚本会按顺序核验并归档，不能将表中单叶成功合称四入口通过。

| 构建记录 label | 范围 | 耗时 | 峰值 RSS（KiB / GiB） | 结果／记录位置 |
| --- | --- | --- | --- | --- |
| `actual_standard_bounded_frobenius_concrete_transfer_v7_header` | 四个 theorem 边界后的具体 choice 自然性 | 271.7 秒 | `9113820` / 8.6916 | 通过；已提交 JSONL |
| `actual_standard_bounded_frobenius_comparison_native_v8` | 原 bounded 正向比较 | 185.1 秒 | `9103464` / 8.6817 | 通过；已提交 JSONL |
| `frobenius_final_leaf_IutInitialThetaPadicBoundedWittFrobeniusLaws` | 当前源码 bounded 正向/native law | 271.7 秒 | `9073572` / 8.6532 | 通过；工作树 JSONL |
| `frobenius_verified_leaf_PadicWittFrobeniusNativeFunction` | 标准原逆函数及左逆律 | 99.5 秒 | `5507852` / 5.2527 | 通过；工作树 JSONL |
| `frobenius_verified_leaf_IutInitialThetaBoundedWittFrobeniusNativeInverse` | actual 原逆函数及右逆律 | 173.6 秒 | `9086824` / 8.6659 | 通过；工作树 JSONL |
| `frobenius_verified_leaf_IutInitialThetaPadicBoundedWittFrobeniusInverse` | bounded 逆交换图 | 256.8 秒 | `9113712` / 8.6915 | 通过；工作树 JSONL |
| `allradius_frobenius_generic_square_dense_inverse_v2` | 原全半径 Carrier 正逆交换图 | 223.4 秒 | `9117024` / 8.6947 | 通过；本机，待归档 |
| `actual_standard_frechet_frobenius_generic_square_v1` | 原 Fréchet 正逆交换图 | 290.0 秒 | `9138028` / 8.7147 | 通过；本机，待归档 |

| 历史失败记录 label | 耗时 | 峰值 RSS（KiB / GiB） | 终态与后续 |
| --- | --- | --- | --- |
| `actual_standard_bounded_frobenius_concrete_transfer_pieces_v6` | 242.6 秒 | `12167816` / 11.604 | Kernel timeout，退出 1；v7 theorem 拆分后通过 |
| `frobenius_final_leaf_IutInitialThetaPadicBoundedWittFrobeniusInverse` | 385.7 秒 | `12166360` / 11.6027 | Kernel timeout，退出 1；逆函数法律上移后通过 |
| `actual_standard_bounded_frobenius_equiv_1m` | 358.3 秒 | `15740828` / 15.012 | memory_limit，退出 −15；局部预算提升已撤回 |

早期监控器曾将部分输出产物摘要误作源码 SHA。受影响的 32 条记录已改记为
`unverified_monitor_digest` 并保留说明；耗时、RSS 和退出码仍是原运行记录，
但这些摘要不能用于精确源码验收。新监控记录包含运行前后源码 SHA 及源码变化标记。

### 历史资源边界

| 单元或尝试 | 已记录结果 | 判定 |
| --- | --- | --- |
| 早期整体 rho comparison | `104733916 KiB`，约 99.88 GiB，退出码 137 | 未验收 |
| 早期 field bridge | `111356192 KiB`，约 106.20 GiB，退出码 137 | 未验收 |
| 早期 field-Witt inclusion | `44895852 KiB`，约 42.82 GiB，退出码 137 | 未验收 |
| 拆分和函数接口调整后的 coefficient、field-Witt、`ambientEquiv` 等叶 | 对应成功运行低于 16 GiB | 局部叶已通过，不覆盖旧 named ambient 方块 |
| 新 presentation 路线的最终 `value_pow` | `9098108 KiB`，8.677 GiB，136.3 秒 | `82ea173` 已验收推送 |
| 原全半径闭包及完成比较 | 比较叶峰值约 8.7 GiB，均已通过四入口 | `f904d0b`、`3a60371` 已验收推送 |
| 旧 named ambient inclusion 与具体 named inclusion 包装 | 多次约 11.6 GiB 触发 deterministic timeout；提高预算的诊断曾触及 15 GiB 停止线 | 仍未验收；保留为独立缺口 |

因此，早期约 100 GiB 的整体比较已由低内存路线完成其值比较、闭包和完成目标；
三层 Frobenius 相容已有成功叶记录，但旧命名包装和新单元整合验收尚未全部解决。
早期运行摘要见[开发计划的资源边界记录](开发计划.V1Act1Scene1.md#2026-11-02rho-比较的-kernel-资源边界与载体接口调整)，
其监控条件与后来受控运行不同。一次不限内存诊断授权已使用，后续继续遵守单叶上限。

## 后续顺序

1. 完成当前串行依赖叶核验、四入口与逐名公理审计，补齐新模块来源和资源归档，提交并推送三层 Frobenius 比较单元。
2. 按[计划 §5](开发计划.V1Act1Scene1.md#5-执行顺序)回到共同真实 geometry producer；已找到真实除点覆盖的 valuation-inertia generator equality 候选入口，尚未实现或验收。后续仍须证明真实惯性商、覆盖及 étale π₁ 身份。
3. 完成 holomorphoid、论文允许的 `B` 或变体、标量/Galois/Tate-log/period 身份及 H¹ₑ/BK 比较。
4. 接通 paper representatives、multiplicity、mixed-moduli descent、G1 归一化和 G4 theta-volume，完成最终 Corollary 3.12 与整体审计。

旧 named ambient 方块和具体 named inclusion 包装继续单独登记。
已通过的值、闭包、完成比较及三层 Frobenius 叶证明不自动关闭这些包装或任何父义务。
