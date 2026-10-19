# Scene1 进度总览 2

已完成证明只保留结论；未完成义务和负面证据保留详细范围、条件和证据。

### 状态判定

| 标记 | 状态       | 使用条件                                                 |
| ---- | ---------- | -------------------------------------------------------- |
| 🟢   | 已闭合     | 本行精确义务已证明，所需实际输入已落实，相关验收已通过   |
| 🔵   | 条件性完成 | 定理及其显式条件已验证，但条件尚未从目标实际数据全部推出 |
| 🟡   | 部分完成   | 已有可引用子结果，仍缺构造、比较或身份等式               |
| ⚪   | 未建立     | 尚无满足本行要求的已验收构造或证明                       |
| 🔴   | 路线已排除 | 已证明某条具体路线不成立；必须写出排除范围及所用条件     |

“已闭合”只对该行声明的范围有效。局部构造闭合，不自动关闭所属最终闸门。
条件性反例不记为无条件反例；一个实际数据适配器不记为完整真实满足模型。
不按文件数、声明数或 S1 编号计算总完成百分比。

## 当前结论

| 项目 | 当前值 |
| --- | --- |
| 更新日期 | 2026-10-19（Asia/Shanghai） |
| 最近完成的数学单元 | preferred algebraic closures 间的 rational Kummer 运输：从自然 Tate 运输导出实际 ℤₚ 基变换单位，用该单位修正 rational 系数，证明 standardMap 交换及同一底域元素的根塔类身份；`LocalKummerRationalClosureTransport.lean` |
| 数学证明基线 | S1.503 及未编号的 actual tilt／Fontaine／B_dR、finite/arch/adelic packet、shell／hull、Haar-product 下界、normalized-log collation、de Rham θ-fiber/hull、marked H¹ 与 closure Kummer 运输；以 [SOURCE_LEDGER](../ArithmeticTeichmullerSpaces/SOURCE_LEDGER.md) 的已验收声明为准 |
| 最近已推送单元 | `afe6ccd`：rational closure Kummer 运输；此前 `3437315` 完成自然 Galois／Tate／integral Kummer closure 运输，`0c970a2` 完成显式 marking 下的原连续 H¹ 运输；更新前 `HEAD=origin/main=afe6ccd` |
| Scene1 整体 | **未完成；最终闸门关闭 0/4** |
| 数学工作状态 | 同一 D 的 actual tilt、Fontaine 主核、primitive-adic 完备 B_dR、de Rham θ-fiber 求值、有限/无限处 container／shell／hull、三层 log-volume 和实际 Haar-product 下界均有已验收构造；ambient H¹ 已有 marked 运输及固定底域 closure 的 integral/rational 自然运输 |
| 当前推进位置 | 在已验收 rational closure 运输上，接入 principal-unit image、p-saturation、ordinary log／inverse exp 和实际 Initial Θ-data 类；两个新叶仍在制。随后仍须从论文 holomorphoid 产生标注，接通 H¹ₑ/BK、paper carrier／权重、theta locus／volume 与 `CanonicalActualHull.AnalyticInput` |
| 尚未接通的主要连接 | H¹ₑ/BK/crystalline、跨 holomorphoid／untilt 的标注生产者及 collation、period/Perfectoid 的论文共同来源、论文代表处与权重、已构造无穷处贡献在最终目标中的处理、actual hull/container 到 paper thetaVolume 的身份、最终 3.12 |
| Prologue 边界 | R5；本轮 Core 假设增量 0，未改既有定理类型或独立依赖 |
| 最新工程验收 | rational closure 新叶、Checks.SceneBounds、Axioms.SceneBounds、Act1Scene1 四项通过；17/17 新声明逐名核对，3017 个打印声明通过公理白名单；542 个可达本工程模块的静态导入边界通过。在制两个叶不计入这些数值 |

阅读顺序：先看四个闸门，再看当前路线和关键子结果，最后查看未完成义务与负面证据。
本总览不以单元数量计算总完成率，详细待办见[具有明确参考来源指示的证明义务](具有明确参考来源指示的证明义务.md)。

## 四个最终验收闸门

G1–G4 依次对应[开发计划 §3](开发计划.V1Act1Scene1.md#3-scene1-形式冻结闸门)的四项要求。
每行的“已有结果”概括子结果，不表示该闸门已经关闭。

| 闸门 | 当前状态 | 已有结果 | 关闭所需的剩余工作 | 证据入口 |
| --- | --- | --- | --- | --- |
| **G1：目标与归一化冻结** | 🟡 部分完成 | general-degree raw/degree-normalized 与 weighted paper-source 等式；local raw→paper normalization、finite/arch tuple 维数消去、统一 adelic log-volume 与实际 Haar-product 身份已证 | 在最终 paper carrier 上统一 raw q-term、paper q-term、权重和 thetaVolume；保留 squareAverage 与无穷处贡献，证明最终系数及符号 | S1.489–503；`PaperQNormalizationBridge.lean`；`IutInitialThetaAdelicFamilyLogVolume.lean`；负面证据 |
| **G2：真实来源模型装配** | 🟡 部分完成 | 同一 D 的 q-root／tilt／Fontaine／B_dR 来源链、ambient H¹ 坐标与 Tate-log、marked 连续 H¹ 及固定底域 closure 的 integral/rational Kummer 运输已证 | 共同产生论文 holomorphoid／thetaScaling／period／Perfectoid 来源，构造跨来源标注、H¹ₑ/BK 与 log 比较；固定底域 closure 同构尚不足以关闭此项 | `0c970a2`、`3437315`、`afe6ccd`；实际几何来源与 Kummer 来源台账 |
| **G3：论文处集与重数会计** | 🟡 部分完成 | selected source→actual section Voss→canonical section-link 的 carrier 等式；代表纤维质量、weighted regrouping、selected/omitted 缺陷及全部 finite/arch tuple 权重已证 | 识别独立 Scene1 link 与论文 `V_p^oss/L'` representatives，闭合 relative degree、代表重数和 mixed-moduli descent；保留缺陷及 degree 因子 | S1.471–500；`IutInitialThetaSelectedQRootLinkAccounting.lean`；`PaperQRepresentativeFiberMass.lean` |
| **G4：实际 theta-volume 与最终连接** | 🟡 部分完成 | actual normalized-log witness／factor orbit／hull 身份、finite/adelic source／hull／shell 体积比较、真实 Haar-product 与带 squareAverage 下界、de Rham θ-fiber 到旧 hull 的身份已证；actual cost→Corollary consumer 保留显式条件 | 论文 theta locus/BK/untilt 来源、全部所需不定性、paper hull/volume 与代表权重身份、最终无穷处处理、完整 RHSData 及最终 3.12 仍缺 | `IutInitialThetaWitnessHullHaarProduct.lean`、`IutInitialThetaNormalizedLogCollation.lean`、`IutInitialThetaLogCollationOrbit.lean`、`IutInitialThetaDeRhamFiberHull.lean` |

qLogTerm 符号问题按用户决定暂作笔误处理，等待作者回复后再讨论。
本总览不把该问题列为当前停工项；G1 的其他归一化和来源义务仍保留。

四个闸门关闭后，还须通过[计划 §4 的最终审计和推送验收](开发计划.V1Act1Scene1.md#4-审计和推送验收)，才能宣布 Scene1 完成。
单个单元的检查和推送通过，不等于该最终验收已完成。

## 当前证明路线

下图展示已经建立的两条实际构造链及其尚缺的汇合关系，不是完整 Lean 导入图。
实线表示已有构造或条件性消费者，虚线表示尚待证明的来源比较。

```mermaid
flowchart TD
    D["同一实际 InitialThetaData D"]
    K["已证：ambient H¹ 坐标与 Tate-log<br/>marked H¹、固定底域 closure Kummer 运输"]
    E["已证：actual tilt、Fontaine 主核<br/>primitive-adic B_dR、θ-fiber 求值"]
    Q["已证：full/VBad q-root<br/>局部法律、纤维 q-pilot 会计"]
    H["已证：ordinary-log hull、Haar、cost"]
    A["条件性：CanonicalActualHull.data<br/>固定 hullVolume、qProduct 与 Corollary consumer"]
    F["已证：指定因子 qroot 的 j² 区域<br/>有限自同构 orbit、正有限 Haar"]
    P["已证：全部有限/无限处 tuple packet<br/>adelic source/hull/shell、有限支撑"]
    L["已证：三层 degree-weighted log-volume<br/>实际 Haar-product、带 squareAverage 下界"]
    B["待证：H¹ₑ/BK、theta、period<br/>跨 untilt collation、Perfectoid 来源"]
    R["待证：paper 代表处与权重<br/>最终无穷处处理、paper hull/volume 身份"]
    C["待完成：同一对象的最终 Corollary 3.12"]
    D --> K
    D --> E
    E --> F
    D --> Q
    Q --> H
    H --> A
    Q --> F
    F --> P
    P --> L
    K -.-> B
    B -.-> A
    F -.-> R
    L -.-> R
    H -.-> R
    B -.-> R
    R -.-> C
    A -.-> C
    classDef done fill:#dcfce7,stroke:#15803d,color:#14532d;
    classDef conditional fill:#dbeafe,stroke:#2563eb,color:#1e3a8a;
    classDef open fill:#f3f4f6,stroke:#6b7280,color:#111827;
    class D,K,E,Q,H,F,P,L done;
    class A conditional;
    class B,R,C open;
```

### 关键子结果与缺口

| 路线位置 | 状态 | 已证明范围或验收缺口 | 所属闸门／证据 |
| --- | --- | --- | --- |
| Tate、连续 H¹ 和 Kummer 基础 | 🟢 已闭合 | 实际 Tate 基、连续 cocycle、标准 H¹ 系数比较、root descent 已证 | G2/G4；S1.336–345 |
| marked continuous H¹ 运输 | 🟢 已闭合 | 显式拓扑群同构和等变系数同构给原连续 H¹ 的连续线性同构、cocycle 公式及逆；实际 Tate twist marking 给 integral/rational 运输、standardMap 交换及按这些标注取并集的 collation | G2/G4；`0c970a2`；`ContinuousH1Transport.lean`、`LocalKummerMarkedTransport.lean` |
| 固定底域 preferred-closure Kummer 运输 | 🟢 已闭合 | closure 代数同构给 Krull Galois 拓扑同构、自然 Tate 运输及 integral/rational H¹ 运输；实际基变换由 ℤₚ 单位给出，根塔选择独立，目标类仍来自同一底域元素 | G2/G4；`3437315`、`afe6ccd`；`GaloisClosureTransport.lean`、`LocalKummerClosureTransport.lean`、`LocalKummerRationalClosureTransport.lean` |
| actual tilt／Fontaine／B_dR 局部来源 | 🟢 已闭合 | canonical completed algebraic closure、原 tilt 的范数／完备／代数闭性、sharp、实际 W(O_F) 的 θ 满射及 primitive 主核；原 B_dR⁺ 完备 DVR、原 B_dR 分式域及 primitive-adic 范数完备性已证 | G2；`IutInitialThetaTiltAlgebraicallyClosed.lean`、`IutInitialThetaFontaineKernel.lean`、`IutInitialThetaDeRhamTopology.lean`；未识别论文指定 F、FF 点或 Fréchet B／ρ-norm |
| ordinary-log principal-unit 与 integral carrier | 🟢 已闭合 | 饱和/线性/连续 log、integral-image intersection、p* 缩放同构及 actual normalized integral witness 已证 | G1/G4；S1.359–425；`IutInitialThetaNormalizedIntegralLog.lean` |
| actual ambient H¹ 坐标与 Tate-log | 🟢 已闭合 | 原拓扑上 `H¹ ≃L[ℚₚ] completion × ℚₚ`；log(p)=0 分支及核为实际 q-root 线的 Tate-log、商比较、连续性已证；actual q-root 与 normalized 类线性独立 | G2/G4；S1.452–457、S1.466 |
| full-support 与 VBad q-root family | 🟢 已闭合 | 任意下方实际 VBad 处的 `2ℓ` 幂方程、标准 ordp 公式与坏特征法律；VBad 限制族取 1 于支撑外，其全部 torsion-place 纤维和及全局 log-sum 精确恢复实际 absLogQ | G2/G3；`IutInitialThetaQRootFamilyLocalLaws.lean`、`IutInitialThetaVBadQRootFamily.lean` |
| selected/omitted 与代表系数会计 | 🟢 已闭合 | full support 的分解、缺陷与严格正性、actual section carrier 到 canonical link 的等式及代表纤维质量 regrouping 已证；coverage、mass-one 和 target bridge 保留各自条件 | G1/G3；S1.475–492；`IutInitialThetaSelectedQRootLinkAccounting.lean`、`PaperQRepresentativeFiberMass.lean` |
| ordinary-log hull 与 canonical actual bundle | 🔵 条件性完成 | 同一 D 固定 ordinary-log hullVolume、raw q-term、q-family、qProduct 下界和 Corollary consumer；剩余 theta/period/Perfectoid 法律由 AnalyticInput 接收 | G1/G2/G4；S1.493–503；`IutInitialThetaCanonicalActualHullData.lean` |
| finite factor orbit / 指定因子 j² 区域 | 🟢 已闭合 | 实际有限 tensor 自同构、normalization 稳定、紧性与正有限 Haar；指定因子缩放及坏特征外恢复 normalization 已证 | G4；`db8dc46`、`17eb097` |
| actual de Rham θ-fiber / tensor image / normalization hull | 🟢 已闭合 | 对原 B_dR⁺ 残值子环的完整 θ-fiber 证明非空及 primitive·b+pilot 表示；求值像是原 qrootAt^(j²) 单点，指定 tensor 因子像是旧 scaleElt 单点；factor orbit 等于旧点轨道且 Haar 为零，其 normalization hull 等于旧 leastHull，紧、Haar 正有限并包含旧 thickened region | G2/G4；`4a80562`；`IutInitialThetaDeRhamFiberHull.lean` |
| 全部有限处 tuple packet 与标准 procession | 🟢 已闭合 | 每个素数上全部 tuple、非空、显式 witness、紧性、普通乘积测度、`ellStar=(ℓ−1)/2` 与共同有限支撑已证 | G3/G4；`223ff40` |
| finite/arch/adelic packet、shell 与 hull | 🟢 已闭合 | 全部 tuple 的 restricted-product container、共同有限支撑、finite principal／arch 正径向 least hull、闭包算子、shell 固定点与 factor 自同构稳定性已证；无穷处 packet log 精确为 (j+1)log π | G3/G4；`IutInitialThetaAdelicPacketRegion.lean`、`IutInitialThetaAdelicHullClosure.lean`、`IutInitialThetaAdelicLogShell.lean` |
| 三层 log-volume 与 actual Haar-product 下界 | 🟢 已闭合 | finite/arch tuple 权重消去 tensor dimension，统一 family 的 packet/global/procession functional 还原 source/hull/shell；实际有限 Haar product、finite/adelic 下界及 prime-preimage 的 +log p 校正已证 | G1/G3/G4；`IutInitialThetaAdelicFamilyLogVolume.lean`、`IutInitialThetaWitnessHullHaarProduct.lean`、`IutInitialThetaFinitePacketPrimeLogVolume.lean` |
| normalized ordinary-log witness／collation hull | 🟢 已闭合 | 实际 integral Kummer 类的 log/p* tensor witness 与原 q-root 有相同 normalization hull；其 class-image collation consumer 及同一 completion 内完整 factor-orbit 饱和保持 hull／体积法律，标准类 tuple 还原既有 actual hull | G2/G4；`IutInitialThetaFiniteNormalizedLogHull.lean`、`IutInitialThetaNormalizedLogCollation.lean`、`IutInitialThetaLogCollationOrbit.lean`；跨 holomorphoid 的 H¹ₑ/BK 身份仍缺 |
| paper carrier / weights / representatives | 🟡 部分完成 | actual source→section Voss→canonical section-link 已证；同 carrier 的 weighted paper bridge 在 hEll/hLink 等条件下成立。独立 Scene1 link、论文 `L'` 及 relative-degree／multiplicity 的最终身份仍缺 | G3；S1.471–500；来源义务清单的 section carrier、normalization 与 fiber-mass 子项 |
| H¹ₑ/BK/crystalline/period | ⚪ 未建立 | ordinary Kummer/log 已证；尚无与论文 H¹ₑ/BK 对象的实际比较，参考 iut 没有可直接移植 Lean proof；Joshi 论文提供构造规格 | G2/G4；`JT-SCENE1-CANONICAL-ACTUAL-HULL-DATA`、来源义务清单 |
| 跨 untilt theta locus 与 paper hull/volume 身份 | ⚪ 未建立 | 已构造 actual finite/arch container、hull、shell 及无穷处数值贡献；尚缺论文 theta locus、跨 arithmeticoid 来源标注／collation、paper volume 身份和无穷处在最终目标中的处理 | G2/G4；来源义务清单 |

### 在制单元：尚未纳入已完成基线

| 文件 | 当前状态 | 达到验收尚需 |
| --- | --- | --- |
| `LocalKummerLogClosureTransport.lean` | 已写出固定底域 closure 运输对 principal image、p-saturation、ordinary log、inverse exp 及 integral lift 的兼容证明；第二次叶检查退出 0，日志仍有两条 unused-section-variable warning | 清理警告；完成逐名 checks／axioms、聚合与静态边界验收、来源登记和推送 |
| `IutInitialThetaClosureLog.lean` | 已写出从同一 D 的 actual completion 构造 preferred closure equivalence、运输实际 principal-unit／divided 类及保留 witness log 公式的代码；尚未编译 | 首次编译及修复，再完成同一单元全部验收、登记和推送 |

两文件目前均未跟踪，未进入 Scene1 聚合和两套审计；不能据此把 closure ordinary-log 兼容或 actual 类运输标为已闭合。

### 最新会计公式及适用范围

令 `Kt = D.prime.torsionField`，`N=[Kt:ℚ]`；capsule 有 `m=j+1` 个标签，`c` 遍历同一有理素数上全部处的 tuple。记 `d_c` 为实际 tensor 的 `ℚₚ` 维数，`R_c` 为指定因子缩放后的有限自同构区域，`μ_c` 为 normalization 测度取 1 的实际 Haar。已证明

```text
weight(v) = [Kt_v : ℚₚ] / N
Σ_v weight(v) = 1
weight(c) = Π_i weight(c_i) = d_c / N^m
Σ_c weight(c) = 1
componentLog(R_c) = log(μ_c(R_c)) / d_c
packetLog(R) = Σ_c weight(c) · componentLog(R_c)
             = log((Π_c μ_c)(R)) / N^m
```

各 `μ_c(R_c)` 正且有限，区域位于 normalization，所以 packet log 不大于零。坏特征外所有区域恢复 integral 基准，packet log 为零，因此 global log 是有限素数和。procession log 为这些 global log 在 `j=1,…,ellStar` 上的平均，且 `-|processionLog| = processionLog`。

令 `Q=absLogQ(D)`，`S=squareAverage(D)` 为标准 procession 的 j² 平均；实际无限处贡献为 `A_j=(j+1)log π`，`A` 为其 procession 平均。对已构造 source／hull 已证：

```text
-j² Q ≤ finiteGlobalLog(D,j) ≤ 0
-S Q  ≤ finiteProcessionLog(D) ≤ 0
A_j-j² Q ≤ adelicGlobalLog(D,j) ≤ A_j
A-S Q    ≤ adelicProcessionLog(D) ≤ A
finiteProcessionVolume = exp(hullProcessionLog - A)
finiteProcessionVolume ≥ exp(-S Q)
paperRootProduct^S < finiteProcessionVolume
```

有限处 volume 由实际 packet Haar 测度的次数根、有限素数乘积及 procession 几何平均构造。最后的严格界使用同一 D 的 actual selected paper-root product 和已证 q-accounting；`S`、local-degree 权重及 `A` 均保留，adelic log 未被假定为非正。`LocalCompletionTensorNormalizationLogVolume.lean` 与 `IutInitialThetaFinitePacketLowerBound.lean` 已完成且纳入来源清单跟踪。

这些等式连接的是完整 torsion-field tuple 的 local-degree 权重；仍须证明它们怎样对应 Joshi III `ss:weighted-vol` / `eq:weights` 的所选处及 relative-degree 权重。actual container、ordinary-log hull 和论文 theta locus 的身份也仍须证明。

局部 q-factor 的已证条件性换算为 `-log(paperFactor)=qOrder·log(residueChar)/(2ℓ)`，而 `normalizedLogTerm=qPilotWeight·(-log(paperFactor))`；q-pilot 权重属于后一个公式。

### 已排除路线：避免重复投入

| 具体路线                                                  | 状态与排除范围                                                              | 当前应保留的工作方向                                          | 证据                     |
| --------------------------------------------------------- | --------------------------------------------------------------------------- | ------------------------------------------------------------- | ------------------------ |
| 用旧 weighted normalization 直接覆盖一般数域              | 🔴 当前路线要求额外 finrank=1，不能完成一般数域模型                         | 来源驱动的归一化复审与真实模型装配                            | S1.270                   |
| 把 VBad 去权系数直接补成 1                                | 🔴 实际系数在指定条件下严格小于 1                                           | 保留实际 coefficient，加权重审 target/volume 会计             | S1.282–283、S1.320      |
| 令 target qLogSum 等于未加权 selectedPaperSum | 🔴 degree-one 旧路线上存在严格 gap；general-degree raw 仍有 degree-scaled 严格 gap | 保留实际 coefficient、degree 及 omitted contribution，使用已证加权恒等式 | S1.356–357、S1.489–492 |
| 把 signed Haar logMeasure 直接等同旧 `link.logVolume`   | 🔴 actual signed log-volume 为负，而旧 transfer 要求非负                    | 使用 negative-log cost，继续证明论文 volume 身份              | S1.321–322、S1.405–406 |
| 将 raw-norm weighted region 无条件当作 paper region       | 🔴 区域函数存在要求 weighted degree 恒定                                    | 从真实 paper norm、处集和 residue-degree 证明条件，或改写载体 | S1.439                   |
| 把 q-root 自身 Kummer 类当作 normalized principal-unit 类 | 🔴 q-root 类不在 saturated image，且不在 normalized ℚₚ 线                 | 保留 unit/prime 分解，分别追踪两个实际类                      | S1.440、S1.451           |

这些结果排除的是表中具体装配路径，不是 Corollary 3.12 本身。

## 未完成证明义务

### G1：目标、符号和归一化

1. **冻结 q-term 的来源语义。** 当前工程 `qLogTerm` 使用 `-log(qFactor)`，论文 Corollary 3.12 字面式存在相反符号；用户已决定暂按笔误处理，但来源审查和作者确认尚未完成。
2. **统一 raw、degree-normalized、paper-normalized 三层。** 现有 general-degree reference/grouped-source 恒等式和 finite tuple 维数消去已证；仍须在最终 paper carrier 上对齐 global degree、`p*`、`2ℓ`、residue-degree、代表权重与选定 volume 的完整表达。
3. **冻结 `thetaVolume` 的对象。** 必须确定它是 actual Haar volume、negative-log cost 的指数，还是不同 untilt 的论文体积，并证明与实际 hull 的关系。
4. **统一消费者。** `Corollary312`、q-family、packet/hull、volume transfer 和最终目标必须共享同一 carrier、权重和符号。

### G2：真实来源模型

1. **共同 analytic 来源。** 同一 D 的算术/q-root、ordinary-log hull、有限处 container 已能实际构造；`CanonicalActualHull.AnalyticInput` 仍接收 `placeData`、`bridge`、`thetaScaling`、`periodMap`、`normalization`、`perfectoidBridge`、`theta_log_shell`。须从同一论文 theta/untilt 来源产生这些字段，而非把现有 bundle 称为联合真实模型。
2. **H¹ₑ/BK 身份。** 需要证明当前 ambient `unitsSubspace` 或明确替代载体与 H¹ₑ/Bloch–Kato 相同；若不相同，必须改写消费者。ordinary log 和成员性不能自动给出该身份。
3. **crystalline/Frobenius/period。** actual tilt、Fontaine θ 主核、原 B_dR⁺ 完备 DVR 及原 B_dR 的 primitive-adic 完备性已证。尚需 B_cris／Frobenius、H¹ₑ/BK 比较、FF／Fréchet B／ρ-norm 的论文身份及全局 product-formula period map 到 `theta.period` 的比较；不重做已完成的 Fontaine／B_dR 局部代数来源。
4. **different/untilt/descent。** 需要连接 completion valuation、论文不同 untilt、period 和 descent，同时保持 q-order、residue-degree 和 volume 会计一致。
5. **跨来源标注与最终 Kummer 对象。** marked ambient H¹ transport 和固定底域 closure 的自然 integral/rational transport 已证；必须进一步从 admissible holomorphoids／anabelomorphisms 产生所需标注，证明 H¹ₑ/BK 及 log 兼容。S1.446 的 span=ambient H¹ 仍不证明论文指定元素／untilt／H¹ₑ 身份。

### G3：论文处集、代表元和重数

1. actual selected source→section Voss→canonical section-link 的 carrier 链已闭合；仍需识别独立 Scene1 link 与论文 `V_p^oss`、`L'` representatives，或证明最终目标所需的明确替代映射。
2. 逐项闭合 representative multiplicity、packet weight、place weight、residue degree、tensor dimension 的乘法会计。
3. 对 full-support 路线，保留 large-prime coverage 的前提或 omitted contribution；对已构造的 VBad 限制族，其 exact fiber accounting 已不要求 full support 等于 VBad。论文 carrier 选择仍须统一，不能删掉原 full-support 的额外贡献。
4. 从真实 paper norm、moduli degree 和不同处集推出 S1.439 的 weighted-degree 恒定条件，或重新定义 region 载体。
5. 将已证 full torsion-field tuple 的 local-degree / tensor dimension 会计，与论文所选代表处的 relative-degree 权重和无穷处归一化接到同一目标求和。

### G4：theta-volume、Corollary 3.12 和最终验收

1. 给出 actual ordinary-log hull 或 finite q-root container 到论文 theta locus / holomorphic hull / `thetaVolume` 的来源等式或足够比较。actual canonical bundle 已定义 `thetaVolume=hullVolume D`；缺的是该对象与论文 volume 的身份，不是本地字段等式。
2. 消费已证 finite/arch/adelic packet、shell、hull、三层 log-volume 与真实 Haar-product，下接 paper 权重和 q-sum；证明保留的 squareAverage、无穷处 A 及最终负绝对值形式如何满足选定 3.12 目标。
3. actual canonical target、q-family、ordinary-log volume 与 Corollary consumer 的接线已存在；须证明其 AnalyticInput 和论文身份从共同真实来源满足，并完成完整 RHSData。
4. 用同一个对象同时满足 G1、G2、G3、G4，而不是保留互不连接的局部适配器。
5. 所有最终声明冻结后，再执行完整 ImportAudit、逐名 checks/axioms、无 `sorryAx`、`git diff --check` 和最终推送验收。

## 负面证据

负面证据只排除下文写明的路线；它们不自动证明论文命题错误，也不允许把条件性结果升级为最终定理。

### S1.305：Corollary 3.12 字面式符号冲突

- **证据：** 在普通实数 log 和 actual contracting q-root 解释下，论文字面右端 `-∑ log |q_w^(1/(2ℓ))|` 为正，左端 `-(1/n)|log(volume)|` 不大于零。
- **排除：** 该组符号解释下的字面不等式不能成立。
- **不能推出：** 不证明论文在其他 carrier、untilt 或符号约定下错误；不能无记录地反转工程 `qLogTerm`。
- **当前决策：** 按用户决定暂作笔误，等待作者回复；不作为当前停工项。

### S1.243：theta/logVolume 与 contracting q-root 的符号冲突

- **证据：** 当前 `Scene1Input` 的 FirstAxiom/VolumeTransfer 强制 `logVolume ≥ 0`；actual canonical contracting q-root 的 ordinary log-volume 在同一解释下为负。
- **排除：** 不能把该 q-root norm 直接作为当前 theta base norm，不能用普通 `norm_pow` 代替论文不同 untilt 的估值关系。
- **不能推出：** 不排除另一个 theta lift、different untilt 或 negative-log cost 解释；不应直接反转 Core 字段或用 reciprocal 替代 q-root。

### S1.321、S1.405：signed Haar logMeasure 不能直接填入旧 VolumeTransfer

- **证据：** actual ordinary-log generated hull 在正长度时的 Haar log-volume 严格为负；旧 transfer 对非负 packet/hull 权重要求 `logVolume ≥ 0`。
- **排除：** 不能把 signed Haar logMeasure 直接当作旧 `link.logVolume` 的生产者。
- **可保留路线：** 使用 `-log(volume)` 作为非负 actual cost；S1.406 已构造有限 cost carrier 和 transfer producer。
- **不能推出：** 不等于论文 `thetaVolume` 必须错误；negative-log cost 与论文 volume 的身份仍未证明。

### S1.420–421：unscaled integral-log image 不等于 p*-scaled shell

- **证据：** 原 integral ordinary-log image 有界、非零且严格小于 p*-scaled shell；乘以 `p*` 才恢复精确载体，并产生 Haar/log-volume correction。
- **排除：** 不能把 unscaled integral image 直接命名为 scaled shell，也不能删除 p* correction。
- **不能推出：** 不证明 actual 原 integral witness 不存在；`IutInitialThetaNormalizedIntegralLog.lean` 已给原 integral 类及 finite-power 类配 `log/p*` 的 witness 公式。旧 divided rational 类是否有 integral lift，仍按其有限根/整除判据判断；两种 class/map 约定必须区分。

### S1.425：usual small-ball Kummer inverse 与 ordinary log/p* 不相容

- **证据：** 保留通常小球指数、原 class identification 和 ℚₚ-linearity 时，逆映射被唯一强制为 ordinary log；actual 原类的 ordinary log 是 `p*` 乘 paper witness。
- **排除：** 不能同时保留这三项约定，又把 ordinary log/p* 当作同一个 BK inverse。
- **可保留路线：** 保留 S1.424 的显式 normalized ordinary map，从来源比较指数、class identification 或 map normalization。
- **不能推出：** 不能仅凭该冲突宣布 H¹ₑ/BK 不存在或论文错误。

### S1.283、S1.356–357：未加权 paper sum 不能替代 weighted target

- **证据：** 当前 VBad representative coefficient 严格小于 1；canonical degree-one 条件下 `qLogSum = referenceAbsLogQ < selectedPaperSum`。
- **排除：** 不能把 target qLogSum 设为未加权 selected paper sum，不能把 VBad 去权系数补成 1。
- **问题等级：** 当前证据支持“上下游接口契约/实现适配问题”，不足以归类为原作者不可修复错误。
- **可保留路线：** 使用实际 coefficient 加权会计，重审下游 hull/volume 消费者。

### S1.403：参考 iut 没有可直接移植的 H¹ₑ/BK 证明

- **证据：** 参考 iut Lean 工程没有可直接移植的 H¹ₑ/Bloch–Kato 比较 proof；Joshi III `ss:bloch-kato-exp`、`ss:bloch-kato-logarithm`、`th:thetam-construction` 给出明确论文构造及外部依赖，但本地 ordinary Kummer/log 尚未与这些对象识别。
- **排除：** 不能通过简单移植参考工程代码关闭 H¹ₑ/BK 义务，不能把 ambient `unitsSubspace` 改名为 H¹ₑ。
- **剩余工作：** 独立建立来源可追溯的形式接口和实际比较定理。

### S1.404：Prologue obligation 构造器不能作为证明来源

- **证据：** `Prologue/Obligations/Constructors.lean` 的 `build_*` 构造器是 `sorry` 占位，Scene1 计划明确禁止导入该模块。
- **排除：** 不能用这些构造器补齐真实 theta、period、volume 或联合模型。
- **不能推出：** 这不是数学命题的反例，只是独立工程原则下的来源拒绝。

### S1.440、S1.451：q-root 类与 normalized principal-unit 类不能混用

- **证据：** actual q-root 的 field-element Kummer 类 norm<1，不在 saturated Kummer image；normalized principal-unit 类在 saturated image、在 ambient `unitsSubspace`，且 q-root 类不在其 `ℚₚ` 单生成 span。
- **排除：** 不能把 q-root 自身 Kummer 类当作 `1+p*·qroot` 产生的 normalized 类，不能用二者互换完成 H¹ₑ/BK 或 prime-line 识别。
- **不能推出：** 不证明 q-root 类不是论文所需的另一个 untilt/prime-line 类；只排除当前两个实际类的混用。

### S1.439：raw-norm weighted region 的恒定条件

- **证据：** weighted region volume 函数存在的充要条件是 weighted degree 恒定；selected fibre 下归结为 moduli local degree 恒定。
- **排除：** 不能无条件把当前 raw-norm region 当作一般 mixed-moduli paper region。
- **剩余工作：** 从真实 paper norm、处集和 residue-degree 数据证明恒定条件，或重新定义 region 载体。

### S1.489–492：general-degree raw target 仍不能消去 paper defects

- **证据：** 保留实际 Tate/source 对齐时，general-degree raw qLogSum 含 `[D.F:ℚ]` 因子；large-prime 路线上有精确恒等式 `raw qLogSum + degree·(coefficient defect + omitted paper mass) = degree·full paper sum`，且实际 VBad 非空给严格 defect。
- **排除：** 不能将 raw qLogSum 直接设成无缺陷的 degree-scaled paper sum，也不能只靠除去 global degree 就删除 representative defect。
- **可保留路线：** S1.496–500 的 degree-normalized reference/grouped weighted-source 恒等式与 S1.493–503 的 actual hull 消费者；论文 carrier/weights 身份仍单独验收。

## 本次验收与工程边界

最近已验收数学单元为 `afe6ccd` 的 rational preferred-closure Kummer transport；详细声明与资源记录见 SOURCE_LEDGER 的 `JT-SCENE1-LOCAL-KUMMER-RATIONAL-CLOSURE-TRANSPORT`。本次总览更新沿用该基线，不把在制文件的检查当作聚合验收。

| 检查 | 结果 | 耗时 | 进程组峰值 RSS |
| --- | --- | --- | --- |
| 新叶 LocalKummerRationalClosureTransport | 通过，无错误或 warning | 60.595 秒 | 5,147,012 KiB |
| Checks.SceneBounds | 通过 | 121.195 秒 | 9,442,524 KiB |
| Axioms.SceneBounds | 通过；17/17 新声明、3017 个打印声明在白名单内 | 114.320 秒 | 9,425,332 KiB |
| Act1Scene1 聚合 | 通过 | 114.647 秒 | 9,272,600 KiB |

最终四项合计 410.757 秒；加首检一次 API／展开适配失败 60.077 秒，共 5 个直接 Lean 任务累计 470.834 秒（4 成功、1 失败），该单元无 heartbeat 超时。此前 marked transport 与 integral closure transport 单元也均无 heartbeat 超时。公理仅 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`；静态导入边界覆盖 542 个本工程模块，未引入 Obligations、Candidate、Scene2、Act2 或 `Iut.*`。

已验收任务固定 CPU 0–13、`LEAN_NUM_THREADS=10`、Lean `-j1`，实际并发 worker 峰值 1。每 0.5 秒采样进程组 RSS，85 GiB 停止线未触发；用户上限 90 GiB。使用 `lake env lean -j1 -o` 和现有预编译依赖，未冷建、清缓存或重编 Mathlib。冻结 Lean `v4.35.0-rc3`、Mathlib `389347a7c1cfa76f6bd5be2ca35d4cb621610ad3`。

本总览按用户明确指令更新。已完成范围、未完成父义务与在制代码分别按上表记录；Prologue-R5／Core 假设增量仍为 0，最终四闸门仍为 0/4。

## 最终完成条件

只有同时满足以下条件，才能把 Scene1 标记为完成：

1. G1 的目标、符号和归一化冻结，并由来源审计支持。
2. G2 的真实 `InitialThetaData/TateFamily`、H¹ₑ/BK、period、different/untilt 和 Kummer 来源链共同实例化。
3. G3 的论文处集、representatives、重数、residue-degree 和 weighted carrier 会计闭合。
4. G4 的 actual `thetaVolume`、packet/hull accounting 和 Corollary 3.12 连接闭合。
5. 最终 ImportAudit、checks、axiom 白名单、无 `sorryAx`、`git diff --check` 和推送验收通过。
