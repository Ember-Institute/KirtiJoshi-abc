# Scene1 进度总览 5

截至 **2026-11-19（Asia/Shanghai）**。Scene1 的几何交付从总览4的 **`a443952`** 推进到 **`0477a914`**。本期还完成了 Lean 工具链迁移，并推进了 Prove2Me 的参考算术链。 [总览4](Scene1进度总览4.md) · [Scene1 开发计划](开发计划.V1Act1Scene1.md) · [Prove2Me 适配计划](开发计划.Prove2Me适配.md)

### 状态判定

| 标记 | 状态 | 使用条件 |
| --- | --- | --- |
| 🟢 | 已闭合 | 本行精确义务有证明，所需输入已落实，对应验收已通过 |
| 🔵 | 条件性完成 | 已验证给定明确输入时的定理，目标数据仍缺这些输入的构造 |
| 🟡 | 部分完成 | 已有可复用的子结果，仍缺实际构造、比较或身份等式 |
| ⚪ | 未建立 | 完整要求仍缺满足其类型的已验收构造或证明 |
| 🔴 | 路线已排除 | 只在所列条件下排除一条具体路线 |

## 当前结论

| 项目 | 当前值 |
| --- | --- |
| Scene1 整体 | **未完成，G1–G4 关闭 0/4** |
| 有明确来源指示的父义务 | **15 项均开放**。见[证明义务清单](具有明确参考来源指示的证明义务.md) |
| iut 参考链适配 | **141/158（89.2%）**。最近验收参考 Vélu 主界、固定常数的循环子群估计和 CanLift 的 étale 下降。 [适配计划 §4.1](开发计划.Prove2Me适配.md#41-参考链审计) |
| 最新 Scene1 数学单元 | 原二阶点平移仿射图的分式域沿原包含映射的像等于原无符号正规化域。 [分式域像等式](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/InitialThetaInfinityShiftedChartFractionField.lean#L156) |
| 几何路线的下一处缺口 | 在平移仿射图的同一剩余中心证明逆坐标公式的分母可逆，再用局部整闭性识别原无符号正规化的上层剩余域 |
| 本地构建环境 | Lean `v4.33.1`，Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`。见[环境锁](../ArithmeticTeichmullerSpaces/migration/environment.lock.json) |
| Prologue 边界 | R5。四项来源法律由 Scene1 生产者负责。见[生产者契约](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/ProducerContracts.lean) |

各项状态以对应定理实际量化的对象、条件及验收范围为准。

## 四个最终验收闸门

| 闸门 | 状态 | 已有支撑 | 关闭所需的证明 |
| --- | --- | --- | --- |
| G1 目标与归一化 | 🟡 | q 因子的原始、按次数归一和加权公式已有局部换算 | 对论文指定的同一处集证明 q 项、论文权重、无穷处体积和符号约定的完整换算，固定 Form 2 及 3.12 的精确类型 |
| G2 共同真实来源 | 🟡 | 同一种子的 Tate 参数与 q 根，原无穷远分歧指数、下层剩余域及平移仿射图的分式域 | 证明上层剩余域及边界身份，实现轨形曲线与尖点，再从同一数据构造 Initial Θ-data、holomorphoid、period 和 H¹ₑ/BK |
| G3 论文处集与重数 | 🟡 | 所选 valuation section、有限覆盖判据、纤维重组及内部加权等式 | 供应论文处集与 $L'$ 的实际代表，证明覆盖、重数、剩余和分歧次数公式，并处理遗漏质量及跨模点下降 |
| G4 theta locus、体积与最终连接 | 🟡 | actual Kummer/ordinary-log 包络、Haar 体积、负对数 cost 和条件性 3.12 消费者 | 由共同标记与 BK 对数证明论文 theta locus 身份，再识别测度和体积并导出最终下界 |

四闸门的正式目标和完成标准见开发计划，现行构建与公理审查依仓库约定执行。 [闸门目标](开发计划.V1Act1Scene1.md#3-未完成义务按最终闸门分解) · [完成标准](开发计划.V1Act1Scene1.md#7-完成标准) · [仓库验收约定](../AGENTS.md#回执与项目验收)

## 已完成的局部结果

| 范围 | 状态 | 精确结果 |
| --- | --- | --- |
| 局部算术与解析基础 | 🟢 | 同一种子给出 Tate 参数、q 根及有限处的完成域。局部倾斜、Fontaine θ、Witt 法律及标准有理半径完成上的 Frobenius 已建立。 [计划第 2 节](开发计划.V1Act1Scene1.md#2-已完成义务只列结果) |
| Kummer 与对数 | 🟢 | 连续整系数和有理系数 H¹ 类、系数映射、普通对数群律和相应包络及体积公式已有证明。 [计划第 2.2 节](开发计划.V1Act1Scene1.md#22-实际-initialthetadata-的局部派生链) |
| 原无穷远分歧与几何作用 | 🟢 | 原无符号上层素点的分歧指数为 1，原平移惯性平凡，带剩余域嵌入的几何点轨道阶为 $\ell$。 [分歧指数](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/InitialThetaInfinityTranslationUnramified.lean#L59) · [几何轨道](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/InitialThetaInfinityTranslationFreeGeometricOrbit.lean#L60) |
| 原下层剩余域与仿射图 | 🟢 | 原下层剩余域与扭点系数域代数等价。两个剩余坐标均来自该域，仿射图在剩余中心的局部环整闭，其分式域经原包含的像等于原无符号正规化域。 [下层剩余域](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/InitialThetaInfinityTranslationBaseResidue.lean#L119) · [局部整闭性](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/InitialThetaInfinityShiftedAffineChart.lean#L192) · [分式域像等式](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/InitialThetaInfinityShiftedChartFractionField.lean#L156) |
| Corollary 3.12 的条件消费者 | 🔵 | `cor312_of_scene1_data` 接收含体积、q 族、归一化和会计字段的 `Corollary312Scene1Data`。`CanonicalActualHull.corollary312` 接收 `InitialThetaData` 及相应的 `AnalyticInput` 等数据，得到实际包络与原始完成域 q 范数上的不等式。 [通用消费者](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/AdelicThetaLinkBridge.lean#L111) · [实际包络消费者](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaCanonicalActualHullData.lean#L258) |

## 当前证明路线

实线表示已有证明连接，虚线表示还缺构造或比较。

```mermaid
flowchart TD
  S["同一算术与 Tate 种子"]
  F["原有限闭包素点提升与惯性固定"]
  E["原平移分歧指数 1、惯性平凡、几何轨道阶 ℓ"]
  R["原下层剩余域等于系数域"]
  A["原平移仿射图的整闭局部环与共同分式域"]
  U["原逆坐标公式的局部分母比较与上层剩余域"]
  G["原边界、尖点与轨形曲线实现"]
  H["共同 Initial Θ-data、holomorphoid 与 H¹ₑ/BK"]
  P["论文处集、代表及权重"]
  N["q 项与体积的统一归一化"]
  V["论文 theta locus 与体积下界"]
  C["Form 2 与 Corollary 3.12"]

  S --> F
  F --> E
  S --> R
  S --> A
  A -.-> U
  R -.-> U
  E -.-> G
  U -.-> G
  G -.-> H
  G -.-> P
  H -.-> V
  P -.-> V
  P -.-> N
  V -.-> C
  N -.-> C

  classDef done fill:#dcfce7,stroke:#15803d,color:#14532d;
  classDef open fill:#f3f4f6,stroke:#6b7280,color:#111827;
  class S,F,E,R,A done;
  class U,G,H,P,N,V,C open;
```

## 未完成的证明义务

第 1–15 项沿用明确来源义务的顺序。统一归一化和 Scene2 需要的全称适配见第 15 项。 [明确来源义务清单](具有明确参考来源指示的证明义务.md)

### Prologue/Core 的来源接口

#### 1. 真实 perfectoid bridge 的来源适配（🟡）

给定共同算术种子的实际有限处，须从论文指定的解析来源同时取得局部整数环、untilt、tilt 与 Fontaine θ。随后要证明该处与 `PerfectoidPlaceData` 的处标记一致，系数映射等于同一 completion embedding，且 `PerfectoidBridgeData` 中的 θ、核和局部法律由这个来源给出。已有局部倾斜、Fontaine 与 Witt 证明可用于这些局部法律。解析点、同一 untilt 的身份和系数图交换仍需要第 6 项提供。 [来源义务一](具有明确参考来源指示的证明义务.md#一prologuecore-相关义务)

#### 2. Core 载体到同一个真实输入（🟡）

`AdelicThetaLinkData` 中的 q 参数、处集、Tate 参数、高度、分歧和 packet 必须由同一数域与曲线的全局数据产生。现有同种子 Tate family、局部 q 根、离散赋值和挠点提供局部构造，`ofInitialThetaData` 等适配器提供投影等式。尚须把这些局部构造与第 4、5 项产出的 `orb`、`localData` 接在同一数域、同一个 $\ell$ 和同一个扭点域上，逐处证明 q 根的范数、阶数和输入到 packet 的坐标转换等式。 [来源义务一](具有明确参考来源指示的证明义务.md#一prologuecore-相关义务)

#### 3. 四个 Scene1 生产者的来源法律（⚪）

`AdelicThetaLink` 需要真实 period 和 q 归一化，`ThetaLiftLog` 需要实际 theta-value 的类及其 log-shell，`PacketCollationHull` 需要论文的来源支撑与跨标记拼接，`VolumeTransfer` 需要同一包络上的测度和体积传递。当前边界已指明四个消费者及各自的显式输入。开放工作是按第 2、6–14 项逐一把字段落实为有精确类型的数学命题与证明，并核对四个输出使用共同来源。体积字段应由测度比较构造，最终数值下界由第 15 项组合导出。 [生产者契约](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/ProducerContracts.lean)

### 共同 Initial Θ-data 与原无穷远边界

#### 4. 实现 `InitialThetaGeometryProducer`（🟡）

在目标几何接口 `AG/TG` 上，对每个 `InitialThetaGeometrySeed` 共同构造 `OrbicurveData` 与依赖该输出的 `LocalThetaData`。种子固定数域、椭圆曲线、代数闭包、坏处集、适用素数及 `HasCoreUniversally`。证明须在同一几何输出上实现赋值截面、分解群和局部覆盖图，并使 `toInitialThetaData` 能用种子的 Tate 族装配这些数据。 [生产者的量化与输出](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/ProducerContracts.lean)

1. 在同一有限正规闭包素点上，设 $k$ 为扭点系数域，$A=k[x',y']$ 为平移除法点 $Q'$ 的仿射坐标环，$\mathfrak m$ 为它的剩余映射核。平移所用的非零二阶点 $T=(r,s)$ 满足 $[\ell]Q'=G+T$，其中 $G$ 是原泛点。记 $c=3r^2+2a_2r+a_4-a_1s$，$\Phi=\Phi_\ell(x')$、$\Psi=\Psi_\ell^2(x')$ 为配方模型的除法多项式取值。待在原共同分式域中组合二阶点平移公式与精确纤维方程，得到

   $$
   x_G^{-1}=\frac{\Phi-r\Psi}{r(\Phi-r\Psi)+c\Psi}.
   $$

   已证的剩余纤维方程给出 $\overline{\Phi-r\Psi}=0$。须将除法多项式在该纤维根处的非零引理特化为 $\overline{\Psi}\ne 0$，并用二阶点的非奇异性和 $2s+a_1r+a_3=0$ 得到 $c\ne 0$。系数域的剩余映射为单射，故目标分母的剩余值为 $\bar c\,\overline{\Psi}\ne 0$，使原基环 $k[x_G^{-1}]$ 进入 $A_{\mathfrak m}$。 [二阶点平移公式](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/TwoTorsionTranslationIntegral.lean#L23) · [实际剩余纤维方程](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/InitialThetaInfinityShiftedDivisionResidue.lean#L130) · [纤维根处分母非零引理](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutCompat/Torsion/Count.lean#L212)
2. 沿已证分式域身份，把原上层正规化的每个元素送入 $A_{\mathfrak m}$。所需证明使用这些元素对 $k[x_G^{-1}]$ 的整性与 $A_{\mathfrak m}$ 的整闭性。随后核对 $\mathfrak m A_{\mathfrak m}$ 在原上层正规化中的收缩就是选定的上层素点，沿该包含诱导剩余域映射。仿射图的常数剩余像使该映射的像恰为 $k$。还须核对它与原下层系数映射相容，得到原上下层相对剩余次数为 1。结合惯性平凡与纤维传递性，可再计算原算术素理想稳定子及上层素点纤维的基数。 [上层剩余域的开放边界](开发计划.V1Act1Scene1.md#2026-11-11原-shifted-chart-的共同分式域与-full-division-field)
3. 把原无穷远正规化纤维与原射影曲线的无穷远点比较，构造与挠点商 $E[\ell]/M$ 的等价，并验证该等价下的 distinguished class。再实现到 `AG.Cusp` 的映射，证明该尖点与坏处的 theta 根模型相容。现有几何轨道定理量化的是带剩余域嵌入的点。 [原几何作用及边界](开发计划.V1Act1Scene1.md#2026-11-10原平移惯性平凡与原几何轨道阶-ℓ)
4. 从原呈示在实际 `AG.Orbicurve` 中构造对象及覆盖，将种子的 core 条件和原呈示的拉回接到 `AG.IsCartesianSquare`，落实局部 $\Pi_v$ 与覆盖条件。最后让尖点、theta 根、赋值截面和局部分解群都属于同一 `orb/localData`。参考 `modelAG/modelTG` 中的构造仍需目标几何接口上的实现。 [来源义务二](具有明确参考来源指示的证明义务.md#二act1scene1共同真实-initial-θ-data-producer)

#### 5. 装配同一份实际 `InitialThetaData/TateFamily`（🟡）

从第 4 项的几何输出和原种子组装数据。记模域、原数域和扭点域为 $M,F,K$，须逐点证明数据中保存的 $M\to K$ 等于规范包含 $M\to F\to K$ 的复合，并沿该等式比较 Tate 族与局部赋值截面的处集限制。使用同一完成域嵌入，逐坏处核对 Tate 曲线的 $j$ 不变量、局部素元、q 阶数的正性及其与 $\ell$ 的互素性、扭点基和 q 根。把局部精确 $2\ell$ 阶点及已证正负两种 distinguished class 接到第 4 项的实际尖点，再核对有限支撑与 q-pilot、link 和 packet 的字段等式。 [来源义务二](具有明确参考来源指示的证明义务.md#二act1scene1共同真实-initial-θ-data-producer) · [模域代数结构的一致性](Prove2Me适配状态.md#初始-θ-数据中模域代数结构的一致性)

### Holomorphoid、period 与 H¹ₑ/BK

#### 6. 构造论文的实际 holomorphoid 来源（🟡）

对第 5 项的数据逐处构造论文的 Fargues–Fontaine 解析点、Berkovich 几何基点、所选 untilt/tilt 和带 anabelomorphic 标记的 Tate 参数族。先证明基准点给出的完成域、整数环及 Fontaine θ 与已有实际局部构造相容。再为参与拼接的每个标记给出所用 Tate 参数、相应 Galois 作用与嵌入，使 period 和上同调的比较能追溯到同一解析来源。 [Joshi I 至 III 来源索引](具有明确参考来源指示的证明义务.md#三act1scene1holomorphoidperiod-和-h¹ₑbk-producer)

#### 7. 识别论文 Fréchet `B`、ρ-范数和 $T_y$（🟡）

现有 `A_inf`、Witt 局部化、`B_dR` 以及标准和实际有理半径完成提供比较对象。须沿第 6 项的同一解析来源证明底环、局部化、拓扑完成和论文 Fréchet $B$ 的比较，并逐半径证明 $\rho$-范数在该映射下的换算。随后须证明比较映射与 Frobenius 交换，在同一环上给出 Tate 对数的收敛域，证明相应元素属于论文 $T_y$ 以及 $T_y\subseteq B^{\varphi=p}$。这些结论须用于第 8 项实际选取的 period 元素。 [Fréchet 计划](开发计划.V1Act1Scene1.md#g2共同真实来源和-producer) · [Joshi II 审计](Joshi2审计.md)

#### 8. H¹ₑ、crystalline 与 Bloch–Kato 比较（🟡）

从同一局部域及 Galois 作用定义论文所用的 H¹ₑ 和 crystalline/Frobenius 比较，给出 BK 指数与对数的精确定义域和核。对每个所选 $2\ell$ 次根 $u$ 及标签 $j$，将 $1+p^*u^j$ 的实际 Kummer 类送入该比较，证明所需的 H¹ₑ 成员关系、整性及 log-shell 身份。系数扩张须明确区分整类、有理像和核中的挠类。若采用整类，须验证论文所写的 $\log_p(1+p^*u^j)/p^*$ 比较。若采用除以 $p^*$ 的有理类，须先对原有理类验证未缩放的普通对数公式，再用 $\mathbb Q_p$ 线性计算其除以 $p^*$ 的像。指定 $\log_p(p)=0$、奇素数时 $p^*=p$、$p=2$ 时 $p^*=4$，并落实实际使用的处与标签。 [来源义务三](具有明确参考来源指示的证明义务.md#三act1scene1holomorphoidperiod-和-h¹ₑbk-producer)

#### 9. 跨 holomorphoid 与 arithmeticoid 的拼接（⚪）

为不同 untilt、不同 holomorphoid 和不同模点定义共同可比较的标记、代表选择与 cohomology transport。必须证明组合相容性、选择代表的独立性及 H¹ₑ、BK 对数和 log-shell 的保持规律，明确 Joshi III 实际使用的 Ind1–Ind3 怎样作用于可比较的数据。固定完备域张量积上的 factor automorphism 和 closure/hull 轨道只给出该固定载体的拼接公式。第 12、13 项需要真实跨来源的 transport。 [来源义务三](具有明确参考来源指示的证明义务.md#三act1scene1holomorphoidperiod-和-h¹ₑbk-producer)

### 论文处集、代表与重数

#### 10. 构造论文 $V_p^{\mathrm{oss}}$ 和 $\underline V^{\mathrm{oss}}$（🟡）

从第 5 项的同一数据实现模域处集到 $L'$ 所选处的双射。逐个有理素数证明 $\underline V^{\mathrm{oss}}$ 的纤维恰是论文选出的奇剩余特征分裂乘法约化处，给出它与 `VBad` 及实际 q 根支撑的双向对应。现有实际纤维覆盖判据给出 `VBadModuliFinset = OddModSupportFinset` 这一等价条件。仍须在论文数据上证明所需覆盖，说明坏处外局部体积何时贡献单位因子，并明确无穷处在总体积中的位置。 [来源义务四](具有明确参考来源指示的证明义务.md#四act1scene1论文处集代表和重数)

#### 11. 实际 $L'$ 代表映射与纤维重数（🟡）

由论文的实际模域、核域 $L'$ 和处集构造代表选择及其限制映射，证明有代表的纤维、代表重数、剩余次数、分歧指数和遗漏项的对应。现有 canonical source-to-section 有限等价可做局部计数。第 4 项的无穷远几何纤维只为相应原函数域的边界提供代数证据。这里仍需核对实际数域的素数纤维，证明论文的代表乘积或求和是否及如何计入重复代表、遗漏质量和剩余域次数。 [来源义务四](具有明确参考来源指示的证明义务.md#四act1scene1论文处集代表和重数)

#### 12. 混合模点下降与统一权重（🟡）

消费第 9–11 项给出的同一论文处集、代表和标记。在每条纤维上推导局部次数、剩余次数、分歧指数、张量维数及纤维质量的公式，再把等式推到跨模点的乘积或求和。既有加权会计等式显式包含代表的次数差额、遗漏质量和全局次数。须证明这些量对论文所选代表取何值。

Joshi III 的 `eq:weights` 给出 $1/[L'_w:(L_{\mathrm{mod}})_v]$。望月新一 IUT III 注记 3.1.1 的系数还含基模域在有理处之上的局部次数和。参考 `LogVolume` 要求正权重且每条有理处纤维权重之和为 1。须在同一处集和测度上证明从论文系数到参考权重的换算，并证明缩放保留反像的对数体积律和张量的乘积公式。左侧 q 项还要另行识别 `QPilotData` 的坏处权重和 IUT IV 定义 1.9 的纤维归一化。 [参考权重审计](Prove2Me适配状态.md#对数体积处权重与局部归一化的来源适配)

### 论文 theta locus、体积与最终证明

#### 13. 将实际 Kummer/log 包络识别为论文 theta locus（🟡）

从第 6、8、9 项取得同一来源的标记、theta 值的 H¹ₑ 类及 BK 对数。在 Joshi III 的 M、J 两类接收空间上，核对基准主单位及 $\{0,\ldots,j\}$ 在乘积与显式序列中的位置。用多重线性映射构造从有限直积到张量积的纯张量像，保留混合处的张量项。随后根据论文的 log-shell、凸闭包及跨来源拼接定义证明实际 packet/hull 的身份，或给出 Form 2 所需的精确包含方向。下界证明须在两个论文集合中找出由同一标记的 $\tau_j=\log_{\mathrm{BK}}(\xi_j)$ 产生的张量格子。 [Joshi 的索引与张量映射义务](Prove2Me适配状态.md#2-joshi-论文直接列出而尚未拆分的证明义务) · [来源义务五](具有明确参考来源指示的证明义务.md#五act1scene1theta-locusvolume-和最终定理)

#### 14. 证明论文包络和 `thetaVolume` 的身份（🟡）

用第 12 项的权重和第 13 项的集合证明测度身份。逐处落实测度的归一化、可测性、非零体积及张量格子的乘积公式，进而证明有穷多个非单位因子的 adelic 乘积公式，接入无穷处因子和标签集递增族上的平均。还须把已证的 Haar 体积及负对数 cost 转换成论文 `thetaVolume` 及其对数，对两个全局集合分别从局部格子包含和体积估计导出乘积下界。 [来源义务五](具有明确参考来源指示的证明义务.md#五act1scene1theta-locusvolume-和最终定理)

#### 15. 完成 Form 2、Corollary 3.12 和必要的下游适配（🔵，现有消费者）

最终声明须保留 Joshi III 的全局初始条件，包括无实嵌入的 $L$、严格 Belyi 型的穿孔椭圆曲线、Galois 扩张 $L/L_{\mathrm{mod}}$、六阶扭点有理性、$\ell\ge 5$ 且 $\ell\nmid[L:L_{\mathrm{mod}}]$、模 $\ell$ 表示的像包含 $\mathrm{SL}_2(\mathbb F_\ell)$、其核的固定域 $L'$ 以及起自模域处集的双射。Form 2 进一步要求充分大的奇素数。设 $\ell^*=(\ell-1)/2$，论文对两个全局集合 $\Theta_M,\Theta_J$ 分别给出体积下界

$$
\operatorname{Vol}(\Theta)\ \ge\
\prod_{w\in\underline V^{\mathrm{oss}}}\left|q_w^{1/(2\ell)}\right|^{\ell^*}
\qquad\bigl(\Theta\in\{\Theta_M,\Theta_J\}\bigr).
$$

Corollary 3.12 的字面左端为 $-\lvert\operatorname{logVol}(\Theta_M)\rvert/\ell^*$，右端为 $-\sum_{p,w}\log|q_w^{1/(2\ell)}|_{L'_w}$，求和取非空 $V_p^{\mathrm{oss}}$ 中的 $(p,w)$。当贡献项为收缩根时，字面右端的负对数与 Form 2 体积推导的右端符号相反。符号冲突沿用暂作笔误的记录，冻结目标前仍须对照字面式、前文采用的符号约定和体积推导。换算须在同一处集上落实每项的原始完成域范数、局部与全局次数、分歧与剩余次数、论文权重及 $2\ell$ 次根和 $p^*$ 对数归一化，再核对无穷处项和取绝对值的条件。 [Joshi 两个目标的来源](Prove2Me适配状态.md#2-joshi-论文直接列出而尚未拆分的证明义务) · [目标代码](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/Corollary312.lean) · [G1 的冻结要求](开发计划.V1Act1Scene1.md#g1目标符号和归一化)

用第 1–14 项构造 q 项、`thetaVolume` 和四项来源法律，并从实际测度给出下界，再实例化现有条件消费者。Scene1 的最终验收覆盖完整类型、导入图、公理和来源追踪。接入参考 `c2` 还须证明 `∀ X, P X → Corollary312Variant X`，其中几何接口固定，`ThetaDataExistence`（P7）为全部适用点和素数提供满足同一 `P` 的数据，以及参考链所需的证书、局部估计和各项身份。已验收的参考链在 `c2` 保留了这个全称命题作为输入，规范高度及 P7 的接合仍开放。 [参考变体与 P7 的适配义务](Prove2Me适配状态.md#joshi-的-312-与参考工程变体之间的适配) · [Scene2 参考链](开发计划.Prove2Me适配.md#41-参考链审计)

### 参考 `c2` 装配中仍开放的曲线输入

- **循环子群估计。** 复挠点界、Legendre 特化和奇乘法约化处的图线判据已接到 Vélu 主界。主界以同一个 $C_0$ 汇总奇坏处 Tate 界、其余有限处的估计和无穷处估计，再用乘积公式得到 $(\ell-2)(h-h_2)/24\le 2\log\ell+T_K$。固定常数的公开 `cyclicBoundOdd` 已供应推论 2.2 所需的 `CurveFactsProp`。 [来源、回执和三语读回](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#the-fixed-constant-cyclic-subgroup-bound)
- **core 例外有限性。** 对给定的 `EtalePi1Theory`，一次穿孔曲线及其符号商的基变换等式把同一供应曲线的非 core 情形归入 `Pi1.excJ`。有限多个有理 $j$ 值各对应非零多项式 $256(X^2-X+1)^3-cX^2(X-1)^2$ 的根，因而只产生有限多个三足点。`coreFiniteness_of_modelAG` 由此提供曲线输入构造器所需的 `CoreFinitenessHyp`。规范装配还需用真实 étale 基本群及其 CanLift 命题 2.7 实例化 `Pi1`。参考 `genuinePi1Theory` 所需的 CanLift 命题涉及原一次穿孔轨形曲线和其符号商，例外值为 $0$、$1728$、$488095744/125$、$1556068/81$。 实际归一化环上的覆盖、沿整闭载体的覆盖下降和多项式次数一判据已验收。已在非分歧 Galois 闭包上证明横坐标下降的归约和覆盖唯一性。第一坐标纤维上的多项式下降与解析提升刚性已用于复数情形的组合证明。须对每条非例外椭圆曲线构造满足commensurator 固定横坐标条件的均匀化，以供应该组合的假设。Lefschetz 的可数覆盖模型已把曲线和两坐标降到同一个代数闭子域，并能在原环境域中恢复扩常数后的覆盖域。扩常数整性下降及 Lefschetz 的条件组合已验收。已证明非零收缩处的分歧指数相等、零收缩处的分歧指数为一、正向 étale 搬运及重参数化相容。二次覆盖映射已在给定低域刚性条件下下降。仍须把实际曲线的有符号与无符号坐标环接到同一二次模型，并完成沿域嵌入的下降及可数子域判定，以实例化特征零基域的 `genuinePi1Theory`。 [模型组合](../prove2me_workspace/Solutions/Source_TripodCoreModel.lean) · [覆盖映射下降](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#descent-of-a-quadratic-cover-map-for-canlift)
- **P7 及高度身份。** Legendre 曲线的逐点 P7 已用同一表示的核固定域构造初始 θ 数据、q-pilot、实际局部理论和 Tate 参数的 $2\ell$ 次根。二挠点有理性、野分歧界、良处分歧指数为一及 $30\ell$ 界已接入同一份局部 θ 数据。塔算术给出 (R4)、(ii) 和 (iii)，其中步骤 (iii) 在同一 q-pilot 的指定素数集上求和。还须落实曲线提供器、核心例外集有限性、Northcott 及远 Abel 存在性的来源，使这些前提对 P7 所需的完整数据族同时成立。参考 `c2` 的条件组合已使用同一局部估计、证书和实际点域、高度、不同理想、导子，给出规范高高度估计。循环子群估计已接入这项组合。它仍依赖全称 `h312` 与素数估计输入。上述字段仍需独立依赖打包、跨版本类型及公理对应和私有平台验收。 [逐点 P7 来源与回执](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#pointwise-p7-with-tower-arithmetic-from-the-legendre-curve)

## 已排除的具体路线

| 状态 | 具体路线及排除范围 |
| --- | --- |
| 🔴 | 在已审计的旧 period 与 transfer 装配中，用实际收缩 q 根的范数直接充作 `thetaBase.norm` 会与所需的非负 `logVolume` 冲突。正长度 ordinary-log 包络的 signed Haar log-volume 也不能直接充作该非负量。 |
| 🔴 | 在已审计的处集和归一化下，现有 canonical q-log 总和严格小于论文候选代表和。实际扭点来源的分歧质量也排除了该来源上的纤维质量为一。 |
| 🔴 | 当前收缩 q-root 的有理类不在已归一化主单位类生成的那条 $\mathbb Q_p$ 直线上。这项排除针对已有普通对数路线的特定单生成空间。 |

负面证据的具体假设和 Lean 入口见 [Scene1 开发计划第 4 节](开发计划.V1Act1Scene1.md#4-负面证据和路线排除)。

## 进度总览4到现在的新进展简报

几何交付的比较区间自 **`a443952`** 至 **`0477a914`**，适配增量见下文。总览4所列未交付的有限闭包和有限素点惯性消费者已进入正式 Scene1 源码。

| 交付 | 总览4之后的精确增量 |
| --- | --- |
| `0de7812f`、`a1ce3f2e` | 在同一有限除法正规闭包中，证明固定原下层域的原有限逆坐标素点惯性元固定原除法点的两个坐标，进而固定整个原无符号域。 |
| `775306be`、`b0e9db57` | 构造原无穷远上层素点的有限闭包提升，证明分歧指数为一，进而证明原平移惯性平凡、几何轨道阶等于 $\ell$。 |
| `4275fb43` | 原下层素点的剩余域沿规范系数映射与同一扭点系数域代数等价，系数次数为一。 |
| `9eff8d37`、`a6ca3e75`、`d1e740fa` | 证明同一种子的二阶点平移给出指定的严格剩余值，将原除法点整坐标与精确纤维方程专化到实际剩余域。 |
| `30a0c0cf`、`022e558b`、`0477a914` | 证明两个平移坐标的剩余值都在系数域中、仿射图在该剩余中心的局部环整闭，以及分式域经原包含的像等于原无符号正规化域。 |

在各交付提交的 Lean `v4.35.0-rc3` 环境中，原分歧指数一、下层剩余域及共同分式域的聚合与公理审查回执依次为 `ci-002988-4a4d0d32`、`ci-003010-d3b776a3`，`ci-003248-4934f3cd`、`ci-003266-95572bcb`，以及 `ci-004720-d1428d42`、`ci-004731-567d6213`。三个 `NormalizationInfinity` 公理审查分别覆盖 286、334、496 条输出，依赖仅含 `propext`、`Classical.choice`、`Quot.sound`。

`d1d6a1a6` 将项目移至 Lean `v4.33.1` 与 Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`，并纳入 FormalSchemes 兼容补丁。`07609510` 更新依赖补丁流程并锁定 Tate 曲线库的兼容补丁。迁移后主库与导入审查、公理聚合、兼容声明审查回执分别为 `ci-006966-5dfcf86a`、`ci-006979-cc34b3c6`、`ci-006981-87320f57`。 [环境锁](../ArithmeticTeichmullerSpaces/migration/environment.lock.json) · [仓库构建约定](../AGENTS.md)

Prove2Me 私有平台已验收参考局部体积平均界、定理 1.10、推论 2.2 及 `statementII_of_cor312` 的条件性证明链。后续本地提交通过了实际 Tate 局部高度比较、Northcott 有限性、素数 2 处贡献和模域次数界的目标环境检查。 [平台适配计划与回执入口](开发计划.Prove2Me适配.md#41-参考链审计)

本地适配从指定扭点域的全体挠点构造判别式平方根，借助同坐标的 Tate 均匀化证明相对分歧整除，进而得到实际三足曲线的 SL₂ 像包含。Legendre 挠点基使 3、5 挠点坐标的次数倍数界 48、480 对每个三足点成立。两向导子比较也已证明，反向误差为 $\log(2\ell)$。 [局部 Tate 与分歧](../prove2me_workspace/Solutions/Source_SL2ImageLocalTate.lean#L81) · [挠点基与次数界](../prove2me_workspace/Solutions/Source_TripodTorsionBasis.lean) · [导子比较](../prove2me_workspace/Solutions/Source_TripodLogCond.lean#L188)

21 字段构造器已消费上述证明。同一供应曲线的定义域次数至多为 `552960 * d`，点的 `logDiff` 等于同一曲线三足域的归一化不同理想次数。构造器和 SL₂ 像通过类型与公理审查 `ci-020827-2725d6f7`，挠点和导子的公开证明通过 `ci-020829-26f0c710`，项目聚合与审查通过 `ci-020844-3d5ac401`。本轮从原合并待办中登记了四项已验收的本地成果，适配计划 §4.1 从 **74/91（81.3%）** 更新为 **78/95（82.1%）**。 [构造器](../prove2me_workspace/Solutions/Source_TripodCurveInputsFromSource.lean#L48) · [来源与回执](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#torsion-field-ramification-and-tripod-curve-inputs)

core 例外有限性的算术归约已通过叶检查、项目聚合及公理审查 `ci-020859-ae4a0f86`。该归约保留所选几何下的例外集包含作为输入。 [有限性归约](../prove2me_workspace/Solutions/Source_TripodCoreFiniteness.lean#L62)

P7 在原表示的核固定域上构造 Tate 族，逐点装配以同一几何的存在性接口为输入，得到初始 θ 数据及 q-pilot，并核对模域次数、去掉 2 和 ℓ 的局部高度、不同理想及导子关系。局部理论接口中的处纤维与权重和也已通过审查。 [P7 来源与回执](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#pointwise-initial-theta-data-and-local-place-fibers)

循环子群父归约保持参考选定的 $C_0$。其中奇坏处图线判据已获本地公理审查，复 Legendre 挠点横坐标界已归约到固定 Heights 的一般复挠点六次幂界。后续复格均匀化、模 $j$ 满射和基本域比较的验收见本节末。Vélu 主界仍开放。 [循环子群归约及回执](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#cyclic-subgroup-bound-at-the-chosen-torsion-constant)

Core 例外有限性已接到给定 `EtalePi1Theory` 的模型，八项声明通过公理审查 `ci-021147-606ee1da`。 [Core 来源及回执](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#core-finiteness-in-the-étale-model)

P7 的局部体积容器和最小包络通过 `ci-021200-5a4e6c8b`。塔的 (R4) 界已由同一挠点域的局部事实与两个次数界推出，审查 `ci-021215-021e43b6` 通过。 [P7 来源及回执](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#the-container-and-tower-local-facts)

实际数域完备化的赋值、局部次数和不同理想支撑已通过审查。同一初始数据上的 theta 区域、不变量和条件证书通过 `ci-021270-ac3cb671`。适配计划 §4.1 达到 **92/109（84.4%）**。 [来源及回执](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#theta-regions-invariants-and-local-arithmetic)

CanLift 的实际归一化载体、覆盖下降和多项式次数一判据通过 `ci-021380-91c6737e`。审查的十四项声明仅使用 Lean 标准公理。适配计划 §4.1 更新为 **93/110（84.5%）**。 [来源及回执](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#canlift-normalization-and-covering-lemmas)

P7 的七字段局部估计通过 `ci-021405-7008ce12`。在给定同一塔的算术前提时，指定素数处的上界由局部体积律、q 次数在基变换下不变及加权平均推出。十六项公理检查均通过，§4.1 达到 **94/111（84.7%）**。 [来源及回执](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#local-estimates-for-the-concrete-theta-region)

逐点 P7 的条件组合接入参考 `c2`，并经 `ci-021440-f6c510e9` 核对类型与五项公理闭包。适配计划 §4.1 达到 **95/112（84.8%）**。实际的局部理论、局部 theta 数据、塔算术与远 Abel 几何仍需从同一来源供应。 [来源与回执](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#concrete-p7-and-its-consumer-in-corollary-22)

复 Legendre 挠点横坐标界已归约到固定 Heights 的一般复挠点界，保持循环子群主界所用的 $C_0$。条件证明与开放归约分别通过 `ci-021483-ab25526b`、`ci-021506-2cdf81e9`，§4.1 达到 **96/113（85.0%）**。 [来源与回执](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#cyclic-subgroup-archimedean-drafts)

P7 的真实数域局部张量及其与 Scene1 真有限处张量的代数、拓扑对应通过 `ci-021534-9f07f95d` 的十七项公理检查。§4.1 达到 **97/114（85.1%）**。 [来源与回执](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#tensor-packet-for-the-concrete-local-theory)

数域塔的条件性步骤 (iii) 和不同理想的局部到全局求和通过 `ci-021569-f47bd4e2` 的五项公理检查。§4.1 达到 **98/115（85.2%）**。 [来源与回执](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#tower-step-iii-and-normalized-different-accounting)

同一 P7 局部数据的 `TL.dst` 已接入步骤 (iii)。审查 `ci-021616-6e2ea5a0` 核对了原坏处见证条件和上界常数。 [来源与回执](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#tower-step-iii-and-normalized-different-accounting)

复格曲线的模 $j$ 恒等式、模群不变性及尖点极限通过九项公理审查 `ci-021617-fb4d9a8a`。§4.1 达到 **100/117（85.5%）**。 [来源与回执](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#modular-j-for-the-complex-torsion-bound)

CanLift 的非分歧 Galois 闭包和基于解析自同构保持 $x$ 的下降通过四项公理审查 `ci-021631-5a00aac0`。§4.1 达到 **101/118（85.6%）**。 [来源与回执](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#canlift-unramified-galois-closure)

实际三足域的 Galois 性与次数界通过 `ci-021651-5fdc99f2`。复格点映射的单射性与模 $j$ 满射通过 `ci-021652-c41c2a60`。§4.1 达到 **103/120（85.8%）**。 [三足域来源](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#galois-structure-of-the-tripodal-field) · [复格点来源](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#the-lattice-point-map-and-modular-j-surjectivity)

同一 q-pilot 的坏处支撑与基本域的两项对数比较分别通过 `ci-021667-f7dd1302`、`ci-021668-80e34e19`。§4.1 达到 **105/122（86.1%）**。 [P7 来源](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#tower-step-iii-and-normalized-different-accounting) · [对数比较来源](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#the-lattice-point-map-and-modular-j-surjectivity)

Serre 迹计算推出的不同理想局部指数界通过五项公理审查 `ci-021693-678cb693`。§4.1 达到 **106/123（86.2%）**。 [来源与回执](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#serres-local-different-bound)

P7 步骤 (ii) 在同一挠点域的不同理想求和后保留误差 $2\log\ell+21$，全局总界通过 `ci-021730-14751bfe`。§4.1 达到 **107/124（86.3%）**。 [来源与回执](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#global-different-bound-in-tower-step-ii)

同一份初始数据上的三项塔算术与逐点 P7 条件装配分别通过 `ci-021742-eb56803e`、`ci-021743-f33906a6`。无穷处局部理论通过 `ci-021744-b251f5a2` 的七项公理审查。§4.1 达到 **110/127（86.6%）**。 [塔算术](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#tower-arithmetic-on-the-selected-theta-data) · [逐点 P7](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#pointwise-p7-with-the-selected-q-pilot) · [无穷处](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#infinite-place-local-theory)

有限处 Haar 体积、最小包络、因子自同构、log-shell 及 Proposition 1.4 已验收。实际 `concreteLocalTheory` 装配两处分支共 41 个字段，逐点 P7 使用同一挠点域的局部理论、Tate 根和 q-pilot。Legendre 曲线的步骤 (iii) 已接入实际良约化与坏处分歧事实。CanLift 的第一坐标多项式下降和解析提升刚性已通过公理审查。§4.1 达到 **116/133（87.2%）**。 [局部理论](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#finite-place-local-theory) · [逐点 θ 数据](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#actual-local-theta-data-on-the-selected-point) · [步骤 (iii)](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#step-iii-for-the-chosen-legendre-curve) · [CanLift](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#canlift-analytic-reduction)

复格加法、一般复挠点六次幂界及 Legendre 特化通过 `ci-021929-7709d914`。复数 CanLift 的条件组合通过 `ci-021953-47fff188`。§4.1 达到 **118/135（87.4%）**。 [复挠点界](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#the-complex-six-power-torsion-bound) · [CanLift 组合](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#complex-canlift-with-the-commensurator-condition)

Vélu 无穷处乘积界和奇阶子群的挠点平移通过 `ci-022033-6796478f` 的公理审查，保留同一 $C_0$。§4.1 达到 **119/136（87.5%）**。 [来源与回执](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#the-archimedean-vélu-bound)

实际 Legendre 曲线的惯性迭代与 $K/F$ 分歧指数界通过项目及公理审查 `ci-022183-c7d6f502`。§4.1 达到 **120/137（87.6%）**。 [来源、回执与三语读回](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#legendre-torsion-field-ramification-away-from-2-and-ℓ)

三足域塔的 $30\ell$ 界和 Vélu 两组指定点分别通过 `ci-022255-2c5b55c1`、`ci-022264-0b6cd23c` 的项目与公理审查。§4.1 达到 **122/139（87.8%）**。 [塔分歧](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#the-ramification-bound-over-the-tripodal-field) · [指定点与半点](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#two-designated-vélu-point-pairs)

指定 Vélu 比值乘积的下降及对数乘积公式通过项目与公理审查 `ci-022356-38c5d13c`，有限处估计仍开放。§4.1 达到 **123/140（87.9%）**。 [来源、回执和三语读回](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#descent-of-the-designated-vélu-ratios)

剩余特征 2 处的温和性和实际 Legendre 域塔的野分歧界通过项目与公理审查 `ci-022416-8f790241`。§4.1 达到 **125/142（88.0%）**。 [温和性](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#tame-ramification-in-residue-characteristic-2) · [野分歧界](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#wild-ramification-of-the-legendre-tower)

Legendre 域塔三项局部事实和逐点 P7 的 (R4)、(ii)、(iii) 算术装配通过项目与公理审查 `ci-022444-83f19d6e`。§4.1 达到 **127/144（88.2%）**。 [塔局部事实](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#local-facts-on-the-actual-legendre-tower) · [逐点 P7](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#pointwise-p7-with-tower-arithmetic-from-the-legendre-curve)

有限处 Vélu 界的搬运、CanLift 的可数覆盖模型及参考 `c2` 接入规范高度估计，分别通过项目与公理审查 `ci-022561-d4e2ce4d`、`ci-022572-9dbbddda`、`ci-022584-92ffefcd`。§4.1 达到 **130/147（88.4%）**。 [Vélu 估计](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#the-legendre-newton-bound-and-transport-of-vélu-estimates) · [可数覆盖模型](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#countable-coefficient-model-for-canlift) · [规范高高度组合](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#reference-corollary-22-on-the-canonical-auxiliary-height)

奇坏处 Vélu 的 Tate 界及向原域的下降、CanLift 扩常数整性和 Lefschetz 条件组合通过项目与公理审查 `ci-022670-0b60f6c5`。§4.1 达到 **133/150（88.7%）**。 [来源、回执和三语读回](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#vélu-estimate-at-odd-multiplicative-places) · [CanLift 整性下降](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#integrality-under-extension-of-constants-for-canlift) · [CanLift 条件组合](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#conditional-lefschetz-assembly-for-canlift)

Vélu 在有限处和无穷处的逐处对数界、CanLift 的 Galois 闭包及其限制映射、实际 Legendre 曲线的模 ℓ 表示通过项目与公理审查 `ci-022720-25476fb9`。§4.1 达到 **136/153（88.9%）**。 [逐处对数界](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#placewise-logarithmic-vélu-estimates) · [CanLift 的 Galois 扩常数](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#galois-closure-under-extension-of-constants-for-canlift) · [Legendre 曲线模 ℓ 表示](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#mod-ell-representation-of-the-legendre-curve-provider)

CanLift 在非零收缩处的分歧指数比较，以及实际 Legendre 曲线定义域中平方根和六挠点的有理性，通过项目与公理审查 `ci-022759-424cfbc4`。§4.1 达到 **138/155（89.0%）**。 [分歧指数](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#ramification-indices-under-extension-of-constants-for-canlift) · [六挠点有理性](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#six-torsion-rationality-of-the-selected-legendre-curve)

低层常数域代数闭时，扩常数后的归一化环覆盖原归一化环的闭点。结合分歧指数和重数相容，仿射轨形曲线的 étale 条件可以下降。项目与公理审查 `ci-022789-a679c21f` 通过。§4.1 达到 **139/156（89.1%）**。 [来源、回执和三语读回](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#descent-of-étale-maps-under-extension-of-constants-for-canlift)

参考 Vélu 主界在同一指定 $C_0$ 下合并有限处和无穷处的估计，并用乘积公式得到奇坏处高度差的上界。项目与公理审查 `ci-022808-047a35ae` 通过。§4.1 达到 **140/157（89.2%）**。 [来源、回执和三语读回](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#the-global-vélu-bound)

复挠点界、Legendre 特化、奇坏处的图线判据和 Vélu 主界已接入公开 `cyclicBoundOdd`，并通过项目与公理审查 `ci-022825-5942080c`。§4.1 达到 **141/158（89.2%）**。 [来源、回执和三语读回](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#the-fixed-constant-cyclic-subgroup-bound)

CanLift 的正向 étale 搬运、重参数化、符号商重数和在给定低域刚性条件下的二次覆盖下降通过项目与公理审查。规范高高度推论 2.2 已由 `cyclicBoundOdd` 供应循环子群估计，保留曲线提供器、核心例外集有限性、远 Abel 存在性、两项素数估计与全称 `h312`。 [覆盖映射下降](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#descent-of-a-quadratic-cover-map-for-canlift) · [规范高高度推论](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#canonical-corollary-22-with-the-proved-cyclic-bound)
