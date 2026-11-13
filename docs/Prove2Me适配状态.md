# Prove2Me 适配状态

## 1. 根据 refer/iut 指示尚未拆分的证明义务

- `refer/iut/Iut/Tripod/ClassicalAbcOfVariant.lean:30`
- `refer/iut/Iut/Tripod/ClassicalAbc.lean:307`
- `refer/iut/Iut/Tripod/Main.lean:129`
- `refer/iut/Iut/Implication/Corollary23.lean:56`
- `refer/iut/Iut/Tripod/Northcott.lean:183`
- `refer/iut/Iut/Tripod/Height.lean:603`
- `refer/iut/Iut/Tripod/Height.lean:791`
- `refer/iut/Iut/Implication/Corollary22.lean:111`
- `refer/iut/Iut/Implication/Corollary22.lean:284`
- `refer/iut/Iut/Implication/Corollary22.lean:357`
- `refer/iut/Iut/Implication/Corollary22.lean:386`
- `refer/iut/Iut/Implication/Theorem110.lean:234`
- `refer/iut/Iut/Implication/LogVolumeBound.lean:69`
- `refer/iut/Iut/Implication/LogVolumeBound.lean:205`

## 2. Joshi 论文直接列出而尚未拆分的证明义务

### `th:moccor-Mochizuki-form2`

来源为 `refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3617`，它分别给出两个全局集合的体积乘积下界。需要将先前固定的椭圆曲线、初始数据、充分大的奇素数以及加权体积定义写入精确陈述。该节点用于连接局部体积估计、全局乘积和后续 3.12，不能把任意实数参数冒充论文中的体积。

### `cor:cor312`

来源为 `refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3647`，它在前一定理的假设和论文符号约定下陈述对数体积不等式。需要同时核对绝对值、负号、除以半阶的归一化和求和处集，保留字面公式与当前体积解释之间的适配义务。该节点是 Scene1 与 Scene2 的接合目标，尚不能直接替换参考工程的 `Corollary312Variant`。

### 第 3 篇第 3、4、6 节的共同来源构造

来源为 `refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:993`、`:1078` 和 `:1387`，依次固定初始数据并构造后续比较所需的对象。需要从同一算术来源追踪各个处的数据、标记及集合构造，而不是为每个消费者分别假定互不相干的存在性。该组节点供应全局集合和体积节点，并应与现有 Prologue、Scene1 的真实来源义务逐项对应。

## 3. 不属于以上两类来源的证明义务

### 规范高度估计及一般位置传递的剩余分解

`canonicalLegendreHeightComparison` 仍需追踪实际单生成数域上的有限处高度、Legendre 不变量及其与既有高度的两向比较；`epsilonELargeHeight` 仍需把来源中的具体四次幂阈值与基础实分析依赖接成可验收节点。二者的陈述已固定到实际对象和明确公式，尚未完成其向基础定理的依赖闭包。

`canonicalCorollary22HighHeightEstimate` 仍需继续拆出推论二点二的共同算术来源、初始 theta 数据、局部理论、所选素数和定理一点一零输入。有限例外集必须识别为来源 `excCore` 与 `K.set ∩ ptLE d` 的交，统一阈值和常数必须分别识别为 `I.threshold cheb` 与 `40*pnt.η+I.B/3`；保留完整三项结论，不以存在某个数值证书代替真实来源。参考工程的真实基本群及缓和基本群构造可从 `ClassicalAbcGenuineCanLift.lean:40` 的特化入口继续追踪，本地还需独立移植并核对相同数据上的消费者。

`Fermat.heightNormalization` 仍需把实际点域 `ℚ(u,v)` 与 `ℚ(u^N)` 的高度归一化、幂的高度公式，以及 `[u:v:1]` 与 `[u:1]` 的一致比较接到底层节点；不能把 `(N−3)/N` 系数误换成覆盖次数 `N²` 的倒数。`Fermat.liftDifferent` 仍需拆出实际根的存在性、完整点域的 `N²` 次数界，以及相同扩张上的归一化判别式／导子估计；单用子域判别式单调性不能证明完整点域的上界。

`Proper.modelExists` 仍需实际构造满足完整 Fermat 方程、生成条件、超越性和对 `ℚ(u)` 次数恰为 `N` 的函数域，给出不可约性与次数证明。`Proper.affineIdentification` 仍需证明全部相关赋值处的仿射开与当前代数坐标对等价，并保持完整剩余域的像；不能只给坐标映射而遗漏域的身份。

`Proper.noncriticalRamificationFinite` 仍需证明任意实际非常数函数 ψ 的分歧处集有限。应在全部真赋值处上，使用实际导数 d/dψ 对正则局部环的保持性、图册的有限个模生成元及 ψ 的有限极点集，证明 `{P | 1 < ramIdx ψ P}` 有限；不能以预先给定的有限分歧值集代替该结论。

`Proper.noncriticalCompositionRamification` 仍需证明实际分歧指数为正，以及每个有理 Möbius 变换／正次数有理多项式列表在实际曲线函数上的复合公式。结论必须同时保留复合函数超越性、所有完整剩余域嵌入下的点值公式，以及原函数分歧指数与实际 P¹ 复合指数的乘积公式；不能只验证单个嵌入或逐点选择不同复合函数。

`Proper.noncriticalP1Normalize` 仍需移植固定来源 `Reduction.normalize_step`：对完整 Galois 稳定的有限代数点集和其外的有理点，给出实际有理初等映射及单位圆盘中的新点集，把区分点归一化为 9。必须保留完整 Galois 稳定性、所有次数上界以及次数至少为 2 时的最高次数计数不增；具体预复合延续须同时保留原点集像、区分点不落入 `{0,1,∞}` 和所有实际分歧点的像条件。无穷点不能被省略。

`Proper.noncriticalP1Rational` 仍需移植固定来源 `Reduction.rational_step`：当单位圆盘内有限代数点的有理最小多项式次数均不超过 1 时，构造同一个实际有理 Möbius 变换／正次数有理多项式列表，使含无穷点的整个分支集落入 `{0,1,∞}`、有理点 9 的像在其外，并覆盖所有实际分歧点。不能以任意点函数或额外未审计的规律字段替代该构造。

`Proper.noncriticalP1Minpoly` 仍需移植固定来源 `Reduction.minpoly_step`：对单位圆盘内完整 Galois 稳定、次数至多 d 且含实际次数 d≥2 点的有限集，应用该点的实际有理最小多项式，给出完整 Galois 稳定的新集和其外的有理区分点；保持次数上界，并把最高次数计数上界从 n+1 降到 n。实际初等映射的预复合延续须保留含无穷点的全部三项非临界 Belyi 条件。`noncriticalP1Zero` 已按固定来源完成次数／计数上界的嵌套归纳组合及零点适配；其归约验收只登记这三个 Open 子义务，不关闭它们，也不关闭相邻的分歧有限性、复合分歧公式或既有 `noncriticalSelection` 数学义务。

`Proper.canonicalDivisorExists` 仍需证明 `du` 除子的有限支撑；`Proper.planeAdjunctionExists` 仍需证明实际典范除子与坐标超平面除子之间的具体伴随关系。应逐处追踪分歧系数，并保留原来的实际 `K`、`H` 和 `J` 契约；不能把预先定义的数字当作除子身份或次数等式。`Proper.cuspGeneratorsExists` 还需给出尖点补集的实际坐标环有限生成性，并包含所需的三个三支点函数。

`Proper.coordinatePoleMultiplicity_eq` 仍需证明：对于满足 `0 < N` 的既有实际 Fermat 模型，两个固定坐标 u、v 在每个真赋值处的实际极点重数 `max(0,-ord)` 相等。必须覆盖全部正则处、坐标为零的情形以及无穷点；不得只证明极点支撑相同或排除零坐标。这是新的明确 Fermat 特化义务，固定的 Belyi／Heights 来源及论文引文均未提供其证明。其结论将实际超平面除子识别为 u 的实际极除子，再由已验收的纤维次数公式和主除子次数为零，结合原有实际伴随数据得到典范次数；`canonicalDivisorDegree` 的归约验收不关闭该子义务，也不证明典范除子或伴随数据的存在性。

`Proper.localCompactness`、`Proper.avoidanceRegularity` 和 `Proper.embeddingBoundsToSet` 还需分别落实有界次数点列的局部紧性、避开尖点后的正则性，以及全部共轭嵌入界向同一赋值紧有界集的传递。固定 Mathlib 已有 `PadicAlgCl 2` 及其谱范数，无须另设该载体的存在性假设；但紧性证明和次数缩放仍需实际接入。

`Proper.canonicalHeightIdentification`、`Proper.belyiHeightRelation`、`Proper.divisorDegreeHeightComparison`、`Proper.belyiDifferentConductorComparison` 和 `Proper.cuspConductorHeightComparison` 仍需向底层高度与算术定理分解。保留极除子表示所定义的真实高度、完整点域和像点域的归一化、统一加法常数、严格除子次数比，以及实际坐标环生成元定义的导子；不得以自由函数、次数比取等或只选一个嵌入代替现有陈述。

参考工程最强入口在源码层仅接收全称 `h312`；其完整外部依赖闭包尚未在本地验收，仍需完成 Joshi 字面三点一二与所需参考变体的精确接合。

### Joshi 的 3.12 与参考工程变体之间的适配

仍需精确陈述从 Joshi III 第 3 篇的 Corollary 3.12 到参考工程 `Corollary312Variant` 的全称适配。参考定理量化于全部 `InitialThetaData`、局部理论、局部 theta 数据和 `QPilotInputs`；单个已选实例不能覆盖该族。Joshi 字面公式与体积推导的 q 项在绝对值、符号、半阶归一化和求和处集上的已知不一致必须逐项保留。现有 `CanonicalActualHull.corollary312` 使用 `CanonicalActualHull.raw_volume_bound`，可作为一个消费者入口；它仍没有证明论文 theta locus 身份，也没有消除符号及归一化差异。

**现有 Joshi 节点证据及明确障碍**：机器可读的 96 节点类型／来源映射和 18 项阻塞审查保存在 `prove2me_workspace/.local/adaptation/source-audits/joshi_existing_map.json`；它是当前源码的静态审查，不含新编译或公理回执。第 3 篇定理 3.12 的上下文至少要求数域 `L` 无实嵌入、严格 Belyi 型椭圆曲线、初始 theta 数据、`L/L_mod` Galois、全部六阶扭点有理、`ell ≥ 5`、`ell` 不整除 `[L:L_mod]`、模 `ell` 表示像包含 `SL₂`、核域 `L′` 以及处集双射；作者明确说初始 theta 数据是全局存在断言，不能由局部构造代替。参考工程的 `A-raw`、`A-cor`、`A-fontaine`、`G-roots` 有源码 proof body 可供复用，但尚未在本迁移项目重编译；源码中 Form 2 与 Corollary 3.12 本身仍为未证目标。

四个 Scene1 producer owner 仍分别是 `AdelicThetaLink`、`ThetaLiftLog`、`PacketCollationHull`、`VolumeTransfer`：现有跨处 Tate／q 来源和部分规范化、Fontaine 事实只能供应局部前提；纸面 theta locus、Bloch–Kato theta 类与 log-shell 身份、跨 holomorphoid 代表拼接、实际 volume-measure 同一性仍缺少来源构造。显式负面障碍包括：字面 Corollary 3.12 的符号与实际收缩根的负对数相反；raw、全局次数、剩余次数、`2ell`、纸面权重和 `p*` 归一化尚无同一 carrier 上的等式；一般 `L` 情形不能假定度为一；现有选取根集的 q-log 总和严格小于纸面选定处集的总和，且 omitted mass/degree defect 未闭合；实际扭点来源的分歧指数至少为 `ell`，故质数纤维不满足 mass-one；普通 `H¹`／Kummer 类尚非论文的 `H¹_e`／crystalline／Bloch–Kato 输入；固定局部完成域的单位拼接不是论文的跨来源代表拼接；现有实际 raw/Haar 体积界也未识别纸面 theta locus、测度和无穷处归一化。Form2、cor312、G1–G4 均仍开放；不得将既有算术 accounting 的局部通过扩大解释为任何全局 theta 结论。

### Prologue 与 Scene1 必要依赖闭包的映射

仍需把最终目标实际需要的基础定义、构造义务和局部结果转为平台节点，确认精确类型、共同来源、实际消费者和无环依赖。已有闭合声明可以逐项机械追溯到固定 Mathlib 版本；条件性局部定理必须保留输入法律，接口及结构字段也不等于真实对象的存在性证明。不能据现有 Prologue 清单断言最终 Joshi 路线的必要叶节点已经全部覆盖。

特别需要细化 `ProducerContracts.lean` 中只选择命题的 `xxxLaw : Prop` 槽位；它们既没有给出具体论文法律，也没有给出其证明。四类真实来源义务仍归 Scene1，不通过扩大 Prologue 假设关闭；旧 `Prologue/Obligations/Constructors.lean` 的四个占位构造器也不能作为现成证明导入。定义文件只供应实际定义与已证明结构事实，尚未实现的存在性保持开放；若后续真实构造揭示新的基础需求，按动态边界审计契约处理。

### 尚待同步的后续子链

一般位置、推论二点二及其通向参考三点一二的后续精确节点仍需准备、独占验收、独立三语读回并按依赖顺序接入私有 mission。允许将未定的 Joshi 陈述作为有来源的候选节点继续拆分；一旦发现形状错误，建立修正版、更新依赖并弃用旧节点，不把未解决的对应关系当成既成事实。完整数学证明的剩余债务仍属于另行排除的 Act2 阶段。

## 4. 未完成自然语言读回的证明义务
