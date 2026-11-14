# Prove2Me 适配状态

## 1. 根据 refer/iut 指示尚未拆分的证明义务

- `refer/iut/Iut/Tripod/ClassicalAbcOfVariant.lean:30`
- `refer/iut/Iut/Tripod/ClassicalAbc.lean:307`
- `refer/iut/Iut/Tripod/Main.lean:129`
- `refer/iut/Iut/Implication/Corollary23.lean:56`
- `refer/iut/Iut/Tripod/Height.lean:603`
- `refer/iut/Iut/Implication/Corollary22.lean:284`
- `refer/iut/Iut/Implication/Corollary22.lean:357`
- `refer/iut/Iut/Implication/Corollary22.lean:386`
- `refer/iut/Iut/Implication/Theorem110.lean:234`
- `refer/iut/Iut/Implication/LogVolumeBound.lean:69`
- `refer/iut/Iut/Implication/LogVolumeBound.lean:205`
- `refer/iut/Iut/Tripod/GeneralPosition.lean:52`
- `refer/iut/Iut/Tripod/GeneralPosition.lean:72`
- `refer/iut/Iut/Tripod/GeneralPosition.lean:108`
- `refer/iut/Iut/Tripod/GeneralPosition.lean:170`
- `Genl@ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf/Genl/Curves/BelyiDescent.lean:248`
- `Genl@ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf/Genl/Curves/Covering.lean:243`
- `Heights@721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/Curve/CondDivisor.lean:61`
- `Heights@721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/Different/Conductor.lean:202`
- `Heights@721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/Curve/KummerPoint.lean:45`
- `Belyi@9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8/Belyi/CurveField/NoncriticalBridge.lean:49`
- `Belyi@9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8/Belyi/NoncriticalP1/Reduction.lean:155`
- `Belyi@9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8/Belyi/NoncriticalP1/Reduction.lean:201`
- `Belyi@9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8/Belyi/NoncriticalP1/Reduction.lean:219`

## 2. Joshi 论文直接列出而尚未拆分的证明义务

### `th:moccor-Mochizuki-form2`

来源为 `refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3617`，它分别给出两个全局集合的体积乘积下界。需要将先前固定的椭圆曲线、初始数据、充分大的奇素数以及加权体积定义写入精确陈述。该节点用于连接局部体积估计、全局乘积和后续 3.12，不能把任意实数参数冒充论文中的体积。

### `cor:cor312`

来源为 `refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3647`，它在前一定理的假设和论文符号约定下陈述对数体积不等式。需要同时核对绝对值、负号、除以半阶的归一化和求和处集，保留字面公式与当前体积解释之间的适配义务。该节点是 Scene1 与 Scene2 的接合目标，尚不能直接替换参考工程的 `Corollary312Variant`。

### 第 3 篇第 3、4、6 节的共同来源构造

来源为 `refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:993`、`:1078` 和 `:1387`，依次固定初始数据并构造后续比较所需的对象。需要从同一算术来源追踪各个处的数据、标记及集合构造，而不是为每个消费者分别假定互不相干的存在性。该组节点供应全局集合和体积节点，并应与现有 Prologue、Scene1 的真实来源义务逐项对应。

### `eq:tensor1`／`eq:codmain1` 与 `th:thetam-construction` 的索引对应

来源为 `refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3030`、`:3054`、`:3068`、`:3312` 和 `:3315`，原文先以 `S_{j+1}={0,…,j}` 定义长度，后在类的乘积和显式序列中使用不同的下标范围。仍需写出这些处之间的索引对应，保留全部基准主单位分量，并明确任何勘误或重索引选择。该义务供应 M 侧张量接收空间和 theta 类的同类型性，由 Scene1 的包拼接与包壳构造负责，不能以静默选取某个有限指标类型关闭。

### `eq:prod-tensor2-mapping` 的映射类别与实际 theta 像

来源为 `refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3064` 和 `:3458`，它把有限直积到张量积的纯张量映射称为向量空间同态。仍需用正确的多重线性类型构造实际映射，并证明论文 theta 像使用的正是该映射，保留全部混合处张量项。该义务供应两类 theta 接收空间和张量范数体积比较，由 Scene1 的包拼接与包壳构造负责；不能给一般纯张量映射安装并不成立的可加同态结构。

## 3. 不属于以上两类来源的证明义务

### 尚未对应到现成来源陈述的具体几何义务

`Fermat.heightNormalization` 仍需把实际点域 `ℚ(u,v)` 与 `ℚ(u^N)` 的高度归一化、幂的高度公式，以及 `[u:v:1]` 与 `[u:1]` 的一致比较接到底层节点；不能把 `(N−3)/N` 系数误换成覆盖次数 `N²` 的倒数。`Fermat.liftDifferent` 仍需拆出实际根的存在性、完整点域的 `N²` 次数界，以及相同扩张上的归一化判别式／导子估计；单用子域判别式单调性不能证明完整点域的上界。

`Proper.modelExists` 仍需实际构造满足完整 Fermat 方程、生成条件、超越性和对 `ℚ(u)` 次数恰为 `N` 的函数域，给出不可约性与次数证明。`Proper.affineIdentification` 仍需证明全部相关赋值处的仿射开与当前代数坐标对等价，并保持完整剩余域的像；不能只给坐标映射而遗漏域的身份。

`Proper.planeAdjunctionExists` 仍需证明固定 Fermat 曲线的实际典范除子、实际无穷超平面除子与非零有理函数之间的逐处伴随公式。原来的 `K`、`H` 和 `J` 契约必须保持；须逐处证明这一具体伴随身份，不能以有限支撑或坐标环有限生成的结论代替。

`Proper.coordinatePoleMultiplicity_eq` 仍需证明：对于满足 `0 < N` 的既有实际 Fermat 模型，两个固定坐标 u、v 在每个真赋值处的实际极点重数 `max(0,-ord)` 相等。必须覆盖全部正则处、坐标为零的情形以及无穷点；不得只证明极点支撑相同或排除零坐标。这是新的明确 Fermat 特化义务，固定的 Belyi／Heights 来源及论文引文均未提供其证明。其结论将实际超平面除子识别为 u 的实际极除子，再由已验收的纤维次数公式和主除子次数为零，结合原有实际伴随数据得到典范次数；`canonicalDivisorDegree` 的归约验收不关闭该子义务，也不证明典范除子或伴随数据的存在性。

`Proper.canonicalHeightIdentification` 的具体 Fermat 特化仍需把实际平面伴随公式、实际超平面高度与固定 `[u:v:1]` 高度连接起来，并对任意明确极除子表示保留统一有界误差。一般除子高度比较、Belyi 高度关系、除子次数高度比较、像点域上的不同理想／导子比较及尖点导子高度比较已有第一类固定来源；其完整点域、像点域、归一化、统一常数、严格次数比及实际生成元的传递仍须按对应来源拆分。

### Joshi 的 3.12 与参考工程变体之间的适配

仍需精确陈述从 Joshi III 第 3 篇的 Corollary 3.12 到参考工程 `Corollary312Variant` 的全称适配。参考定理量化于全部 `InitialThetaData`、局部理论、局部 theta 数据和 `QPilotInputs`；单个已选实例不能覆盖该族。Joshi 字面公式与体积推导的 q 项在绝对值、符号、半阶归一化和求和处集上的已知不一致必须逐项保留。现有 `CanonicalActualHull.corollary312` 使用 `CanonicalActualHull.raw_volume_bound`，可作为一个消费者入口；它仍没有证明论文 theta locus 身份，也没有消除符号及归一化差异。

**现有 Joshi 节点证据及明确障碍**：机器可读的 96 节点类型／来源映射和 18 项阻塞审查保存在 `prove2me_workspace/.local/adaptation/source-audits/joshi_existing_map.json`；它是当前源码的静态审查，不含新编译或公理回执。第 3 篇定理 3.12 的上下文至少要求数域 `L` 无实嵌入、严格 Belyi 型椭圆曲线、初始 theta 数据、`L/L_mod` Galois、全部六阶扭点有理、`ell ≥ 5`、`ell` 不整除 `[L:L_mod]`、模 `ell` 表示像包含 `SL₂`、核域 `L′` 以及处集双射；作者明确说初始 theta 数据是全局存在断言，不能由局部构造代替。参考工程的 `A-raw`、`A-cor`、`A-fontaine`、`G-roots` 有源码 proof body 可供复用，但尚未在本迁移项目重编译；源码中 Form 2 与 Corollary 3.12 本身仍为未证目标。

四个 Scene1 producer owner 仍分别是 `AdelicThetaLink`、`ThetaLiftLog`、`PacketCollationHull`、`VolumeTransfer`：现有跨处 Tate／q 来源和部分规范化、Fontaine 事实只能供应局部前提；纸面 theta locus、Bloch–Kato theta 类与 log-shell 身份、跨 holomorphoid 代表拼接、实际 volume-measure 同一性仍缺少来源构造。显式负面障碍包括：字面 Corollary 3.12 的符号与实际收缩根的负对数相反；raw、全局次数、剩余次数、`2ell`、纸面权重和 `p*` 归一化尚无同一 carrier 上的等式；一般 `L` 情形不能假定度为一；现有选取根集的 q-log 总和严格小于纸面选定处集的总和，且 omitted mass/degree defect 未闭合；实际扭点来源的分歧指数至少为 `ell`，故质数纤维不满足 mass-one；普通 `H¹`／Kummer 类尚非论文的 `H¹_e`／crystalline／Bloch–Kato 输入；固定局部完成域的单位拼接不是论文的跨来源代表拼接；现有实际 raw/Haar 体积界也未识别纸面 theta locus、测度和无穷处归一化。Form2、cor312、G1–G4 均仍开放；不得将既有算术 accounting 的局部通过扩大解释为任何全局 theta 结论。

### Prologue 与 Scene1 必要依赖闭包的映射

仍需把最终目标实际需要的基础定义、构造义务和局部结果转为平台节点，确认精确类型、共同来源、实际消费者和无环依赖。已有闭合声明可以逐项机械追溯到固定 Mathlib 版本；条件性局部定理必须保留输入法律，接口及结构字段也不等于真实对象的存在性证明。不能据现有 Prologue 清单断言最终 Joshi 路线的必要叶节点已经全部覆盖。

特别需要细化 `ProducerContracts.lean` 中只选择命题的 `xxxLaw : Prop` 槽位；它们既没有给出具体论文法律，也没有给出其证明。四类真实来源义务仍归 Scene1，不通过扩大 Prologue 假设关闭；旧 `Prologue/Obligations/Constructors.lean` 的四个占位构造器也不能作为现成证明导入。定义文件只供应实际定义与已证明结构事实，尚未实现的存在性保持开放；若后续真实构造揭示新的基础需求，按动态边界审计契约处理。

## 4. 未完成自然语言读回的证明义务
