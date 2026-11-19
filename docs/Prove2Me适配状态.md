# Prove2Me 适配状态

## 1. 根据 refer/iut 指示尚未拆分的证明义务

- `refer/iut/Iut/Tripod/Main.lean:129`
- `refer/iut/Iut/Tripod/ClassicalAbcGenuineCanLift.lean:28`
- `refer/iut/Iut/Implication/Corollary22.lean:284`
- `refer/iut/Iut/Implication/Corollary22.lean:357`
- `refer/iut/Iut/Implication/LogVolumeBound.lean:69`
- `refer/iut/Iut/Tripod/GeneralPosition.lean:52`
- `refer/iut/Iut/Tripod/GeneralPosition.lean:72`
- `refer/iut/Iut/Tripod/GeneralPosition.lean:108`
- `refer/iut/Iut/Tripod/GeneralPosition.lean:170`
- `Genl@ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf/Genl/Curves/BelyiDescent.lean:248`
- `Genl@ea2846c877d1e16d8f0b911a5fed07f5ee69eaaf/Genl/Curves/Covering.lean:243`
- `Heights@721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/Curve/CondDivisor.lean:61`
- `Heights@721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/Curve/KummerPoint.lean:45`
- `Belyi@9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8/Belyi/CurveField/NoncriticalBridge.lean:49`
- `Belyi@9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8/Belyi/NoncriticalP1/Reduction.lean:155`
- `Belyi@9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8/Belyi/NoncriticalP1/Rational.lean:130`
- `Belyi@9ce4d3f793d3bc831f2fc7214b7dbad90ea012d8/Belyi/NoncriticalP1/Reduction.lean:219`

## 2. Joshi 论文直接列出而尚未拆分的证明义务

### `th:moccor-Mochizuki-form2`

来源为 `refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3617`，它分别给出两个全局集合的体积乘积下界。需要将先前固定的椭圆曲线、初始数据、充分大的奇素数以及加权体积定义写入精确陈述。该节点用于连接局部体积估计、全局乘积和后续 3.12，不能把任意实数参数冒充论文中的体积。

### `cor:cor312`

来源为 `refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3647`，它在前一定理的假设和论文符号约定下陈述对数体积不等式。需要同时核对绝对值、负号、除以半阶的归一化和求和处集，保留字面公式与当前体积解释之间的适配义务。该节点是 Scene1 与 Scene2 的接合目标，尚不能直接替换参考工程的 `Corollary312Variant`。

### 第 3 篇第 3、4、6 节的共同来源构造

来源为 `refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:993`、`:1078` 和 `:1387`，依次固定初始数据并构造后续比较所需的对象。需要从同一算术来源追踪各个处的数据、标记及集合构造，而不是为每个消费者分别假定互不相干的存在性。该组节点供应全局集合和体积节点，并应与现有 Prologue、Scene1 的真实来源义务逐项对应。

### `eq:tensor1`／`eq:codmain1` 与 `th:thetam-construction` 的索引对应

来源为 `refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3030`、`:3054`、`:3068`、`:3312` 和 `:3315`，原文先以 `S_{j+1}={0,…,j}` 定义长度，后在类的乘积和显式序列中使用不同的下标范围。仍需写出这些处之间的索引对应，保留全部基准主单位分量，并明确任何勘误或重索引选择。该义务供应 M 侧张量接收空间和 theta 类的同类型性，由 Scene1 的包拼接与包络构造负责，不能以静默选取某个有限指标类型关闭。

### `eq:prod-tensor2-mapping` 的映射类别与实际 theta 像

来源为 `refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3064` 和 `:3458`，它把有限直积到张量积的纯张量映射称为向量空间同态。仍需用正确的多重线性类型构造实际映射，并证明论文 theta 像使用的正是该映射，保留全部混合处张量项。该义务供应两类 theta 接收空间和张量范数体积比较，由 Scene1 的包拼接与包络构造负责；不能给一般纯张量映射安装并不成立的可加同态结构。

## 3. 不属于以上两类来源的证明义务

### 尚未对应到现成来源陈述的具体几何义务

`Fermat.heightNormalization` 仍需把实际点域 `ℚ(u,v)` 与 `ℚ(u^N)` 的高度归一化、幂的高度公式，以及 `[u:v:1]` 与 `[u:1]` 的一致比较接到底层节点；不能把 `(N−3)/N` 系数误换成覆盖次数 `N²` 的倒数。`Fermat.liftDifferent` 仍需拆出实际根的存在性、完整点域的 `N²` 次数界，以及相同扩张上的归一化判别式／导子估计；单用子域判别式单调性不能证明完整点域的上界。

`Proper.modelExists` 仍需实际构造满足完整 Fermat 方程、生成条件、超越性和对 `ℚ(u)` 次数恰为 `N` 的函数域，给出不可约性与次数证明。`Proper.affineIdentification` 仍需证明全部相关赋值处的仿射开与当前代数坐标对等价，并保持完整剩余域的像；不能只给坐标映射而遗漏域的身份。

`Proper.planeAdjunctionExists` 仍需证明固定 Fermat 曲线的实际典范除子、实际无穷超平面除子与非零有理函数之间的逐处伴随公式。原来的 `K`、`H` 和 `J` 契约必须保持；须逐处证明这一具体伴随身份，不能以有限支撑或坐标环有限生成的结论代替。

`Proper.coordinatePoleMultiplicity_eq` 仍需证明：对于满足 `0 < N` 的既有实际 Fermat 模型，两个固定坐标 u、v 在每个真赋值处的实际极点重数 `max(0,-ord)` 相等。必须覆盖全部正则处、坐标为零的情形以及无穷点；不得只证明极点支撑相同或排除零坐标。这是新的明确 Fermat 特化义务，固定的 Belyi／Heights 来源及论文引文均未提供其证明。其结论将实际超平面除子识别为 u 的实际极除子，再由已验收的纤维次数公式和主除子次数为零，结合原有实际伴随数据得到典范次数；`canonicalDivisorDegree` 的归约验收不关闭该子义务，也不证明典范除子或伴随数据的存在性。

`Proper.canonicalHeightIdentification` 的具体 Fermat 特化仍需把实际平面伴随公式、实际超平面高度与固定 `[u:v:1]` 高度连接起来，并对任意明确极除子表示保留统一有界误差。尖点导子高度比较仍须按第一类固定来源拆分，保留完整点域、归一化、统一常数与实际生成元。

### Joshi 的 3.12 与参考工程变体之间的适配

仍需精确陈述从 Joshi III 第 3 篇的 Corollary 3.12 到参考工程 `Corollary312Variant` 的全称适配。参考 `c2` 在固定的远 Abel 几何与缓和几何接口下要求 `∀ X, P X → Corollary312Variant X`；`ThetaDataExistence`（P7）须为全部适用点和素数供应满足同一 `P` 的数据，并同时供应证书、局部估计及各项身份。因此，所需范围是 P7 实际供应的完整数据族；单个已选实例不足，也不能把待证不等式藏进 `P`。Joshi 字面公式与体积推导的 q 项在绝对值、符号、半阶归一化和求和处集上的已知不一致必须逐项保留。现有 `CanonicalActualHull.corollary312` 使用 `CanonicalActualHull.raw_volume_bound`，可作为一个消费者入口；它仍没有证明论文 theta locus 身份，也没有消除符号及归一化差异。

第 3 篇定理 3.12 的上下文至少要求数域 `L` 无实嵌入、严格 Belyi 型椭圆曲线、初始 theta 数据、`L/L_mod` Galois、全部六阶扭点有理、`ell ≥ 5`、`ell` 不整除 `[L:L_mod]`、模 `ell` 表示像包含 `SL₂`、核域 `L′` 以及处集双射；作者明确说初始 theta 数据是全局存在断言，不能由局部构造代替。Form 2 与 Corollary 3.12 的实际来源构造及全称适配仍待拆分。

`IsSourceP7Variant CI anab X` 已给出 `c2` 所需的来源范围。尚须证明 `∀ X, IsSourceP7Variant CI anab X → Corollary312Variant X`，保留任意次数界，并核对同一 P7 数据下 q-pilot 左端和对数体积右端的论文身份。现有 Scene1 桥要求 `[D.F : ℚ] = 1` 和指定实际 hull 的体积等式，一般次数的换算及该体积等式仍须落实。 [规范 P7 消费者](../prove2me_workspace/Solutions/Source_TripodCanonicalCorollary22PrimeEstimates.lean#L26) · [现有 Scene1 桥](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaCanonicalCorollary312Bridge.lean#L20)

四个 Scene1 producer owner 仍分别是 `AdelicThetaLink`、`ThetaLiftLog`、`PacketCollationHull`、`VolumeTransfer`：现有跨处 Tate／q 来源和部分规范化、Fontaine 事实只能供应局部前提；纸面 theta locus、Bloch–Kato theta 类与 log-shell 身份、跨 holomorphoid 代表拼接、实际 volume-measure 同一性仍缺少来源构造。显式负面障碍包括：字面 Corollary 3.12 的符号与实际收缩根的负对数相反；raw、全局次数、剩余次数、`2ell`、纸面权重和 `p*` 归一化尚无同一 carrier 上的等式；一般 `L` 情形不能假定度为一；现有选取根集的 q-log 总和严格小于纸面选定处集的总和，且 omitted mass/degree defect 未闭合；实际扭点来源的分歧指数至少为 `ell`，故质数纤维不满足 mass-one；普通 `H¹`／Kummer 类尚非论文的 `H¹_e`／crystalline／Bloch–Kato 输入；固定局部完成域的单位拼接不是论文的跨来源代表拼接；现有实际 raw/Haar 体积界也未识别纸面 theta locus、测度和无穷处归一化。Form2、cor312、G1–G4 均仍开放；不得将既有算术 accounting 的局部通过扩大解释为任何全局 theta 结论。

### 对数体积处权重与局部归一化的来源适配

`refer/iut/Iut/Cor312/LogVolume.lean` 的实际接口给定严格正的实数处权重，要求每条有理处纤维上的权重之和为一，再把标签上的权重相乘。文件说明把预期权重写为局部次数除以全局次数；望月新一《集合论多宇宙间算术 Teichmüller 理论》第三篇注记 3.1.1（二）（印刷及文件第 94 页）使用的系数则为 `1 / ([K_ṽ : (F_mod)_v] · ∑_{w|v_Q} [(F_mod)_w : Q_v_Q])`。当前尚未给出这两种表达在实际处集、扩张和体积归一化上的换算，不能从说明文字直接认定二者相同。

仍需在共同来源的处集上构造满足该接口全部字段的权重和局部体积，并证明标签集对应的数据包体积、标签集递增族上的平均体积及全局体积确实读回所选论文公式。若通过同时调整权重与局部体积建立对应，必须保留并证明素数倍乘的反像使对数体积增加该素数的对数等既有归一化法律，以及纤维重数和张量乘积的组合公式。原文页图、公式及固定源码差异保存在 `prove2me_workspace/.local/adaptation/reference-volume-tate-carriers-20261115/paper-context.json`。

还须区分左侧输入的权重和上述体积接口的权重：`refer/iut/Iut/Cor312/LeftHandSide.lean:58` 的 `QPilotData` 只要求坏处权重严格为正，没有给出局部次数除以全局次数的等式，也没有纤维权重和为一的法律。`refer/iut/Iut/Implication/Invariants.lean:115` 的 `logQAt` 只按剩余特征分组；其求和等于 `QPilotData.logQ` 的恒等式不能识别论文的归一化纤维量。望月新一第四篇定义 1.9（二）（印刷及文件第 22 页）的分母是固定非空纤维内的局部次数之和，须另外证明它与所用全局次数、实际 q 参数及主界系数的换算；不能仅按源码说明中的名称认定身份。原始引文和完整来源命令见 `prove2me_workspace/.local/adaptation/reference-main-bound-carriers-20261115/paper-materials-v1/paper-context.json`。

### 初始 θ 数据中模域代数结构的一致性

`refer/iut/Iut/Cor312/ThetaData/Basic.lean:96` 保存模域到扭点域的代数结构 `algebraModK`，随后保存 `towerModK` 标量塔字段。实际编译类型表明，后者使用从原数域到扭点域的规范标量作用限制到模域后得到的作用，其类型没有引用所保存的 `algebraModK`；因此不能据该字段宣称已证明所保存的代数结构与规范包含相容。Tate 族采用规范包含所诱导的模域代数结构，而局部数据和赋值截面接收所保存的结构，二者的身份必须另行核对。

`pointThetaData_algebraMap_moduli_torsion` 已证明规范 P7 的模域映射等于规范包含的复合，q-pilot 已用完整模域纤维的局部次数和写出代表处权重。论文适配仍需匹配原数域、模域、扭点域及完成域，核对代表处截面和坏处支持。P7 排除剩余特征 $2,\ell$，Joshi 的奇分裂乘法约化处集仍可能包含 $\ell$ 上方的处。对应须处理这一差异，并核对 Haar 绝对值的剩余次数换算及原文的符号冲突。 [规范 P7 映射](../prove2me_workspace/Solutions/Source_ReferenceIutPointModuliMap.lean#L16) · [代表处权重](../prove2me_workspace/Solutions/Source_ReferenceIutCor312PointRepresentativeWeight.lean#L21) · [原文及公式对照](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/readbacks/p7-cor312-source-comparison.md)

### Prologue 与 Scene1 必要依赖闭包的映射

仍需把最终目标实际需要的基础定义、构造义务和局部结果转为平台节点，确认精确类型、共同来源、实际消费者和无环依赖。已有闭合声明可以逐项机械追溯到固定 Mathlib 版本；条件性局部定理必须保留输入法律，接口及结构字段也不等于真实对象的存在性证明。不能据现有 Prologue 清单断言最终 Joshi 路线的必要叶节点已经全部覆盖。

特别需要细化 `ProducerContracts.lean` 中只选择命题的 `xxxLaw : Prop` 槽位；它们既没有给出具体论文法律，也没有给出其证明。四类真实来源义务仍归 Scene1，不通过扩大 Prologue 假设关闭；旧 `Prologue/Obligations/Constructors.lean` 的四个占位构造器也不能作为现成证明导入。定义文件只供应实际定义与已证明结构事实，尚未实现的存在性保持开放；若后续真实构造揭示新的基础需求，按动态边界审计契约处理。

### CanLift 复一致化与可公度子

给定复一致化和正次数多项式，若其值在可公度子作用下不变且纤维为群轨道，则横坐标在可公度子作用下不变。这个条件结论已接入复 CanLift。还须对每条非例外复椭圆曲线提供实际一致化，构造上半平面到格点补集的全纯覆盖、纤维轨道和两个 deck 生成元，再沿模函数 $j$ 与 Weierstrass 换元把覆盖搬到该曲线。生成多项式的路线还需要证明 deck 群在其可公度子中的相对指数有限，以及可公度子作用后横坐标的多项式增长界。这两个结论分别支持有限陪集多项式与系数下降。 [第一坐标刚性与复数组合](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#first-coordinate-rigidity-from-an-invariant-polynomial)

陪集多项式已证明有限指数下的轨道分离，Lüroth 生成元已证明多项式子代数中的复合表示。任意两份已给出的复一致化之间已有一个同时相容于覆盖和覆盖变换群的共轭。仍需为目标椭圆曲线构造至少一份这样的覆盖，并在同一覆盖上供应可公度子指数和坐标增长条件。 [来源、回执和三语读回](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#coset-polynomials-and-complex-uniformization-uniqueness)

### 规范 P7 的有限处整包与曲线 q-pilot

有限处的公开单分量公式已验收。整包计算还须在同一 `ThetaLocalData` 上把每个标签配置的体积拆成加权和，消去其他标签的边际，按模域的完整纤维合并局部次数，得出 $-j^2\operatorname{logQAt}(p)/(2\ell)$。全局计算随后须与无穷处公式合并，并由 P7 的坏处有限集控制有理处求和的支撑。

有理 Legendre 族已有 $v_5(j(x_m))=-2m$ 的证明。仍须沿实际点域嵌入把该赋值搬回曲线提供器，证明相应有限处确为该曲线的 P7 坏处，读取同一 Tate 参数的次数，并把所求项纳入 q-pilot。条件标量界使用的全局体积前提仍须从上面的整包计算得到。 [来源、回执和三语读回](../prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md#rational-legendre-family-and-the-conditional-principal-volume-bound)

## 4. 未完成自然语言读回的证明义务

- `AbcAdaptation_Reference_Iut_Concrete_TateInputsSupply`：无待决译名。
- `AbcAdaptation_Reference_Iut_Tripod_CurveProviderHeight`：无待决译名。
- `AbcAdaptation_Reference_Iut_Tripod_TatePoleOrder`：无待决译名。
- `AbcAdaptation_Reference_Iut_Tripod_GoodReductionHeight`：无待决译名。
- `AbcAdaptation_Reference_Iut_Tripod_FiniteHeightMapEquiv`：无待决译名。
- `Source_TripodRelativeDegreeTower`：无待决译名。
- `Source_TripodRelativeDegreeSum`：无待决译名。
- `Source_TripodRelativeAbsoluteValue`：无待决译名。
- `Source_TripodFiniteHeightExtension`：无待决译名。
- `tripodalFieldOf_eq`、`tpdEquiv_jT`、`h_eq_finHeight_div`：无待决译名。
- `LegendreHeightHyp`、`legendreHeight`、`canonicalLegendreHeightComparison_of_provider`：无待决译名。
- `northcott_of_equiv`、`curveInputs_height_eq`、`curveInputs_htCan_equiv`、`curveInputs_northcott`：无待决译名。
- `TwoAdicBoundHyp`、`twoAdicBound'`、`twoAdicBound`、`curveInputs_B_nonneg`、`curveInputs_heightEq_two_le`：无待决译名。
- `curveInputs_dmod_le`：无待决译名。
- `curveInputs_deg_le`、`curveInputs_logDiff_eq`、`curveInputsOfSL2Image`、`CyclicBoundOddHyp`：无待决译名。
- `EllipticCurveData.prime_dvd_card_range`、`EllipticCurveData.prime_dvd_ramificationIdx`：无待决译名。
- `AbcAdaptation_Reference_TateCurvesTheta_QParameter_NormalizedOrder`：无待决译名。
- `AbcAdaptation_Reference_Iut_Cor312_ThetaData_AdmissiblePrime`：无待决译名。
- `AbcAdaptation_JoshiTeich_Prologue_Arithmetic_Basic`：无待决译名。
- `AbcAdaptation_Reference_Genl_GeneralPosition_StatementII`：无待决译名。
- `AbcAdaptation.Reference.Iut.statementII_of_cor312`：无待决译名。
- `AbcAdaptation_Reference_Iut_Tripod_Theory`：无待决译名。
- `AbcAdaptation.Tripod.statementII_bridge`：无待决译名。
- `AbcAdaptation_Reference_Iut_Concrete_CurveData`：无待决译名。
- `AbcAdaptation_Reference_Iut_Concrete_UniformizerSupply`：无待决译名。
- `TowerArithmetic.localEstimate`：`capsule`（待定：胶囊／囊）。
- `ConcreteThetaDataExistence.toThetaDataExistence`、`CurveInputs.concreteThetaDataExistence`：无待决译名。
- `ThetaLocalData.withBadChars`、`ThetaLocalData.step_iii_of_qPilotInputs`：无待决译名。
- `pointThetaData`、`concreteThetaDataExistence_of_pointwise`。
- `archComponentVol_archLogShell`、`exists_leastHull_infinite`、`prop15`。
