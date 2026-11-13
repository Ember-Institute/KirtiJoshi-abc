# Prove2Me 适配状态

## 1. 根据 refer/iut 指示尚未拆分的证明义务

- `refer/iut/Iut/Tripod/ClassicalAbcOfVariant.lean:30`
- `refer/iut/Iut/Tripod/ClassicalAbc.lean:227`
- `refer/iut/Iut/Tripod/ClassicalAbc.lean:291`
- `refer/iut/Iut/Tripod/ClassicalAbc.lean:307`
- `refer/iut/Iut/Tripod/GeneralPosition.lean:269`
- `refer/iut/Iut/Tripod/Main.lean:129`
- `refer/iut/Iut/Implication/Corollary23.lean:56`
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

### 具体代数点的高度估计与有理数高度之间的分解验收

有理数高度到整数 abc 的算术组合已验收；仍需把具体代数点上的 `StatementI` 连接到该有理数高度目标。次数一、对数不同理想项为零、实际高度比较、同一整数根基的对数导子上界是四个精确开放子定理；它们必须和 `statementII_of_children`／`statementI_of_statementII` 的来源链实际组合并经 MCP-CI 验收。当前 `Definitions/Def_TripodRationalComposition.lean` 已保留无占位符的组合代码，并移除了未被使用的开放定理导入；`Solutions/Sol_abc_rational_height.lean` 通过真实开放子节点供应全部六个输入。新规范模块名、组合审查和完整盲审读回已验收；仍需完成平台上传并确认实际归约边。闭合组合只消费明确的开放子节点，不等于几何子定理已证明。

新增的命题二子链只使用已有的具体代数点、次数、归一化高度、对数不同理想项、导子和紧有界集合：`BoundedDegreeFiniteness` 要求全部代数点中次数及实际高度有界的子集有限，`HighHeightEstimate` 给出正次数界与每个紧有界集合上的统一高点阈值和误差常数。两项子定理的类型、有限例外组合与独立三语读回均已验收，证据位于 `.local/adaptation/tripod-unit-20261113/`；数学子定理仍开放。仍需将该子链连接到平台的有理数高度目标，并继续拆分高点估计的来源输入。这是对参考 Corollary 2.3 证明中高点估计与有限例外步骤的提取；辅助椭圆曲线高度到实际高度的转换、有限异常核的吸收、Corollary 2.2 的算术来源仍属于高点估计的未拆分债务，不能以这项中间陈述冒充已经归约到 3.12。

命题二到命题一的论文来源已核实：望月新一 *Arithmetic Elliptic Curves in General Position*，Theorem 2.1，印刷第 11–13 页。作者官网下载 PDF 的直连回执、SHA-256 与路径保存在 `.local/adaptation/sources/Mochizuki_GenEll_Theorem2.1.pdf.receipt.json`。第 12–13 页使用有限覆盖、非临界 Belyi 映射和统一高度比较；本地当前只有 `statementII` 到 `statementI` 的精确开放归约接口，尚未形式化覆盖／Belyi 子链，所以论文出处并不构成该边已证明的证据。

### Joshi 的 3.12 与参考工程变体之间的适配

仍需精确陈述从 Joshi III 第 3 篇的 Corollary 3.12 到参考工程 `Corollary312Variant` 的全称适配。参考定理量化于全部 `InitialThetaData`、局部理论、局部 theta 数据和 `QPilotInputs`；单个已选实例不能覆盖该族。Joshi 字面公式与体积推导的 q 项在绝对值、符号、半阶归一化和求和处集上的已知不一致必须逐项保留。现有 `CanonicalActualHull.corollary312` 使用 `CanonicalActualHull.raw_volume_bound`，可作为一个消费者入口；它仍没有证明论文 theta locus 身份，也没有消除符号及归一化差异。

**现有 Joshi 节点证据及明确障碍**：机器可读的 96 节点类型／来源映射和 18 项阻塞审查保存在 `prove2me_workspace/.local/adaptation/source-audits/joshi_existing_map.json`；它是当前源码的静态审查，不含新编译或公理回执。第 3 篇定理 3.12 的上下文至少要求数域 `L` 无实嵌入、严格 Belyi 型椭圆曲线、初始 theta 数据、`L/L_mod` Galois、全部六阶扭点有理、`ell ≥ 5`、`ell` 不整除 `[L:L_mod]`、模 `ell` 表示像包含 `SL₂`、核域 `L′` 以及处集双射；作者明确说初始 theta 数据是全局存在断言，不能由局部构造代替。参考工程的 `A-raw`、`A-cor`、`A-fontaine`、`G-roots` 有源码 proof body 可供复用，但尚未在本迁移项目重编译；源码中 Form 2 与 Corollary 3.12 本身仍为未证目标。

四个 Scene1 producer owner 仍分别是 `AdelicThetaLink`、`ThetaLiftLog`、`PacketCollationHull`、`VolumeTransfer`：现有跨处 Tate／q 来源和部分规范化、Fontaine 事实只能供应局部前提；纸面 theta locus、Bloch–Kato theta 类与 log-shell 身份、跨 holomorphoid 代表拼接、实际 volume-measure 同一性仍缺少来源构造。显式负面障碍包括：字面 Corollary 3.12 的符号与实际收缩根的负对数相反；raw、全局次数、剩余次数、`2ell`、纸面权重和 `p*` 归一化尚无同一 carrier 上的等式；一般 `L` 情形不能假定度为一；现有选取根集的 q-log 总和严格小于纸面选定处集的总和，且 omitted mass/degree defect 未闭合；实际扭点来源的分歧指数至少为 `ell`，故质数纤维不满足 mass-one；普通 `H¹`／Kummer 类尚非论文的 `H¹_e`／crystalline／Bloch–Kato 输入；固定局部完成域的单位拼接不是论文的跨来源代表拼接；现有实际 raw/Haar 体积界也未识别纸面 theta locus、测度和无穷处归一化。Form2、cor312、G1–G4 均仍开放；不得将既有算术 accounting 的局部通过扩大解释为任何全局 theta 结论。

### Prologue 与 Scene1 必要依赖闭包的映射

需要把现有基础定义、构造义务和已证明局部结果映射到平台节点，并逐项确认其实际消费者和共同来源条件。源工程已有义务清单尚未转成当前 `prove2me_workspace` 的完整声明依赖图，不能据此认定必要叶节点全部覆盖。定义文件只供应已验证定义和结构性事实，未证明的构造存在性保留为开放定理；不得把结论藏进任意命题字段或全局实例。尚需对最终目标可达的节点建立来源记录、精确类型、状态及无环依赖关系，并将已完成证明接入对应节点。

### 私有平台节点与本地分解图的同步

用户已启动私有 mission `eeb5193f-68c0-41d0-9263-4a5ff7c801ee` 的证明流程。仍需按依赖顺序同步其余定义、开放子定理和已验收组合，逐条保存平台终态与实际消费者；完整数学证明仍要求关闭其余开放叶节点。根节点的第一条归约边已验收，证据保存在 `prove2me_workspace/.local/adaptation/root-fix-sketch-20261113/`，不再列为待办。

## 4. 未完成自然语言读回的证明义务

- 无。
