# 对 Joshi's FAQ 的独立形式化审查

日期：2026-10-27（Asia/Shanghai）

审查对象：[FAQ about the proof of the abc-conjecture](../refer/Joshi2/joshi-mochizuki-FAQ.md)，本地版本标注日期为 2025-11-01。

本页记录基于本项目现状的阶段性判断，覆盖下文列明的主张，不是对 FAQ 全部文字的逐句验收。
本页核对的已提交数学基线为 `40ee645d8ac67064b9df6bc3731d9091d15a1de7`（`Prove positivity of canonical actual hull qLogSum`）。
positive pilot volume normalization 已完成；实际 Witt ρ-norm、全半径共同完备环、
可度量拓扑、连续 ℚₚ 标量作用、实际 Frobenius、由收敛级数构造的 Tate-log，
以及取值于实际 φ=p 子空间的单射、连续 ℤₚ 线性 Tate-log 映射。
后续又证明了实际 ρ-范数的乘法等式、共同环与原有界 Witt 来源的全半径完备化之间的典范比较，
以及对标准 ℚₚ 标量范数的半范数标定和拓扑相容性。
截至当前基线，每个半径坐标也已证明单射；实际 θ 求值是保持典范 ℚₚ 标量的连续开满射，
其商与原 untilt 连续 ℚₚ 代数等价。实际有理 Tate tensor 已闭嵌入 φ=p 子空间并落在 θ 核中；
全体 tilt 主单位上的收敛 period-log 也已证明单射，并与 untilt 中的实际对数级数相容。
进一步，主单位来源上的 period 序列已证明正合；整个实际 φ=p 子空间上的 θ 求值
已证明连续、满射且为开映射。该子空间及其对有理 Tate period 直线的商均已有
与原一致结构相容的标准 ℚₚ Banach 范数。整个 φ=p 子空间上的完整核身份仍未证明。
当前还已完成实际 Witt 指数的局部双向对数互逆、环带指数、整 Witt 像闭合，
以及在具有实际有界 Witt 代表的条件下去除分母并恢复主单位 period。
任意环带指数具有这种精确来源代表的存在性仍未证明。
进一步，canonical actual hull 的 link、thetaVolume、qProduct 下界、volume normalization、transfer log bound
以及条件性 Corollary 3.12 side conditions 已完成；raw qProduct 已归一化为 `exp(-ℓ* qLogSum)`，
并已证明 raw qFactor、raw qProduct 严格介于 0 和 1 之间，raw `qLogSum > 0`。
这些结果仍属于给定实际 hull 的局部和条件性结论。
整个共同环的 θ 核已证明由实际 primitive 元素 ξ 生成；已构造非零收敛轨道乘积 P，
并证明整个 φ=p 的 θ 核中每个元素都唯一可被 P 整除。乘以 P 已给出该完整核与实际闭子空间
`{y : φ(y)=p·f₀·y}` 之间的连续 ℚₚ 线性等价。这将完整核问题落实到具体方程的解分类，
但尚未证明该解空间为一维，也未据此完成 Tate 核身份。

这些局部构造保留给定 `InitialThetaData` 等显式输入；它们尚未从 arithmetic seed
产生完整的共同真实来源模型。

## 当前判断

FAQ 中不少基础数学陈述有可靠依据，本项目也已独立验证其中若干局部构件。
但那些将局部构件连接成 Corollary 3.12 和 abc 证明的核心主张，尚未由本项目完整验证。

对“Joshi 一方有多少主张是真的”，当前能给出的结论是：基础对象和部分局部构造已有正面证据，
period-ring 路线已有从实际 Witt 来源、完备化、Frobenius、θ 求值到 period 映射的具体形式化支持，
应当提高对这些局部步骤可以严格实现的信心；跨来源比较、论文体积估计和证明完成声明仍待验证。
现有证据不足以给出具有统计校准意义的整个 FAQ 真命题百分比；下文的 60% 只是明确标注范围的工作性估计。

不能将 FAQ 的 41 个问题直接换算成“多少项主张为真”。一个回答通常同时包含标准定理、
几何类比、研究性构造、对其他作者的解释和“关键缺口已经解决”的完成声明。
这些内容必须分别判断，不能给整个回答统一盖章。

若必须给出一个工作性比例：在能够明确解析、且确实包含数学断言的 Joshi 一方主张中，
本项目目前估计约 **60%（粗略范围 50%–70%）** 是标准数学事实或很可能为真；约 **25%**
是有合理局部依据但尚未由本项目验证的构造或比较；约 **15%** 是完成声明、历史转述或
依赖未建立身份的结论，当前不能确认。这个比例不是对 41 个问题逐题打分，也不是统计结论；
Q39 按本项目的范围声明排除在审查之外。

## 对最终成功率的直接判断

如果问题限定为“沿 Joshi 路线最终形成一条完整、可审计的 abc 证明”，我的当前主观后验估计是
**5%**，合理的主观区间约为 **2%–10%**。这里的事件是完整证明链闭合，不是某个局部定理成立，
也不是 abc 猜想本身的真值概率。

已完成的 ArithmeticTeichmullerSpaces 代码确实提高了信心：它把共同 Witt 环、全半径完备化、
Frobenius、θ 求值、Tate-log、主单位 period、Banach 商、完整特征核的乘积除法，以及 canonical
actual hull 的定量符号化，推进为可检查的 proof term。相对于只读论文和参考 IUT 代码时的低先验，
这应当是一次正向更新。

更新幅度仍然有限，因为这些结果主要检验“局部对象和局部法律能够一致实现”。在“核心跨来源比较
最终可完成”和“局部理论成立但核心比较仍无法完成”两种情形下，都可能看到相同的 Witt、Frobenius、
θ 和 period-ring 局部成果。因此代码量不能按比例换算成最终成功率；真正有区分力的证据仍是同一真实
来源上的 global holomorphoid、H¹ₑ/BK、paper `B`、跨来源 collation、paper theta locus/volume，
以及最后的 Corollary 3.12 producer 身份全部闭合。

当前信心保持在 5% 而非更高，还有三个可核对的原因：

1. 四个最终闸门仍为 **0/4**，15 项父义务仍全部开放；canonical actual hull 的结果没有关闭真实 producer、
   论文处集或跨来源身份义务。
2. `fullKernel = periodMap.range` 仍未证明。现有结果只给出完整特征 θ 核与具体带因子 Frobenius
   解空间的连续线性等价，以及主单位来源上的正合性；开满射不等于核身份。
3. qProduct/qLogSum 的正性和条件性 Corollary 3.12 side conditions 仍依赖给定的 actual hull 与
   显式输入，尚未从 arithmetic seed 生成论文所需的完整真实 producer。

本项目目前的明确验收数字是：Scene1 最终闸门关闭 **0/4**，
[明确来源证明义务](具有明确参考来源指示的证明义务.md)中的 15 项父义务均未勾选。
这些数字表示完整证明的验收状态，不是 FAQ 的真命题比例，也不是这些开放命题为假的证据。

## 判断标准

| 类别 | 本页含义 |
| --- | --- |
| 有基础数学依据 | 相关对象或一般事实有明确数学来源；不等于其在目标证明中的全部用途已经验收 |
| 已验证局部构件 | 本工程有相应 proof term 和模块验收，结论限于实际定理的输入、类型与归一化 |
| 核心连接未验证 | 已有部分构件，但尚未证明所需的共同来源、比较映射、成员性或最终身份 |
| 需补充表述条件 | 原文字面陈述需要明确归一化、标记、嵌入或适用范围，才能成为精确形式化目标 |
| 尚不能确认完成声明 | 当前项目证据不能支持“相关缺口已修复”或“争论已解决”的结论 |

未完成形式化，不自动证明原主张错误；有一个条件性消费者，也不自动证明其输入条件由实际数据满足。

## 对具体主张的判断

| FAQ 位置与内容 | 基于本项目的判断 | 尚须明确或完成的部分 |
| --- | --- | --- |
| **Q8：不同的完备代数闭赋值域，以及 perfectoid/Fargues–Fontaine 背景** | 基础理论有数学依据；本工程已有实际局部 tilt、Fontaine、Witt 等构件 | 本项目没有因此验收 FAQ 所需的全部非同构 untilt 家族、参数空间及其共同标记。局部对象存在不自动提供整个变化族 |
| **Q13、Q20：以 untilt 数据组织 Tate 参数和赋值比较** | 区分底层对象与附加 untilt/标记数据具有明确意义；本项目能从给定数据派生局部 Tate/q-root source | 尚未构造并验收论文要求的完整 holomorphoid 变化族、参数函数、共同值群比较和全局来源 |
| **Q16–17、Q33：几何例子中的标记、嵌入、基域变换与缩放** | 具体例子有数学依据，能够说明“抽象同构”与“保持指定数据的同构”不同 | 本项目未逐句形式化这些例子。非同构判断须写清标记、嵌入及 j-invariant 条件，不能将例子的结论推广到任意曲线；几何例子本身不推出算术体积估计 |
| **Q18：非平凡 arithmetic scaling 与 theta-link 的关系** | 区分同一赋值的幂重标定与不同 untilt 的相对比较是必要的 | 仍须证明目标 untilt 之间的具体缩放、其保持的数据，以及缩放怎样进入同一 theta/hull/volume 计算；不能以一个实数幂公式替代这些构造 |
| **Q22、Q24：全局拼接、乘积公式和 global Frobenius** | 普通局部构件与有限会计已有支持 | 论文的 global holomorphoid、global Frobenius、全局作用、归一化和所需不变量尚未形成完整的已验收来源链；现有局部 Frobenius 不等于该全局构造 |
| **Q36：构造扩大后的 theta 集合并估计其体积** | 本工程已有 actual packet/hull、紧致性、Haar/cost 公式及若干定量界 | 尚未识别 paper theta locus，也未证明 paper thetaVolume、代表权重和最终不等式在同一真实来源上相容 |
| **Q37：通过 period rings 或 Galois cohomology 比较并 collate 不同来源的 Tate 参数** | 局部 Kummer、ambient H¹、ordinary log 及固定 tensor 内 hull/collation 已有证明；共同 Witt 环已有乘法范数、全半径完备化比较和标准 ℚₚ 半范数拓扑；有理 Tate tensor 闭嵌入实际 φ=p 子空间，主单位来源上的 period 序列正合；整个 φ=p 子空间上的 θ 已是连续线性开满射，Tate 商也是 Banach 空间；完整特征 θ 核已连续线性等价于一个具体带因子 Frobenius 方程的解空间 | 该解空间的分类、完整特征 θ 核等于 Tate 直线、论文 Fréchet `B` 的完整身份、H¹ₑ/crystalline/BK、跨 holomorphoid transport、代表选择和体积控制仍开放。固定 completion 的 automorphism orbit 不等于跨来源 collation |
| **Q29：早期遗漏的 global Frobenius 用法已修复** | 这是关于修订后的完整证明链的完成声明；当前项目尚不能确认 | 须落实所指 global Frobenius 的实际构造、使用位置、比较法律和后续估计，不能只依据修订说明确认 |
| **Q41 及附录：对 Scholze–Stix 争论的回应，以及这些回应是否解决核心问题** | Q41 指向其他回应文献；当前项目证据不足以确认核心问题已解决 | 区分不同算术结构的存在性，与在这些结构之间建立足以推出目标不等式的比较；前者不自动完成后者。FAQ 对争论各方观点的转述也不作为本工程已核实的历史结论 |

**Q39：本项目没有兴趣也不会审查有关断言**

其余涉及学习建议、文献史、类比解释、引用争议或未列出的具体断言，本页不作整体真伪裁决。

## Q8 与 Q18 的归一化说明

Q8 要求嵌入 `ℚₚ → K` 等距。若 `ℚₚ` 使用标准归一化，则沿用该嵌入和归一化时必有

\[
|p|_K=|p|_{\mathbb Q_p}=p^{-1}.
\]

Q18 写出 `|p|K=p⁻λ`，并讨论非平凡相对缩放。如果它沿用上述同一归一化，就只能得到
`λ=1`；若要使用非平凡的 `λ`，必须另行说明共同 tilt 的归一化、各 untilt 的标准归一化
以及两者的转换。

这不是说原文一定矛盾：它可能在比较不同归一化。但形式化不能省略这一层区别，
也不能从“存在不同 untilt”直接推得所需的非平凡数值缩放。

当前工程已在同一共同环上证明一项具体标定。记原坐标半范数为 `Nρ`，令

\[
c_\rho=\frac{\log |p|_{\mathbb Q_p}}{\log\rho}>0,
\qquad P_\rho(x)=N_\rho(x)^{c_\rho}.
\]

则 `Pρ(a • x) = |a|ℚₚ Pρ(x)`，且整族 `Pρ` 与整族 `Nρ` 定义相同拓扑。
这是给定来源上的明确归一化结果；Q18 所需的跨 untilt 缩放及其体积用途仍须另行证明。

## 当前项目给出的具体证据

已推送的 [positive pilot integral tensor](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaPositivePilotIntegralTensor.lean)
在同一 supported completion 中，使用 `j=1,…,n`、`n=(ℓ−1)/2` 的实际 integral Kummer 像类。
其 normalized ordinary log 的范数为 `r^(j²)`，其中 `r=‖qroot‖`。
该模块证明了 tensor witness、hull 身份、紧致性、正有限 Haar 性，以及保留实际 local degree 的 log-volume 公式。

已提交的 [volume normalization 比较单元](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaPositivePilotVolumeNormalization.lean)
进一步比较以下两个明确数值。记 `d=localDeg(s)`：

\[
V=\text{该 actual hull 的 dimension-normalized Haar volume},
\qquad
W=\prod_{j=1}^{n}r^{\frac1d\frac{j^2}{n^2}}.
\]

该单元已证明

\[
\log V=n^2\log W,\qquad V=W^{n^2},\qquad 0<V<W<1.
\]

`W` 在这里是同半径、同 inverse-local-degree 权重的 normalized witness product，
没有被识别为论文不同 untilt 的实际 volume。因此这一结果只排除把这里的 `V` 和 `W`
直接等同的具体装配方式，不是 Corollary 3.12 的反例，也不证明它就是历史争论中的同一个缺口。

当前 canonical actual hull 的[汇总模块](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaCanonicalActualHullSummary.lean)
已把 link、thetaVolume、qProduct 下界、volume normalization、transfer log bound 和条件性
Corollary 3.12 消费者接到同一个显式 `AnalyticInput`。配套的
[qProduct 归一化](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaCanonicalActualHullQProductNormalization.lean)、
[qProduct 界](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaCanonicalActualHullQProductBounds.lean)
和 [qLogSum 符号](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaCanonicalActualHullQLogSumSign.lean)
模块证明 raw `qProduct = exp(-ℓ* qLogSum)`、`0 < qFactor < 1`、`0 < qProduct < 1`
及 `qLogSum > 0`。这些定理的输入仍是给定的 actual hull 数据；它们没有证明该数据就是
论文 theta locus，也没有生成缺失的 arithmetic-seed producer。

后续的 [Witt ρ-norm](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittRhoNorm.lean)
在实际 bounded Witt localization 上给出了非阿基米德环范数；对每个 `0<ρ<1`，
已有保范、稠密且单射的完备化嵌入，以及相应的 Witt 数位展开收敛。
[全半径共同完备环](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittAllRadiusCompletion.lean)
进一步在各半径完备环的乘积中取对角像的闭包，得到完备 Hausdorff 拓扑交换环、
连续坐标半范数和分离性；同一来源的展开在全部半径同时收敛。
[乘法性](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittMultiplicativeNorm.lean)
现已证明原环和各固定半径完备环上的范数乘法等式，并将其传到共同环的每个坐标半范数。
[半径比较](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittRadiusInterpolation.lean)
还证明了中间半径的半范数受两端最大值控制，并给出由夹逼半径子族判定收敛的定理。

在此基础上，[有理半径拓扑](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittRationalRadiusTopology.lean)
证明可数有理半径坐标判定原有拓扑，并得到可度量性；
[标量连续性](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittPadicScalarContinuity.lean)
给出了连续 ℚₚ 嵌入和联合连续标量作用。
共同环上已有实际连续 Frobenius 环自同构及连续逆映射，各半径级数收敛也已有证明。

[全半径完备化比较](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittFrechetComparison.lean)
给出原有界 Witt 环按整族半径拓扑取 Hausdorff 完备化后，与上述共同环之间的典范一致等价和环同构，
并证明该比较固定原环的嵌入、保持半径值，满足相应的连续环映射延拓与唯一性。
[ℚₚ 代数比较](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittFrechetPadicComparison.lean)
进一步保持原有标量作用。
[标定后的半范数族](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittNormalizedSeminorms.lean)
对标准 ℚₚ 范数满足真正的标量齐次性，保持乘法性和非阿基米德性，并以 `WithSeminorms`
证明它们定义原有拓扑。这为 Fréchet ℚₚ 代数所需的局部凸结构提供了具体支持。

[Tate-log](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittTateLogarithm.lean)
从实际 cyclotomic Tate tower 的坐标 `[ε(t)]−1` 出发，证明对数级数在每个半径收敛，
从而定义共同环中的 `tateLog(t)`。
[Frobenius 特征关系](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittTateFrobeniusEigen.lean)
进一步证明 `φ(tateLog(t)) = p · tateLog(t)`；
[加性 Tate period](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittAdditiveTatePeriod.lean)
证明 `tateLog(tu) = tateLog(t) + tateLog(u)`，并将这些同一数值打包成取值于实际 φ=p 子空间的加性群同态。
这些关系由实际坐标、收敛和极限推导，并非作为调用者条件传入。

[Tate-log 单射性](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittTateLogarithmInjective.lean)
和[连续线性化](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittTateLogarithmLinear.lean)
现已进一步证明该映射单射、连续，并对典范嵌入 `ℤₚ → ℚₚ` 满足标量相容性；
`tateLogEigenContinuousLinear_injective` 给出取值于实际 φ=p 子空间的单射连续半线性映射。
将目标限制标量到 ℤₚ 后，这就是上述连续 ℤₚ 线性映射。

[半径忠实性](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittRadiusFaithfulness.lean)
进一步证明共同环到每个固定半径完备环的坐标映射都单射。因此原坐标函数 `Nρ`
各自都是确定的乘法范数，已超出仅有整族坐标共同分离零点的结论。

[θ 满射性](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittThetaSurjective.lean)
和[商拓扑比较](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittThetaQuotientTopology.lean)
证明从共同环到原 untilt 的实际 Fontaine 求值连续、满射且为开映射，核是闭极大理想。
[ℚₚ 代数商比较](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittThetaPadicQuotient.lean)
进一步将商与原 untilt 识别为连续 ℚₚ 代数等价；该标量结构与原有几何嵌入相容，
核非零并包含实际 Tate-log。

[有理 Tate 来源](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittRationalTateSource.lean)
使用实际 `ℚₚ ⊗[ℤₚ] Additive(Tate)`，证明其为一维 ℚₚ 空间。
[有理 period 映射](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittRationalTatePeriod.lean)
将它连续线性闭嵌入共同环的实际 φ=p 子空间，其像也在 θ 核中，并证明限制后的
`eigenEvaluation` 与 `eigenPeriodMap` 复合为零。
这里已经有真正的有理 Tate period 直线，而不只是整数 Tate 模的条件性接口。

[主单位 period](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittPrincipalUnitPeriod.lean)
还将构造扩展到整个 tilt 主单位群 `1+𝔪_F`：实际 `log([u])` 级数在所有半径收敛，
满足乘积转加法及 φ=p 关系，θ 求值等于原 untilt 中 `log(u♯)` 的收敛级数。
这里 `♯` 是乘法映射，以上结论没有假定它可加。
[主单位单射性](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittPrincipalUnitInjective.lean)
进一步证明 `periodLog(u)=0 ↔ u=1`，从而整个主单位 period 映射单射；它在 Tate 元素上
与已有 Tate-log 相同。

[主单位 period 核比较](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittPrincipalPeriodKernel.lean)
证明：对每个主单位 `u`，`θ(periodLog(u))=0` 当且仅当 `periodLog(u)` 属于实际有理 Tate period 直线。
[实际 p 次除法](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittPrincipalPrimeDivision.lean)
由 tilt 的逆 Frobenius 构造唯一的 p 幂根，period-log 将它送到相应的逆 p 幂标量倍。
[主单位求值满射与正合性](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittPrincipalEvaluationSurjective.lean)
进一步证明主单位对数求值满射到原 untilt，其核恰好为实际有理 Tate 来源的像。
这已给出乘法形式群来源上的正合序列；尚未证明每个 φ=p 元素都是主单位的 period-log。

[完整 φ=p 求值满射](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittEigenEvaluationSurjective.lean)
已独立证明整个实际 φ=p 子空间上的 θ 满射到原 untilt。
[特征子空间拓扑](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittEigenRadiusTopology.lean)
证明该子空间完备，任一半径坐标都检测其原有拓扑并给出闭嵌入；
[Banach 范数](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittEigenBanach.lean)
在同一载体上给出标准 ℚₚ 范数空间结构，保持原一致结构。
[有理 Tate 商](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittTateBanachQuotient.lean)
也因此是 Banach 空间，其到原 untilt 的求值连续线性且满射。
[开映射与提升界](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittEigenEvaluationOpen.lean)
还证明上述两个求值映射均为开商映射，并给出原 untilt 元素的 period 原像范数界。

[对数作用于指数的互逆](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittLogExpInverse.lean)
及[指数作用于对数的局部互逆](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittExponentialLocalInverse.lean)
已在明确的小范数范围内证明 `log(exp(x))=x` 和相应的 `exp(log(1+y))=1+y`。
[环带指数](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittAnnularExponential.lean)
进一步将构造组织到相容的半径范围，并证明特征元素的指数满足 Frobenius 幂关系。
这些结果给出了恢复主单位 period 的具体局部方法。

[整 Witt 像闭合](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittIntegralImageClosed.lean)
证明实际 `A_inf` 像在各半径完备环及共同环中闭合。
[有界指数来源与 period 恢复](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittBoundedExponentialPeriod.lean)
则证明：在指定的小范数条件下，如果缩放后特征元素的环带指数具有同一个实际有界 Witt 代表，
便能由 Frobenius 幂关系去除该代表的 p 分母，获得整 Witt 来源，并恢复原特征元素的主单位 period 表示。
这里“具有同一个精确有界来源代表”仍是显式条件。来源稠密性只提供近似，
整像闭合只控制来自整像的极限；两者都不能直接补出该存在性。

[轨道乘积的 Frobenius 方程](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittNormalizedOrbitProductFiniteFrobenius.lean)
和[完整特征核除法](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittEigenKernelInfiniteDivision.lean)
提供了另一条直接处理完整核的路线。记实际 θ 主核的生成元为 ξ，
`fₙ=(-1/p)·φⁿ(ξ)`，`P=∏ₙfₙ`。这里 P 是在原共同环中实际收敛的非零乘积，满足
`φ(P)·f₀=P`、`θ(P)=0`；每个满足 `φ(x)=p·x` 且 `θ(x)=0` 的 x 都有唯一表示 `x=P·y`。

[完整核比较](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittEigenKernelTwistedComparison.lean)
进一步证明，乘以 P 给出连续 ℚₚ 线性等价

\[
\{y\in C:\varphi(y)=p f_0y\}
\;\xrightarrow[\;y\mapsto Py\;]{\;\sim\;}\;
\ker(\theta|_{C^{\varphi=p}}).
\]

这个结论处理的是整个特征 θ 核，保留原载体、标量和拓扑，并未把核替换为已知的主单位 period 像。
但具体方程的解空间是否恰好由 Tate 来源生成，仍须证明。

[轨道乘积的一次零点](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittOrbitProductSimpleThetaZero.lean)
已证明 `P=ξQ` 中的唯一商 Q 满足 `θ(Q)≠0`，从而 `ξ²∤P`。
[完整核上的商求值](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaWittEigenKernelFirstOrder.lean)
则构造连续线性映射 `x↦θ(x/P)`，并证明其核恰好为完整特征 θ 核中可被 ξ² 整除的元素。
目前尚未证明该映射单射或其像的分类；一次零点结果本身不提供这些结论。

为明确这些结论的范围，记 `C` 为本项目共同完备环，`E=C^{φ=p}`，
`K` 为给定的原 untilt，`L` 为实际有理 Tate period 在 `E` 中的像：

| 精确主张 | 当前状态 |
| --- | --- |
| `L ⊆ ker(θ∣E)`，且 `L` 为一维闭 ℚₚ 子空间 | 已证明 |
| 主单位 period-log 单射；其 θ 求值满射到 `K`，核由有理 Tate 来源给出 | 已证明 |
| `θ∣E : E → K` 为连续线性开满射 | 已证明 |
| `E/L` 为 Banach 空间，诱导求值 `E/L → K` 为连续线性开满射 | 已证明 |
| 满足小范数条件且其环带指数具有精确有界 Witt 代表的元素，可恢复为主单位 period-log | 已证明；代表存在性是显式条件 |
| 整个共同环中的 `ker θ=(ξ)` | 已证明；这是整个环的主理想身份 |
| 非零轨道乘积 P 满足 `φ(P)·f₀=P`、`θ(P)=0`、`ξ²∤P` | 已证明 |
| 乘以 P 将 `{y : φ(y)=p·f₀·y}` 连续 ℚₚ 线性等价到 `ker(θ∣E)` | 已证明；不含解空间维数或分类假设 |
| 完整特征 θ 核上的 `x↦θ(x/P)` 连续线性，核恰为其中的 ξ² 倍数 | 已证明；单射性及像的分类尚未证明 |
| `ker(θ∣E)=L`，即上述诱导求值单射 | 尚未证明；两种表述的等价性已证明 |
| 每个 `E` 中的元素都可写成主单位的 period-log | 尚未证明 |

因此，FAQ 的 period-ring 路线已得到多项相互连接的局部正面证据，且满射部分已实际完成。
当前局部关键缺口是整个 φ=p 子空间上的完整核身份和主单位 period 表示。
指数路线已将一项具体剩余问题落实为环带指数的精确有界或整来源代表存在性。
轨道乘积路线则已把整个特征 θ 核连续线性地转化为具体 Frobenius 方程的解空间，剩余解分类仍开放。
整个环的主核等式 `ker θ=(ξ)` 与特征子空间上的核身份 `ker(θ∣E)=L` 是不同命题，前者不自动推出后者。
主单位像上的核比较不能自动推广到整个 φ=p 子空间；开满射也不能自动升级为同构。
论文 `B` 的完整身份、period/BK 比较和跨来源体积用途仍须另行落实。

## 如何据此更新判断

局部构造能够通过 Lean 验证，是正面证据：它支持相关数学构件的正确性，也说明部分路线确实可以严格实现。
尤其是从 Witt 环、全半径收敛一直推到单射连续线性 Tate-log 的实际 φ=p 关系，
再加上乘法性范数、典范完备化比较、标准 ℚₚ 半范数拓扑、实际 θ 商、
有理 Tate period 闭嵌入、主单位来源上的正合性、整个 φ=p 子空间上的开满射及 Banach 商，
已经比仅有抽象接口或条件性消费者提供了更强的路线支持，应据此提高对这些具体步骤的信心。
这些互相连接的成果也提高了对局部 period-ring 实现路线的信心。
后续指数互逆和有界来源去分母进一步缩小了这条局部路线的剩余问题，因而也构成正面更新；
但含有来源代表存在性条件的恢复定理，尚不能算作完整表示定理。
完整核的实际乘积除法及连续线性比较，又将进展推进到完整核本身，因而也应计入正面证据。
它们尚未完成解分类，更未解决跨来源比较和论文体积估计；即使后两者存在缺口，
这些局部构件仍可能全部成立，所以它们对完整 abc 证明的支持力度不能按代码量累加。

用贝叶斯语言说，应比较这些成果在“核心比较能够完成”和“局部理论成立但核心比较无法完成”
两种情形下出现的可能性。若两种情形都很容易产生同样的局部成果，它们对最终成功率的
区分力就有限；若某个成果直接解决两种情形分歧所在的比较或身份问题，更新幅度才应更大。
本项目尚无可校准这些似然及先验的统计模型，因此不能据此给出可信的整体成功百分比。

参考 IUT 代码中“给定某条件即可推出结论”的证明，支持的是条件推导。若条件正是待证明的
source law、paper identity 或体积界，就仍须独立构造并验证该条件。

对最终路线最有区分力的正面证据，是在同一真实来源上完成跨 untilt 比较、H¹ₑ/BK、
paper theta locus/volume 与最终不等式，消除自由数学输入。相应的负面证据则必须是
带有精确条件和排除范围的矛盾或反例。尚未完成某项工作，不应被当作它为假的证据。

本页据此认可已有基础成果，保留核心连接的未验证状态，不给出未经校准的整体成功百分比。
