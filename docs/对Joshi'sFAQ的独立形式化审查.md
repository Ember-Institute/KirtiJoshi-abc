# 对 Joshi's FAQ 的独立形式化审查

日期：2026-10-26（Asia/Shanghai）

审查对象：[FAQ about the proof of the abc-conjecture](../refer/Joshi2/joshi-mochizuki-FAQ.md)，本地版本标注日期为 2025-11-01。

本页记录基于本项目现状的阶段性判断，覆盖下文列明的主张，不是对 FAQ 全部文字的逐句验收。
已推送数学基线为 `3212737`。工作区中的 positive pilot volume normalization 单元已通过叶编译，完整审计及提交尚未完成，单列说明。

## 当前判断

FAQ 中不少基础数学陈述有可靠依据，本项目也已独立验证其中若干局部构件。
但那些将局部构件连接成 Corollary 3.12 和 abc 证明的核心主张，尚未由本项目完整验证。

不能将 FAQ 的 41 个问题直接换算成“多少项主张为真”。一个回答通常同时包含标准定理、
几何类比、研究性构造、对其他作者的解释和“关键缺口已经解决”的完成声明。
这些内容必须分别判断，不能给整个回答统一盖章。

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
| **Q37：通过 period rings 或 Galois cohomology 比较并 collate 不同来源的 Tate 参数** | 局部 Kummer、ambient H¹、ordinary log、Witt/Fontaine 及固定 tensor 内的 hull/collation 有实质形式化成果 | H¹ₑ/crystalline/BK、两种方法所需的比较、跨 holomorphoid transport、代表选择和体积控制仍开放。固定 completion 的 automorphism orbit 不等于跨来源 collation |
| **Q29：早期遗漏的 global Frobenius 用法已修复** | 这是关于修订后的完整证明链的完成声明；当前项目尚不能确认 | 须落实所指 global Frobenius 的实际构造、使用位置、比较法律和后续估计，不能只依据修订说明确认 |
| **Q41 及附录：相关回应已经解决 Scholze–Stix 所指出的核心问题** | 当前项目证据不足以确认这一结论 | 区分不同算术结构的存在性，与在这些结构之间建立足以推出目标不等式的比较；前者不自动完成后者。FAQ 对争论各方观点的转述也不作为本工程已核实的历史结论 |

**Q39：本项目没有兴趣也不会审查有关断言**。

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

## 当前项目给出的具体证据

已推送的 [positive pilot integral tensor](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaPositivePilotIntegralTensor.lean)
在同一 supported completion 中，使用 `j=1,…,n`、`n=(ℓ−1)/2` 的实际 integral Kummer 像类。
其 normalized ordinary log 的范数为 `r^(j²)`，其中 `r=‖qroot‖`。
该模块证明了 tensor witness、hull 身份、紧致性、正有限 Haar 性，以及保留实际 local degree 的 log-volume 公式。

正在验收的 [volume normalization 比较单元](../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaPositivePilotVolumeNormalization.lean)
进一步比较以下两个明确数值。记 `d=localDeg(s)`：

\[
V=\text{该 actual hull 的 dimension-normalized Haar volume},
\qquad
W=\prod_{j=1}^{n}r^{\frac1d\frac{j^2}{n^2}}.
\]

叶编译已验证

\[
\log V=n^2\log W,\qquad V=W^{n^2},\qquad 0<V<W<1.
\]

`W` 在这里是同半径、同 inverse-local-degree 权重的 normalized witness product，
没有被识别为论文不同 untilt 的实际 volume。因此这一结果只排除把这里的 `V` 和 `W`
直接等同的具体装配方式，不是 Corollary 3.12 的反例，也不证明它就是历史争论中的同一个缺口。

## 如何据此更新判断

局部构造能够通过 Lean 验证，是正面证据：它支持相关数学构件的正确性，也说明部分路线确实可以严格实现。
但即使核心比较存在缺口，这些局部构件仍可能全部成立，所以它们对完整 abc 证明的支持力度不能按代码量累加。

参考 IUT 代码中“给定某条件即可推出结论”的证明，支持的是条件推导。若条件正是待证明的
source law、paper identity 或体积界，就仍须独立构造并验证该条件。

对最终路线最有区分力的正面证据，是在同一真实来源上完成跨 untilt 比较、H¹ₑ/BK、
paper theta locus/volume 与最终不等式，消除自由数学输入。相应的负面证据则必须是
带有精确条件和排除范围的矛盾或反例。尚未完成某项工作，不应被当作它为假的证据。

本页据此认可已有基础成果，保留核心连接的未验证状态，不给出未经校准的整体成功百分比。
