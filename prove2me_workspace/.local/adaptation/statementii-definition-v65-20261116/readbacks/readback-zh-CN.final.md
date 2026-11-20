# StatementII 定义的简体中文读回

本稿由原中文译文定稿，按 TERM-016 采用「紧致有界子集」。独立英文读回由原档记录为 gpt-6.1-sol。 [原中文](readback-zh-CN.md) · [独立英文](readback-en.md) · [TERM-016](../../../../../docs/三语术语名词关键对照.md#L45) · [Lean 定义](../../../../Definitions/Def_AbcAdaptation_Reference_Genl_GeneralPosition_StatementII.lean#L23)

固定一个宇宙层级 \(u\) 和一个高度理论结构 \(T\)。其形式数据包括：该宇宙中的一个类型 \(\operatorname{Curve}\)；对每个 \(X\in\operatorname{Curve}\) 给定的同一宇宙中的类型 \(\operatorname{Pt}(X)\)；\(\operatorname{Curve}\) 上的两个谓词 \(\operatorname{Hyperbolic}\)、\(\operatorname{DivisorFree}\)；以及对每个 \(X\) 和自然数 \(n\) 给定的 \(\operatorname{Pt}(X)\) 的子集 \(\operatorname{ptLE}(X,n)\)、\(\operatorname{ptEQ}(X,n)\)。结构要求，对所有 \(X,n\)，

\[
\operatorname{ptLE}(X,0)=\varnothing,\qquad
\operatorname{ptLE}(X,n+1)=\operatorname{ptLE}(X,n)\cup\operatorname{ptEQ}(X,n+1).
\]

结构还给出三个实值函数 \(h_X,\delta_X,\kappa_X:\operatorname{Pt}(X)\to\mathbb R\)，分别对应 `htCan`、`logDiff`、`logCond`；一个指定元素 \(P=\operatorname{tripod}\in\operatorname{Curve}\)，满足 \(\operatorname{Hyperbolic}(P)\)；同一宇宙中的一个类型 \(\mathcal K=T.\mathrm{CBS}\)；以及映射 \(S=T.\mathrm{cbsSet}:\mathcal K\to\mathcal P(\operatorname{Pt}(P))\)。

这里的数据是抽象类型、谓词、子集和函数。该结构没有给出拓扑、支撑映射、固定素数集合、定义域或数值次数函数。这些数据的名称不附加几何或算术规律。所提供的结构也没有对 \(h_X,\delta_X,\kappa_X\) 施加符号或相容性条件。代码将 \(\mathcal K\) 的元素称为“紧致有界子集”，其底层子集为 \(S(K)\)；它们的形式要求仅为上述类型和映射。

对这个固定的 \(T\)，`StatementII` 定义如下命题：对每个自然数 \(d\in\mathbb N\) 和每个实数 \(\varepsilon\in\mathbb R\)，如果 \(\varepsilon>0\)，那么对每个 \(K\in\mathcal K\)，都存在一个实数 \(C\in\mathbb R\)，使得每个 \(x\in\operatorname{Pt}(P)\) 都满足

\[
x\in S(K)\cap\operatorname{ptLE}(P,d)
\quad\Longrightarrow\quad
h_P(x)\le (1+\varepsilon)\bigl(\delta_P(x)+\kappa_P(x)\bigr)+C.
\]

量词顺序为：固定 \(T\)，选取 \(d\)，选取 \(\varepsilon\)，假设 \(\varepsilon>0\)，选取 \(K\)，得到 \(C\)，然后考察指定子集中的所有 \(x\)。常数 \(C\) 可以依赖 \(T,d,\varepsilon,K\)，但对 \(x\) 统一适用。它可以是任意实常数，定义既不要求 \(C>0\)，也不要求 \(C\ge0\)。定义中唯一的数值正性前提是 \(\varepsilon>0\)，没有 \(d>0\) 的要求。

有限自然数界 \(d\) 通过指定子集 \(\operatorname{ptLE}(P,d)\) 限制所考察的点。这并不表示该子集是有限集；代码也没有将它等同于具有某种域论次数的点集。当 \(d=0\) 时，上述结构规律给出该子集为空，因此关于 \(x\) 的条件真空成立。若 \(S(K)\) 或它与限制子集的交集为空，同样真空成立。结构没有要求 \(\mathcal K\) 有元素。

上式展开了记号 `≲`：对同一类型上的实值函数 \(f,g\) 及其子集 \(A\)，\(f\lesssim_A g\) 表示存在实数 \(C\)，使每个 \(x\in A\) 都满足 \(f(x)\le g(x)+C\)。其方向是用右侧函数加常数给出左侧函数的上界。`StatementII` 只要求这个方向，不要求反向上界，也不要求绝对差有界。另行给出的关系 `≈` 要求两个方向的上界，但这里使用的不是该关系，定义也没有对该关系取商。公式中的函数加法和乘以 \(1+\varepsilon\) 都按点进行。

该声明的显式结构参数为 \(T\)，宇宙层级 \(u\) 为隐式参数。变量 \(d,\varepsilon,K,C,x\) 都在命题内部被量化，不是额外的外部参数。一般的偏差关系具有隐式的底层类型参数，此处取为 \(\operatorname{Pt}(P)\)；函数和子集则为该关系的显式参数。`StatementII` 没有额外的数学类型类假设；实数运算和函数的按点运算使用导入的标准实例。
