# `AbcAdaptation.Tripod.tripodTheory`

## English

The module `Def_AbcAdaptation_Reference_Iut_Tripod_Theory` defines a fixed noncomputable value of `AbcAdaptation.Reference.Genl.HeightTheory` at universe zero. Its curve index type is the one-element type `Unit`. The field `tripod` selects its unique index $*$. The fields `Hyperbolic` and `DivisorFree` are constantly true and constantly false, respectively. The proof `hyperbolic_tripod` is the proof of truth at the selected index. [Height theory structure](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Genl_GeneralPosition_HeightTheory.lean:25) · [Data definition](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_Theory.lean:21)

The point type at $*$ is `Pt`, the subtype of the specified algebraic closure $\overline{\mathbb Q}=\mathrm{AlgebraicClosure}(\mathbb Q)$ consisting of $z\ne0,1$. A point $x$ carries $z=x.1$ and both inequalities. Let $F_z=\mathbb Q(z)\subseteq\overline{\mathbb Q}$ and let $a_z\in F_z$ be the generator whose image is $z$. For every $d\in\mathbb N$ the degree fields and their identities are

$$
\begin{aligned}
n_z&=\operatorname{natDegree}(\operatorname{minpoly}_{\mathbb Q}(z))=[F_z:\mathbb Q]>0,\\
\mathrm{ptLE}(*,d)&=\{x\in\mathrm{Pt}:n_{x.1}\le d\},&
\mathrm{ptEQ}(*,d)&=\{x\in\mathrm{Pt}:n_{x.1}=d\},\\
\mathrm{ptLE}(*,0)&=\varnothing,&
\mathrm{ptLE}(*,d+1)&=\mathrm{ptLE}(*,d)\cup\mathrm{ptEQ}(*,d+1).
\end{aligned}
$$

The definition uses the existing proofs for the last two identities. The three function fields `htCan`, `logDiff`, and `logCond` have domain `Pt` and codomain $\mathbb R$. Their values at $x$ are $h(x)$, $\delta(x)$, and $\kappa(x)$ below. [Point and field](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:25) · [Point degree](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:46) · [Degree sets and identities](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:67)

$$
\begin{aligned}
h(x)&=\frac{\mathrm{Height.logHeight}_1(a_z)}{n_z},\\
\delta(x)&=\frac{\log|\operatorname{discr}(F_z)|}{n_z},\\
\kappa(x)&=\frac{1}{n_z}\sum_{v\in B_z}\log N(\mathfrak p_v),&
B_z&=\{v:v(a_z)\ne1\ \lor\ v(a_z-1)\ne1\}.
\end{aligned}
$$

Here $v$ and $w$ denote finite and infinite places of $F_z$, acting by multiplicative absolute values. The ideal $\mathfrak p_v$ is the prime ideal of $\mathcal O_{F_z}$ corresponding to $v$, and $N$ is the absolute ideal norm. The conductor is a finite-support sum with one term for each bad place $v\in B_z$. In the height formula, $m_w$ is $1$ at a real place and $2$ at a complex place. The product over the finite places has finite support away from $1$. The relative logarithmic height in the numerator is

$$
\mathrm{Height.logHeight}_1(a_z)
=\log\!\left(\prod_{w\ \mathrm{infinite}}\max(1,w(a_z))^{m_w}
              \prod_{v\ \mathrm{finite}}\max(1,v(a_z))\right).
$$

All three functions divide by the positive field degree $n_z$. The log-different can also be written with the absolute norm of the different ideal in place of $|\operatorname{discr}(F_z)|$. [Height and log-different](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:85) · [Number-field height formula](/home/admin-wsl/Coq/mathlib4-0df444a/Mathlib/NumberTheory/Height/NumberField.lean:110) · [Different ideal identity](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:109) · [Bad places and conductor](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:115)

The field `CBS` is the type `CompactlyBounded`. A record $K$ consists of a finite set $V$ of rational primes containing $2$, proofs of these prime conditions, and an arbitrary real bound $c$. The field `cbsSet` assigns a subset of `Pt` to each $K$. Membership of $x$ in this subset is the conjunction of the following conditions in its field $F_z$.

$$
\begin{aligned}
&\forall v\text{ finite},\quad
 \operatorname{char}(\mathcal O_{F_z}/\mathfrak p_v)\in V
 \ \Longrightarrow\
 |\log v(a_z)|\le c\ \land\ |\log v(a_z-1)|\le c,\\
&\forall w\text{ infinite},\quad
 |\log w(a_z)|\le c\ \land\ |\log w(a_z-1)|\le c .
\end{aligned}
$$

The same $c$ applies to both absolute values at each specified place, for every point in the subset. [Compactly bounded subsets](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:163)

## 简体中文

模块 `Def_AbcAdaptation_Reference_Iut_Tripod_Theory` 定义宇宙层级为零的 `AbcAdaptation.Reference.Genl.HeightTheory` 的一个固定的不可计算值。曲线指标类型为单元素类型 `Unit`。`tripod` 字段选取它的唯一指标 $*$。`Hyperbolic` 和 `DivisorFree` 字段分别恒真和恒假。`hyperbolic_tripod` 提供所选指标处真命题的证明。 [高度理论结构](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Genl_GeneralPosition_HeightTheory.lean:25) · [数据定义](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_Theory.lean:21)

指标 $*$ 的点类型为 `Pt`，即指定代数闭包 $\overline{\mathbb Q}=\mathrm{AlgebraicClosure}(\mathbb Q)$ 中满足 $z\ne0,1$ 的元素组成的子类型。点 $x$ 带有 $z=x.1$ 及两条不等关系的见证。令 $F_z=\mathbb Q(z)\subseteq\overline{\mathbb Q}$，以 $a_z\in F_z$ 表示在代数闭包中像为 $z$ 的生成元。对每个 $d\in\mathbb N$，次数字段及其恒等式为

$$
\begin{aligned}
n_z&=\operatorname{natDegree}(\operatorname{minpoly}_{\mathbb Q}(z))=[F_z:\mathbb Q]>0,\\
\mathrm{ptLE}(*,d)&=\{x\in\mathrm{Pt}:n_{x.1}\le d\},&
\mathrm{ptEQ}(*,d)&=\{x\in\mathrm{Pt}:n_{x.1}=d\},\\
\mathrm{ptLE}(*,0)&=\varnothing,&
\mathrm{ptLE}(*,d+1)&=\mathrm{ptLE}(*,d)\cup\mathrm{ptEQ}(*,d+1).
\end{aligned}
$$

定义沿用已有证明给出最后两条恒等式。三个函数字段 `htCan`、`logDiff`、`logCond` 的定义域均为 `Pt`，陪域均为 $\mathbb R$。它们在 $x$ 的取值分别为下式中的 $h(x)$、$\delta(x)$、$\kappa(x)$。 [点与定义数域](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:25) · [点的次数](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:46) · [次数集合及恒等式](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:67)

$$
\begin{aligned}
h(x)&=\frac{\mathrm{Height.logHeight}_1(a_z)}{n_z},\\
\delta(x)&=\frac{\log|\operatorname{discr}(F_z)|}{n_z},\\
\kappa(x)&=\frac{1}{n_z}\sum_{v\in B_z}\log N(\mathfrak p_v),&
B_z&=\{v:v(a_z)\ne1\ \lor\ v(a_z-1)\ne1\}.
\end{aligned}
$$

其中 $v$ 和 $w$ 分别为 $F_z$ 的有限处和无穷处，均作为乘性绝对值作用。$\mathfrak p_v$ 是 $v$ 对应的 $\mathcal O_{F_z}$ 素理想，$N$ 为理想绝对范数。导子使用有限支撑和，$B_z$ 中每个坏处 $v$ 贡献一项。高度公式中实处的 $m_w$ 为 $1$，复处的 $m_w$ 为 $2$。有限处的乘积只有有限项异于 $1$。分子中的相对对数高度为

$$
\mathrm{Height.logHeight}_1(a_z)
=\log\!\left(\prod_{w\ \mathrm{infinite}}\max(1,w(a_z))^{m_w}
              \prod_{v\ \mathrm{finite}}\max(1,v(a_z))\right).
$$

三个函数的分母均为正数域次数 $n_z$。不同理想对数项也可将 $|\operatorname{discr}(F_z)|$ 写为不同理想的绝对范数。 [高度与不同理想对数项](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:85) · [数域高度公式](/home/admin-wsl/Coq/mathlib4-0df444a/Mathlib/NumberTheory/Height/NumberField.lean:110) · [不同理想恒等式](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:109) · [坏处与导子](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:115)

`CBS` 字段取类型 `CompactlyBounded`。一份记录 $K$ 含有有理素数的有限集 $V$、各成员为素数且 $2\in V$ 的证明，以及任意实数界 $c$。`cbsSet` 将每份记录映到 `Pt` 的一个子集。点 $x$ 属于该子集，当且仅当其定义数域 $F_z$ 上下列两项同时成立。

$$
\begin{aligned}
&\forall v\text{ finite},\quad
 \operatorname{char}(\mathcal O_{F_z}/\mathfrak p_v)\in V
 \ \Longrightarrow\
 |\log v(a_z)|\le c\ \land\ |\log v(a_z-1)|\le c,\\
&\forall w\text{ infinite},\quad
 |\log w(a_z)|\le c\ \land\ |\log w(a_z-1)|\le c .
\end{aligned}
$$

同一个 $c$ 约束子集内每个点在每个指定处的两个绝对值的对数。 [紧致有界子集](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:163)

## 日本語

モジュール `Def_AbcAdaptation_Reference_Iut_Tripod_Theory` は、宇宙レベル零における `AbcAdaptation.Reference.Genl.HeightTheory` の固定された非計算的な値を定義する。曲線の添字の型は一元型 `Unit` である。`tripod` フィールドはその唯一の添字 $*$ を選ぶ。`Hyperbolic` と `DivisorFree` のフィールドはそれぞれ恒真と恒偽である。`hyperbolic_tripod` は選ばれた添字で真となる命題の証明である。 [高さ理論の構造](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Genl_GeneralPosition_HeightTheory.lean:25) · [データの定義](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_Theory.lean:21)

添字 $*$ における点の型は `Pt` であり、指定された代数閉包 $\overline{\mathbb Q}=\mathrm{AlgebraicClosure}(\mathbb Q)$ で $z\ne0,1$ を満たす元の部分型である。点 $x$ は $z=x.1$ と二つの不等関係の証拠を持つ。$F_z=\mathbb Q(z)\subseteq\overline{\mathbb Q}$ とし、代数閉包での像が $z$ となる生成元を $a_z\in F_z$ とする。各 $d\in\mathbb N$ について、次数のフィールドとその等式は次のとおりである。

$$
\begin{aligned}
n_z&=\operatorname{natDegree}(\operatorname{minpoly}_{\mathbb Q}(z))=[F_z:\mathbb Q]>0,\\
\mathrm{ptLE}(*,d)&=\{x\in\mathrm{Pt}:n_{x.1}\le d\},&
\mathrm{ptEQ}(*,d)&=\{x\in\mathrm{Pt}:n_{x.1}=d\},\\
\mathrm{ptLE}(*,0)&=\varnothing,&
\mathrm{ptLE}(*,d+1)&=\mathrm{ptLE}(*,d)\cup\mathrm{ptEQ}(*,d+1).
\end{aligned}
$$

定義は最後の二つの等式に既存の証明を用いる。三つの関数フィールド `htCan`、`logDiff`、`logCond` の定義域は `Pt`、終域は $\mathbb R$ である。点 $x$ での値はそれぞれ以下の $h(x)$、$\delta(x)$、$\kappa(x)$ である。 [点と定義体](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:25) · [点の次数](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:46) · [次数による集合と等式](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:67)

$$
\begin{aligned}
h(x)&=\frac{\mathrm{Height.logHeight}_1(a_z)}{n_z},\\
\delta(x)&=\frac{\log|\operatorname{discr}(F_z)|}{n_z},\\
\kappa(x)&=\frac{1}{n_z}\sum_{v\in B_z}\log N(\mathfrak p_v),&
B_z&=\{v:v(a_z)\ne1\ \lor\ v(a_z-1)\ne1\}.
\end{aligned}
$$

ここで $v$ と $w$ はそれぞれ $F_z$ の有限素点と無限素点であり、乗法的絶対値として作用する。$\mathfrak p_v$ は $v$ に対応する $\mathcal O_{F_z}$ の素イデアル、$N$ はイデアルの絶対ノルムである。導手には有限台の和を用い、$B_z$ の悪い素点 $v$ ごとに一項を数える。高さの式の $m_w$ は実素点で $1$、複素素点で $2$ となる。有限素点にわたる積で $1$ と異なる項は有限個である。分子の相対対数高さは

$$
\mathrm{Height.logHeight}_1(a_z)
=\log\!\left(\prod_{w\ \mathrm{infinite}}\max(1,w(a_z))^{m_w}
              \prod_{v\ \mathrm{finite}}\max(1,v(a_z))\right).
$$

三つの関数はいずれも正の体の次数 $n_z$ で割る。不同イデアルの対数項では、$|\operatorname{discr}(F_z)|$ を不同イデアルの絶対ノルムで表すこともできる。 [高さと不同イデアルの対数項](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:85) · [数体の高さの公式](/home/admin-wsl/Coq/mathlib4-0df444a/Mathlib/NumberTheory/Height/NumberField.lean:110) · [不同イデアルの等式](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:109) · [悪い素点と導手](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:115)

`CBS` フィールドは型 `CompactlyBounded` である。レコード $K$ は有理素数の有限集合 $V$、各元の素数性と $2\in V$ の証明、および任意の実数の境界 $c$ を持つ。`cbsSet` は各レコードに `Pt` の部分集合を対応させる。点 $x$ がその部分集合に属するための必要十分条件は、その定義体 $F_z$ 上で次の二つが成り立つことである。

$$
\begin{aligned}
&\forall v\text{ finite},\quad
 \operatorname{char}(\mathcal O_{F_z}/\mathfrak p_v)\in V
 \ \Longrightarrow\
 |\log v(a_z)|\le c\ \land\ |\log v(a_z-1)|\le c,\\
&\forall w\text{ infinite},\quad
 |\log w(a_z)|\le c\ \land\ |\log w(a_z-1)|\le c .
\end{aligned}
$$

同じ $c$ が、部分集合の各点について、指定された各素点での二つの絶対値の対数を制限する。 [コンパクト有界部分集合](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:163)

## 消费者与存档回执

现行 `curveInputsOfSL2Image` 构造以 `tripodTheory` 为高度理论的 `CurveInputs`，规范推论 2.2 组装使用它的点类型和次数限制。来源 `Iut.Tripod.statementII_iff` 使用对应的 `Iut.Tripod.tripodTheory`，归档中的目标私有 `statementII_bridge` 使用现行定义的值。 [曲线输入](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCurveInputs.lean:26) · [规范推论 2.2](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCanonicalCorollary22.lean:39) · [来源消费关系](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/basic55-delivery-v98-20261117/SOURCE_LEDGER.json:2454)

现行理论模块 SHA-256 为 `a9e22491aabe84d68e3ea4c01b813dc0a2de106c85bf78d484b52b8dc668c5e6`，与存档叶检查、产物检查及等价定理归档中留存的模块一致。叶检查 `ci-018046-08138ad2`、产物检查 `ci-018050-c51863f6` 和审查 `ci-018396-b29fa0e0` 均使用独占工作区，退出码为 $0$。审查对 `tripodTheory` 只报告 `propext`、`Classical.choice` 和 `Quot.sound`。此次读回沿用存档独立读回所确认的公式，中文按现行术语表使用「紧致有界子集」。 [公理审查](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/basic55-delivery-v98-20261117/ci-history.json:990) · [产物检查](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/basic55-delivery-v98-20261117/ci-history.json:2080) · [叶检查](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/basic55-delivery-v98-20261117/ci-history.json:2164) · [读回归档](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/basic55-delivery-v98-20261117/basic55-evidence-v98.tar.gz) · [术语表](/home/admin-wsl/Coq/abc/docs/三语术语名词关键对照.md:45)
