# `statementII_bridge`

## English

The private declaration `statementII_bridge` in the archived `QueryNativeStatementIIAudit.lean` has no external parameters or hypotheses. It proves a logical equivalence for the fixed height theory `AbcAdaptation.Tripod.tripodTheory`.

$$
\texttt{tripodTheory.StatementII}\ \Longleftrightarrow\
\texttt{AbcAdaptation.Tripod.StatementII}.
$$

The archive member is `native-unit/queries/QueryNativeStatementIIAudit.lean`, line 195, in namespace `AbcAdaptation.Tripod.NativeStatementIIReplayV100`. [Archived source](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/statementii-native-delivery-v105-20261117/archive-content-manifest.json:74) · [Height theory](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_Theory.lean:21) · [General Statement II](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Genl_GeneralPosition_StatementII.lean:23) · [Concrete Statement II](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:200)

A point $x$ has a coordinate $z=x.1$ in the specified algebraic closure of $\mathbb Q$, with $z\ne0,1$. Let $F_z=\mathbb Q(z)$, let $a_z\in F_z$ be the generator mapping to $z$, and let $n_z=[F_z:\mathbb Q]$ be the positive degree of the minimal polynomial of $z$ over $\mathbb Q$. The functions `htCan`, `logDiff`, and `logCond` give $h$, $\delta$, and $\kappa$, respectively.

$$
\begin{aligned}
h(x)&=\frac{\mathrm{Height.logHeight}_1(a_z)}{n_z},&
\delta(x)&=\frac{\log|\operatorname{discr}(F_z)|}{n_z},\\
\kappa(x)&=\frac{1}{n_z}\sum_{v\in B_z}\log N(\mathfrak p_v),&
B_z&=\{v:v(a_z)\ne1\ \lor\ v(a_z-1)\ne1\}.
\end{aligned}
$$

The numerator $\mathrm{Height.logHeight}_1(a_z)$ is the relative logarithmic height in $F_z$. The conductor sum includes every $v\in B_z$ once and is finite. The ideal $\mathfrak p_v$ belongs to the finite place $v$, and $N$ is its absolute ideal norm. Finite and infinite places act by multiplicative absolute values. [Point data](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:25) · [Height and different](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:85) · [Conductor](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:130)

Each compactly bounded subset parameter $K$ consists of a finite set $V$ of rational primes containing $2$ and a real bound $c$, which may be negative. Its point set $K.\mathrm{set}$ consists of the $x$ with the following two properties in $F_z$.

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

The left-hand statement uses the bounded discrepancy relation. The notation $f\lesssim_{S}g$ means that some real $C$ satisfies $f(x)\le g(x)+C$ for every $x\in S$. The height-theory specialization uses pointwise addition and real scalar multiplication of functions. Unfolding it gives

$$
\forall d\in\mathbb N,\quad
\forall\varepsilon\in\mathbb R_{>0},\quad
\forall K:\mathrm{CompactlyBounded},\quad
\exists C\in\mathbb R,\quad
\forall x\in K.\mathrm{set}\cap\{y\in\mathrm{Pt}:n_{y.1}\le d\},\
h(x)\le (1+\varepsilon)(\delta(x)+\kappa(x))+C .
$$

The right-hand statement unfolds to

$$
\begin{aligned}
&\forall d\in\mathbb N,\quad
\forall\varepsilon\in\mathbb R_{>0},\quad
\forall K:\mathrm{CompactlyBounded},\quad
\exists C\in\mathbb R,\quad
\forall x:\mathrm{Pt},\\
&\hspace{2em}x\in K.\mathrm{set}\ \Longrightarrow\
n_{x.1}\le d\ \Longrightarrow\
h(x)\le (1+\varepsilon)(\delta(x)+\kappa(x))+C .
\end{aligned}
$$

On either side, $\varepsilon$ ranges over the positive reals. The real constant $C$ may depend on $d,\varepsilon,K$ and must serve every point with those two membership conditions. The range includes $d=0$, where the point condition is vacuous because $n_z>0$. The proof expands intersection membership into a conjunction, rewrites degree-set membership as $n_z\le d$, and turns the conjunction into the two successive implications. The equivalence transfers a proof of either statement to the other. [Subset conditions](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:163) · [Bounded discrepancy](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Genl_Mathlib_Order_BoundedDiscrepancy.lean:20) · [General form](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Genl_GeneralPosition_StatementII.lean:23) · [Concrete form](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:200)

## 简体中文

归档 `QueryNativeStatementIIAudit.lean` 中的私有声明 `statementII_bridge` 无外部参数或前提。它对指定的高度理论 `AbcAdaptation.Tripod.tripodTheory` 证明一个逻辑等价式。

$$
\texttt{tripodTheory.StatementII}\ \Longleftrightarrow\
\texttt{AbcAdaptation.Tripod.StatementII}.
$$

归档成员为 `native-unit/queries/QueryNativeStatementIIAudit.lean` 第 195 行，命名空间为 `AbcAdaptation.Tripod.NativeStatementIIReplayV100`。 [归档源文件](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/statementii-native-delivery-v105-20261117/archive-content-manifest.json:74) · [高度理论](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_Theory.lean:21) · [一般形式的陈述二](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Genl_GeneralPosition_StatementII.lean:23) · [具体形式的陈述二](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:200)

点 $x$ 的坐标 $z=x.1$ 属于指定的有理数域代数闭包，且 $z\ne0,1$。令 $F_z=\mathbb Q(z)$，以 $a_z\in F_z$ 表示像为 $z$ 的生成元，记 $n_z=[F_z:\mathbb Q]$ 为 $z$ 在 $\mathbb Q$ 上的极小多项式的正次数。函数 `htCan`、`logDiff`、`logCond` 分别给出 $h$、$\delta$、$\kappa$。

$$
\begin{aligned}
h(x)&=\frac{\mathrm{Height.logHeight}_1(a_z)}{n_z},&
\delta(x)&=\frac{\log|\operatorname{discr}(F_z)|}{n_z},\\
\kappa(x)&=\frac{1}{n_z}\sum_{v\in B_z}\log N(\mathfrak p_v),&
B_z&=\{v:v(a_z)\ne1\ \lor\ v(a_z-1)\ne1\}.
\end{aligned}
$$

分子 $\mathrm{Height.logHeight}_1(a_z)$ 是 $F_z$ 上的相对对数高度。导子和是有限和，$B_z$ 中每个 $v$ 贡献一次。$\mathfrak p_v$ 是有限处 $v$ 对应的素理想，$N$ 是理想绝对范数。有限处和无穷处都作为乘性绝对值作用。 [点的数据](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:25) · [高度与不同理想](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:85) · [导子](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:130)

每个紧致有界子集参数 $K$ 由一个含 $2$ 的有理素数有限集 $V$ 和一个实数界 $c$ 组成。$c$ 可以为负。其点集 $K.\mathrm{set}$ 由在 $F_z$ 上同时满足以下两项的点 $x$ 组成。

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

左边的命题使用有界差关系。$f\lesssim_{S}g$ 表示存在 $C\in\mathbb R$，使每个 $x\in S$ 均满足 $f(x)\le g(x)+C$。高度理论在此使用函数的逐点加法和实数数乘。展开左边得到

$$
\forall d\in\mathbb N,\quad
\forall\varepsilon\in\mathbb R_{>0},\quad
\forall K:\mathrm{CompactlyBounded},\quad
\exists C\in\mathbb R,\quad
\forall x\in K.\mathrm{set}\cap\{y\in\mathrm{Pt}:n_{y.1}\le d\},\
h(x)\le (1+\varepsilon)(\delta(x)+\kappa(x))+C .
$$

展开右边得到

$$
\begin{aligned}
&\forall d\in\mathbb N,\quad
\forall\varepsilon\in\mathbb R_{>0},\quad
\forall K:\mathrm{CompactlyBounded},\quad
\exists C\in\mathbb R,\quad
\forall x:\mathrm{Pt},\\
&\hspace{2em}x\in K.\mathrm{set}\ \Longrightarrow\
n_{x.1}\le d\ \Longrightarrow\
h(x)\le (1+\varepsilon)(\delta(x)+\kappa(x))+C .
\end{aligned}
$$

两边的 $\varepsilon$ 均取遍正实数。常数 $C$ 可以依赖 $d,\varepsilon,K$，并须统一适用于满足两个成员条件的所有点。次数范围包含 $d=0$，此时因为 $n_z>0$，点的不等式要求空真。证明展开交集成员资格为合取，将次数集合的成员资格改写为 $n_z\le d$，再将合取前提改写为两个连续蕴含。任一边命题的证明都可通过该等价式推出另一边。 [子集成员条件](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:163) · [有界差关系](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Genl_Mathlib_Order_BoundedDiscrepancy.lean:20) · [一般形式](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Genl_GeneralPosition_StatementII.lean:23) · [具体形式](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:200)

## 日本語

アーカイブされた `QueryNativeStatementIIAudit.lean` の非公開宣言 `statementII_bridge` は、外部パラメータと仮定を持たない。固定した高さ理論 `AbcAdaptation.Tripod.tripodTheory` について次の論理同値を証明する。

$$
\texttt{tripodTheory.StatementII}\ \Longleftrightarrow\
\texttt{AbcAdaptation.Tripod.StatementII}.
$$

アーカイブ内での宣言の位置は `native-unit/queries/QueryNativeStatementIIAudit.lean` の 195 行であり、名前空間は `AbcAdaptation.Tripod.NativeStatementIIReplayV100` である。 [アーカイブされたソース](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/statementii-native-delivery-v105-20261117/archive-content-manifest.json:74) · [高さ理論](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_Theory.lean:21) · [一般形の命題 II](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Genl_GeneralPosition_StatementII.lean:23) · [具体形の命題 II](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:200)

点 $x$ の座標 $z=x.1$ は指定された $\mathbb Q$ の代数閉包に属し、$z\ne0,1$ を満たす。$F_z=\mathbb Q(z)$、$a_z\in F_z$ を像が $z$ となる生成元とし、$n_z=[F_z:\mathbb Q]$ を $z$ の $\mathbb Q$ 上の最小多項式の正の次数とする。`htCan`、`logDiff`、`logCond` の各関数はそれぞれ $h$、$\delta$、$\kappa$ を与える。

$$
\begin{aligned}
h(x)&=\frac{\mathrm{Height.logHeight}_1(a_z)}{n_z},&
\delta(x)&=\frac{\log|\operatorname{discr}(F_z)|}{n_z},\\
\kappa(x)&=\frac{1}{n_z}\sum_{v\in B_z}\log N(\mathfrak p_v),&
B_z&=\{v:v(a_z)\ne1\ \lor\ v(a_z-1)\ne1\}.
\end{aligned}
$$

分子 $\mathrm{Height.logHeight}_1(a_z)$ は $F_z$ における相対対数高さである。導手の和は有限であり、$B_z$ の各 $v$ を一度ずつ数える。$\mathfrak p_v$ は有限素点 $v$ に対応する素イデアルであり、$N$ はイデアルの絶対ノルムである。有限素点と無限素点は乗法的絶対値として作用する。 [点のデータ](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:25) · [高さと不同イデアル](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:85) · [導手](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:130)

コンパクト有界部分集合の各パラメータ $K$ は、$2$ を含む有理素数の有限集合 $V$ と実数の境界 $c$ からなる。$c$ には負の値も許される。点集合 $K.\mathrm{set}$ は $F_z$ で次の二つの条件を満たす点 $x$ からなる。

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

左辺の命題は有界な差の関係を用いる。$f\lesssim_{S}g$ は、ある実数 $C$ が存在して、各 $x\in S$ に対し $f(x)\le g(x)+C$ が成り立つことを表す。この高さ理論では関数の和と実数倍は点ごとに計算する。左辺を展開すると次の命題が得られる。

$$
\forall d\in\mathbb N,\quad
\forall\varepsilon\in\mathbb R_{>0},\quad
\forall K:\mathrm{CompactlyBounded},\quad
\exists C\in\mathbb R,\quad
\forall x\in K.\mathrm{set}\cap\{y\in\mathrm{Pt}:n_{y.1}\le d\},\
h(x)\le (1+\varepsilon)(\delta(x)+\kappa(x))+C .
$$

右辺を展開すると次の命題が得られる。

$$
\begin{aligned}
&\forall d\in\mathbb N,\quad
\forall\varepsilon\in\mathbb R_{>0},\quad
\forall K:\mathrm{CompactlyBounded},\quad
\exists C\in\mathbb R,\quad
\forall x:\mathrm{Pt},\\
&\hspace{2em}x\in K.\mathrm{set}\ \Longrightarrow\
n_{x.1}\le d\ \Longrightarrow\
h(x)\le (1+\varepsilon)(\delta(x)+\kappa(x))+C .
\end{aligned}
$$

両辺で $\varepsilon$ は正の実数全体をわたる。定数 $C$ は $d,\varepsilon,K$ に依存してよく、この二つの所属条件を満たすすべての点に同じ値を用いる。次数の範囲には $d=0$ も含まれ、$n_z>0$ なので、その場合は点に対する不等式の条件は空虚に成り立つ。証明は、共通部分への所属を連言に展開し、次数の集合への所属を $n_z\le d$ に書き換え、その連言を二つの連続する含意に変換する。この同値を用いて、一方の命題の証明から他方の証明を得られる。 [部分集合への所属条件](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:163) · [有界な差の関係](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Genl_Mathlib_Order_BoundedDiscrepancy.lean:20) · [一般形](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Genl_GeneralPosition_StatementII.lean:23) · [具体形](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcTripod.lean:200)

## 消费者与存档回执

目标声明保存在私有审查源码中，审查读取其完整类型和证明，核对两项来源等价证明及三项实际辅助。现行正式源码中的 `statementII_of_children` 直接从有界次数点的有限性和高高度估计给出具体的陈述二。归档保留了与来源证明的原始表达式差异。 [消费关系](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/statementii-native-delivery-v105-20261117/SOURCE_LEDGER.json:12) · [证明差异](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/statementii-native-delivery-v105-20261117/actual-difference-summary.json) · [陈述二的现行组装](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_TripodStatementIIComposition.lean:21)

`ci-018506-8f6104c5` 在独占工作区以无快照模式完成内核和公理审查，退出码 $0$，诊断为空。私有声明只依赖 `propext`、`Classical.choice` 和 `Quot.sound`，且 `no_sorryAx = true`。审查源码的 SHA-256 为 `32e6165fc63243999f5f51a6a64f773329516670557fa0f996bdbde5e2fbdb6b`。回执所列六个定义模块与现行源码逐字节一致。归档内的原三语读回为 `readback/readback.trilingual.md`，本稿按当前术语表使用「紧致有界子集」。 [成功回执及归档成员](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/statementii-native-delivery-v105-20261117/ci-history.json:42) · [独立读回存档](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/statementii-native-delivery-v105-20261117/archive-content-manifest.json:189) · [证据归档](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/statementii-native-delivery-v105-20261117/statementii-closed-native-evidence-v105.tar.gz) · [术语表](/home/admin-wsl/Coq/abc/docs/三语术语名词关键对照.md:45)
