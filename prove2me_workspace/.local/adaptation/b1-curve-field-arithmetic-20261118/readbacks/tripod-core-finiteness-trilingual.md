# Tripod core finiteness

## English

### `finite_legendreJ_preimage`

Let $A\subset\mathbb Q$ be any finite set. A tripod point is an element $x\in\overline{\mathbb Q}\setminus\{0,1\}$. Define its Legendre $j$-value by

$$
J(x)=\frac{256(x^2-x+1)^3}{x^2(x-1)^2}.

$$
The set of all tripod points $x$ for which $J(x)=a$ in $\overline{\mathbb Q}$ for some $a\in A$ is finite. It is empty if $A$ is empty. [Lean declaration](../../../../Solutions/Source_TripodCoreFiniteness.lean#L40) · [Legendre value](../../../../Definitions/Def_TripodCanonicalHighHeightInputs.lean#L23)

### `finite_curve_j_preimage`

Let $P$ be any curve provider. It supplies finiteness of the $3$- and $5$-torsion for the curve construction, arithmetic data for each resulting curve $E_x$ over its number field $F_x$, and the corresponding mod-$\ell$ representation data for each prime $\ell$. Here $E_x$ and $F_x$ are the curve and field in $P.\mathrm{curve}(x)$ for the same tripod point $x$. For every finite $A\subset\mathbb Q$, the set of all tripod points $x$ such that $j(E_x)$ equals the image in $F_x$ of some $a\in A$ is finite. It is empty if $A$ is empty. [Lean declaration](../../../../Solutions/Source_TripodCoreFiniteness.lean#L50) · [Curve provider](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviders.lean#L28)

### `coreFiniteness_of_exceptionalJ`

Fix a curve provider $P$ as above, an anabelian geometry $AG$ at universe level zero, a finite $A\subset\mathbb Q$, a natural degree bound $d$, and a compactly bounded datum $K$. The datum $K$ consists of a finite set of rational primes $V$ containing $2$ and a real bound $b$. Its underlying set $C_K$ consists of the tripod points $x$ at which $\left|\log |x|_v\right|$ and $\left|\log |x-1|_v\right|$ are both at most $b$ at every infinite place and every finite place $v$ of $\mathbb Q(x)$ whose residue characteristic belongs to $V$. [Compactly bounded subsets](../../../../Definitions/Def_AbcTripod.lean#L169)

For a tripod point $x$, let $X_x$ be the once-punctured curve of $E_x$ in $AG$ and $Q_x$ its sign quotient. Say that the universal core condition holds at $x$ if, for every field $L$ of characteristic zero at universe level zero and every embedding $f:F_x\to L$, the base change of $Q_x$ along $f$ is a core of the base change of $X_x$ along $f$, according to the core relation in $AG$. Assume that **every** tripod point where this condition fails has $j(E_x)$ equal in $F_x$ to the image of some $a\in A$. Then the set of such failures in $C_K$ with $[\mathbb Q(x):\mathbb Q]\le d$ is finite. The degree bound and compactly bounded condition restrict the conclusion. For $d=0$ the degree locus is empty. If $A$ is empty, the inclusion hypothesis rules out every failure. [Lean declaration](../../../../Solutions/Source_TripodCoreFiniteness.lean#L62) · [Universal core condition](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean#L32) · [Finiteness predicate](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts.lean#L50)

## 简体中文

### `finite_legendreJ_preimage`

给定任意有限集 $A\subset\mathbb Q$。三足点是 $x\in\overline{\mathbb Q}\setminus\{0,1\}$。其 Legendre $j$ 值为

$$
J(x)=\frac{256(x^2-x+1)^3}{x^2(x-1)^2}.

$$
三足点 $x$ 中，在 $\overline{\mathbb Q}$ 内满足 $J(x)=a$ 且 $a\in A$ 的点构成有限集。当 $A$ 为空时，该点集为空。 [Lean 声明](../../../../Solutions/Source_TripodCoreFiniteness.lean#L40) · [Legendre 值](../../../../Definitions/Def_TripodCanonicalHighHeightInputs.lean#L23)

### `finite_curve_j_preimage`

给定任意曲线供应器 $P$。它提供曲线构造所需的三阶和五阶挠点有限性、各所得曲线 $E_x$ 在其数域 $F_x$ 上的算术数据，以及每个素数 $\ell$ 对应的模 $\ell$ 表示数据。对同一个三足点 $x$，$E_x$ 和 $F_x$ 是 $P.\mathrm{curve}(x)$ 给出的曲线和数域。对每个有限集 $A\subset\mathbb Q$，所有满足 $j(E_x)$ 在 $F_x$ 中等于某个 $a\in A$ 的像的三足点 $x$ 构成有限集。当 $A$ 为空时，该点集为空。 [Lean 声明](../../../../Solutions/Source_TripodCoreFiniteness.lean#L50) · [曲线供应器](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviders.lean#L28)

### `coreFiniteness_of_exceptionalJ`

固定如上的曲线供应器 $P$、宇宙层级零的远 Abel 几何 $AG$、有限集 $A\subset\mathbb Q$、自然数次数界 $d$ 及紧致有界数据 $K$。$K$ 由包含 $2$ 的有限素数集 $V$ 和实数界 $b$ 组成。其底层集合 $C_K$ 由以下三足点 $x$ 组成。在 $\mathbb Q(x)$ 的每个无穷处和剩余特征属于 $V$ 的每个有限处 $v$，$\left|\log |x|_v\right|$ 和 $\left|\log |x-1|_v\right|$ 均不超过 $b$。 [紧致有界子集](../../../../Definitions/Def_AbcTripod.lean#L169)

对三足点 $x$，令 $X_x$ 为 $AG$ 中 $E_x$ 的一次穿孔曲线，$Q_x$ 为其符号商。若对宇宙层级零的每个特征零域 $L$ 及每个嵌入 $f:F_x\to L$，沿 $f$ 基变换后的 $Q_x$ 在 $AG$ 的核关系下是基变换后的 $X_x$ 的一个核，则称 $x$ 满足普遍核条件。假设对**所有**不满足该条件的三足点 $x$，$j(E_x)$ 在 $F_x$ 中等于某个 $a\in A$ 的像。则 $C_K$ 中满足 $[\mathbb Q(x):\mathbb Q]\le d$ 且不满足普遍核条件的三足点构成有限集。次数界及紧致有界条件用于限制结论。当 $d=0$ 时，次数限制选出的点集为空。当 $A$ 为空时，由包含假设可知所有三足点都满足普遍核条件。 [Lean 声明](../../../../Solutions/Source_TripodCoreFiniteness.lean#L62) · [普遍核条件](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean#L32) · [有限性命题](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts.lean#L50)

## 日本語

### `finite_legendreJ_preimage`

任意の有限集合 $A\subset\mathbb Q$ を取る。三脚上の点は $x\in\overline{\mathbb Q}\setminus\{0,1\}$ の元である。その Legendre の $j$ 値を

$$
J(x)=\frac{256(x^2-x+1)^3}{x^2(x-1)^2}

$$
とする。ある $a\in A$ に対して $\overline{\mathbb Q}$ の中で $J(x)=a$ が成り立つような三脚上の点 $x$ 全体の集合は有限である。$A$ が空ならば、この点集合も空である。 [Lean の宣言](../../../../Solutions/Source_TripodCoreFiniteness.lean#L40) · [Legendre の $j$ 値](../../../../Definitions/Def_TripodCanonicalHighHeightInputs.lean#L23)

### `finite_curve_j_preimage`

任意の曲線供給データ $P$ を取る。$P$ は曲線の構成に必要な $3$-ねじれ点と $5$-ねじれ点の有限性、得られた各曲線 $E_x$ の数体 $F_x$ 上での算術データ、および各素数 $\ell$ に対する法 $\ell$ の表現データを与える。ここで $E_x$ と $F_x$ は、同じ三脚上の点 $x$ に対して $P.\mathrm{curve}(x)$ が与える曲線と数体である。任意の有限集合 $A\subset\mathbb Q$ に対して、$j(E_x)$ が $F_x$ の中である $a\in A$ の像に等しいような三脚上の点 $x$ 全体の集合は有限である。$A$ が空ならば、この点集合も空である。 [Lean の宣言](../../../../Solutions/Source_TripodCoreFiniteness.lean#L50) · [曲線供給データ](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviders.lean#L28)

### `coreFiniteness_of_exceptionalJ`

上記の曲線供給データ $P$、宇宙レベル零の遠アーベル幾何 $AG$、有限集合 $A\subset\mathbb Q$、自然数の次数上界 $d$、およびコンパクト有界データ $K$ を固定する。$K$ は $2$ を含む有限素数集合 $V$ と実数の上界 $b$ からなる。その台集合 $C_K$ は、$\mathbb Q(x)$ のすべての無限素点と、剰余標数が $V$ に属するすべての有限素点 $v$ において $\left|\log |x|_v\right|$ と $\left|\log |x-1|_v\right|$ がともに $b$ 以下となる三脚上の点 $x$ の集合である。 [コンパクト有界集合](../../../../Definitions/Def_AbcTripod.lean#L169)

三脚上の点 $x$ に対して、$X_x$ を $AG$ における $E_x$ の原点を除いた曲線、$Q_x$ をその符号商とする。宇宙レベル零の任意の標数零の体 $L$ と任意の埋め込み $f:F_x\to L$ に対して、$f$ に沿う $Q_x$ の基底変換が $AG$ のコア関係のもとで $X_x$ の基底変換のコアであるとき、$x$ は普遍的なコア条件を満たすという。この条件を満たさない**すべての**三脚上の点 $x$ について、$j(E_x)$ が $F_x$ の中である $a\in A$ の像に等しいと仮定する。このとき、$C_K$ に属し $[\mathbb Q(x):\mathbb Q]\le d$ を満たす点のうち、普遍的なコア条件を満たさないものの集合は有限である。次数上界とコンパクト有界条件は結論の対象を制限する。$d=0$ ならば次数条件を満たす点はない。$A$ が空ならば、包含の仮定によりすべての三脚上の点が普遍的なコア条件を満たす。 [Lean の宣言](../../../../Solutions/Source_TripodCoreFiniteness.lean#L62) · [普遍的なコア条件](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean#L32) · [有限性の命題](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts.lean#L50)

## 来源与审查

本地证明沿用参考 `Iut/Tripod/Core.lean` 的有限根论证。清除分母所得的多项式

$$
256(T^2-T+1)^3-aT^2(T-1)^2

$$
在 $T=0$ 取值 $256$。曲线 $j$ 值通过 $F_x$ 到 $\overline{\mathbb Q}$ 的嵌入转为同一三足点的 Legendre 值。几何例外值归约把曲线核失败的包含关系交给这里的有限性定理。 [参考 Core.lean](../../../../../refer/iut/Iut/Tripod/Core.lean#L31) · [实际曲线 $j$ 值](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_JTransport.lean#L34) · [直接消费者](../../../../Solutions/Source_TripodCoreGeometry.lean#L74)

叶检查 `ci-020853-fe047d77` 和项目审查 `ci-020859-ae4a0f86` 成功。该项目审查导入 Checks、ImportAudit、Act1Scene1 和 AxiomAudit。三条声明的公理均为 `propext`、`Classical.choice` 和 `Quot.sound`。 [叶检查](../receipts/tripod-core-ci-020853-fe047d77-result.json) · [审查输入](../ReviewTripodCoreFiniteness.lean#L1) · [项目及公理审查](../receipts/tripod-core-ci-020859-ae4a0f86-result.json)
