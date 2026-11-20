# Finite Θ components, hulls, and packet log-volume

## English

### Data and notation

Let `AG` be an anabelian geometry interface and `TG` a tempered geometry interface over `AG`. Fix initial Θ-data $D$ over these interfaces. It gives a number field $F$, an elliptic curve $E/F$, an admissible prime $\ell\ge 5$, and the $\ell$-torsion field $K=D.\mathrm{Kt}$. Let $B_F$ be the set of finite places of $F$ above the selected set $D.\mathrm{VBad}$ of places of the field of moduli. Write $w\mid p$ for a place with residue characteristic $p$.

All three statements take `TL : ThetaLocalData D (concreteLocalTheory (K := D.Kt))`. The local theory is fixed to the concrete one on $K$. For a rational prime $p$, write $V_p$ for the finite places of $K$ over $p$. At $v\in V_p$, put $d_v=[K_v:\mathbb Q_p]$ and $\lambda_v=d_v/[K:\mathbb Q]$. The valuation $\operatorname{ord}_{p,v}$ satisfies $\operatorname{ord}_{p,v}(p)=1$. For nonzero $x\in K_v$, it is $-\log\lVert x\rVert/(d_v\log p)$ in the completion norm of the code.

The input `TL` supplies a finite set $B$ of prime residue characteristics and, at every finite place $v$ of $K$, a nonzero element $q_v\in K_v$ of nonnegative normalized valuation. It gives $q_v=1$ when the residue characteristic of $v$ is outside $B$. For each $v\mid w$ with $w$ a finite place of $F$, it supplies a ring map $F_w\to K_v$. When $w\in B_F$, the input identifies $q_v^{2\ell}$ with the image of the Tate parameter $q_w$ under this map. It also gives
$$
\operatorname{ord}_{p,v}(q_v)=\frac{\nu_w(q_w)}{2\ell e_w}
$$
for such pairs of residue characteristic $p$. Here $e_w$ is the ramification index of $w$ over $p$, and $\nu_w(q_w)$ is the integer Tate parameter order with a uniformizer of order one. The residue characteristics of places in $B_F$ and of places of $K$ above them belong to $B$. The input also gives the following base-change identity for every rational prime $p$ and any finite enumeration of $B_F$.
$$
\sum_{v\in V_p}\lambda_v\operatorname{ord}_{p,v}(q_v)
=\frac{1}{2\ell}\sum_{\substack{w\in B_F\\ w\mid p}}\frac{f_w}{[F:\mathbb Q]}\nu_w(q_w).
$$
Here $f_w$ is the residue degree of $w$ over $p$.

### `thetaComponent_finite_eq_scaled`

Take any natural number $n$, index $0\le i<n$, and rational prime $p$. In the standard procession of length $n$, the $i$-th capsule has labels $L_j=\{0,\ldots,j\}$ with $j=i+1$. Its distinguished label is $j$. For every tuple $c:L_j\to V_p$, let $T_c$ be the concrete tensor product of the completions $K_{c(k)}$ over $\mathbb Q_p$, and let $O_c$ be the integral closure of $\mathbb Z_p$ in $T_c$. Let $a_c$ be the image of $q_{c(j)}^{\,j^2}$ in $T_c$ under the inclusion of the $j$-th factor. This is a unit of $T_c$.

The finite Θ component is the union of the images of $a_c O_c$ under the specified automorphisms induced by the automorphisms of the individual completions over $\mathbb Q_p$. The theorem states that this union equals the principal region $a_c O_c$. The allowed index set is empty for $n=0$.

### `thetaHull_region_finite`

Use $n=(\ell-1)/2$, the length of the standard procession in the right-hand-side data $R=\texttt{TL.rhsData}$. For every $0\le i<n$ and every rational prime $p$, use the labels $L_j$ and the regions $a_c O_c$ above. The packet is the product of the rings $T_c$ over all tuples $c:L_j\to V_p$. Its Θ region is the product of the finite Θ components. The holomorphic hull is the least containing region among products of the form $\prod_c b_cO_c$ with every $b_c$ a unit of $T_c$. The theorem states that the region of this hull at $p$ is
$$
\prod_{c:L_j\to V_p} a_cO_c .
$$
In particular, a point $x=(x_c)_c$ belongs to the hull at $p$ exactly when $x_c\in a_cO_c$ for every tuple $c$.

### `packetVol_finite_thetaHull`

In addition to the local Θ data, take `QI : QPilotInputs D`. It supplies a proof that $B_F$ is finite and that every finite place of $F$ has positive residue degree. Let $X$ be the concrete variant data formed from $D$, `TL`, and `QI`. Its $q$-pilot contribution at $p$ is
$$
X.\operatorname{logQAt}(p)
=\log p\sum_{\substack{w\in B_F\\w\mid p}}\frac{f_w}{[F:\mathbb Q]}\nu_w(q_w).
$$
An empty sum is zero. For every $0\le i<(\ell-1)/2$ and every rational prime $p$, let $H_{i,p}$ be the just-described region of the holomorphic hull. The real-valued packet log-volume in $R$ satisfies
$$
R.\operatorname{packetVol}(i,p,H_{i,p})
=-j^2\,\frac{X.\operatorname{logQAt}(p)}{2\ell},\qquad j=i+1.
$$
The left side denotes `R.vol.packetVol i (.finite p) ((R.thetaHull i).region (.finite p))`. The packet uses a weighted sum of the component log-volumes with tuple weight $\prod_{k\in L_j}\lambda_{c(k)}$. Each component takes the log of the additive Haar measure relative to $O_c$, then divides by $\dim_{\mathbb Q_p}T_c$. Scaling by $q_{c(j)}^{\,j^2}$ in one factor therefore gives the component log-volume $-j^2\operatorname{ord}_{p,c(j)}(q_{c(j)})\log p$. The place weights sum to one, so averaging over the other labels leaves the weighted sum over $c(j)$. The base-change identity for `TL` gives the divisor $2\ell$ in the result.

## 简体中文

### 数据和记号

设 `AG` 为远 Abel 几何接口，`TG` 为其上的缓和几何接口。固定这些接口上的初始 Θ 数据 $D$。它给出数域 $F$、椭圆曲线 $E/F$、可容许素数 $\ell\ge5$ 和 $\ell$-扭点域 $K=D.\mathrm{Kt}$。记 $B_F$ 为 $F$ 中位于模域所选处集 $D.\mathrm{VBad}$ 上方的有限处集。记 $w\mid p$ 表示 $w$ 的剩余特征为 $p$。

三个声明都接收 `TL : ThetaLocalData D (concreteLocalTheory (K := D.Kt))`，其中局部理论固定为 $K$ 上的具体局部理论。对每个有理素数 $p$，记 $V_p$ 为 $K$ 在 $p$ 上方的有限处集。对 $v\in V_p$，令 $d_v=[K_v:\mathbb Q_p]$、$\lambda_v=d_v/[K:\mathbb Q]$。赋值 $\operatorname{ord}_{p,v}$ 归一化为 $\operatorname{ord}_{p,v}(p)=1$。若 $x\in K_v$ 非零，则该赋值按代码中的完备化范数写为 $-\log\lVert x\rVert/(d_v\log p)$。

输入 `TL` 给出由素数组成的有限剩余特征集 $B$，并对 $K$ 的每个有限处 $v$ 给出非零元 $q_v\in K_v$，其归一化赋值非负。若 $v$ 的剩余特征不属于 $B$，则 $q_v=1$。对于 $F$ 的每个有限处 $w$ 及其上方的 $v$，输入还给出环同态 $F_w\to K_v$。若 $w\in B_F$，则 $q_v^{2\ell}$ 等于 Tate 参数 $q_w$ 在该同态下的像。对于这样的上覆关系，在剩余特征为 $p$ 时还有
$$
\operatorname{ord}_{p,v}(q_v)=\frac{\nu_w(q_w)}{2\ell e_w}.
$$
这里 $e_w$ 是 $w$ 在 $p$ 上方的分歧指数，$\nu_w(q_w)$ 是取素元的阶为一时 Tate 参数的整数阶。$B_F$ 中各处和 $K$ 中位于其上方的各处的剩余特征均属于 $B$。对于每个有理素数 $p$ 及 $B_F$ 的任意有限枚举，输入还给出如下基域变换等式。
$$
\sum_{v\in V_p}\lambda_v\operatorname{ord}_{p,v}(q_v)
=\frac{1}{2\ell}\sum_{\substack{w\in B_F\\ w\mid p}}\frac{f_w}{[F:\mathbb Q]}\nu_w(q_w).
$$
其中 $f_w$ 是 $w$ 在 $p$ 上方的剩余次数。

### `thetaComponent_finite_eq_scaled`

任取自然数 $n$、指标 $0\le i<n$ 和有理素数 $p$。在长度为 $n$ 的标准标签集递增族中，第 $i$ 个标签集为 $L_j=\{0,\ldots,j\}$，其中 $j=i+1$，指定标签为 $j$。对任意处元组 $c:L_j\to V_p$，记 $T_c$ 为各完备化 $K_{c(k)}$ 在 $\mathbb Q_p$ 上的具体张量积，$O_c$ 为 $\mathbb Z_p$ 在 $T_c$ 中的整闭包。记 $a_c$ 为 $q_{c(j)}^{\,j^2}$ 在第 $j$ 个张量因子的嵌入下的像。$a_c$ 是 $T_c$ 的可逆元。

有限处的 Θ 分量是由各个完备化在 $\mathbb Q_p$ 上的自同构所诱导的指定自同构作用于 $a_cO_c$ 后，所得诸像的并集。该声明断言此并集等于缩放后的整闭包 $a_cO_c$。$n=0$ 时，指标集为空。

### `thetaHull_region_finite`

取 $n=(\ell-1)/2$。这是右端数据 $R=\texttt{TL.rhsData}$ 中标准标签集递增族的长度。对每个 $0\le i<n$ 和每个有理素数 $p$，沿用上述标签集 $L_j$ 与区域 $a_cO_c$。整包是由全部处元组 $c:L_j\to V_p$ 索引的各环 $T_c$ 的乘积。其 Θ 区域是各有限处 Θ 分量的乘积。全纯包络在形如 $\prod_c b_cO_c$ 且各 $b_c$ 均为 $T_c$ 中可逆元的区域中，取包含 Θ 区域的最小者。该声明断言此包络在 $p$ 处的区域等于
$$
\prod_{c:L_j\to V_p} a_cO_c .
$$
换言之，$x=(x_c)_c$ 属于 $p$ 处的全纯包络，当且仅当对每个处元组 $c$ 都有 $x_c\in a_cO_c$。

### `packetVol_finite_thetaHull`

在同一局部 Θ 数据之外，给定 `QI : QPilotInputs D`。它给出 $B_F$ 有限以及 $F$ 的每个有限处的剩余次数为正。令 $X$ 为由 $D$、`TL` 和 `QI` 组成的具体变体数据。其 $p$ 处的 $q$ 对数贡献为
$$
X.\operatorname{logQAt}(p)
=\log p\sum_{\substack{w\in B_F\\w\mid p}}\frac{f_w}{[F:\mathbb Q]}\nu_w(q_w).
$$
空和取零。对每个 $0\le i<(\ell-1)/2$ 和每个有理素数 $p$，记上述全纯包络在 $p$ 处的区域为 $H_{i,p}$。$R$ 给出的实数值整包对数体积满足
$$
R.\operatorname{packetVol}(i,p,H_{i,p})
=-j^2\,\frac{X.\operatorname{logQAt}(p)}{2\ell},\qquad j=i+1.
$$
左端对应 `R.vol.packetVol i (.finite p) ((R.thetaHull i).region (.finite p))`。整包按处元组权重 $\prod_{k\in L_j}\lambda_{c(k)}$ 对分量对数体积求和。每个分量先对以 $O_c$ 的加法 Haar 测度为基准的测度比取对数，再除以 $\dim_{\mathbb Q_p}T_c$。在一个张量因子上按 $q_{c(j)}^{\,j^2}$ 缩放，得到分量对数体积 $-j^2\operatorname{ord}_{p,c(j)}(q_{c(j)})\log p$。处权重之和为一，所以对其余标签作加权求和后，剩下对指定标签所取处 $c(j)$ 的加权和。等式右端的分母 $2\ell$ 来自 `TL` 的基域变换等式。

## 日本語

### データと記号

`AG` を遠アーベル幾何学のインターフェース、`TG` をその上の緩和幾何のインターフェースとする。これらに関する初期 Θ データ $D$ を固定する。$D$ は数体 $F$、楕円曲線 $E/F$、許容素数 $\ell\ge5$、および $\ell$-捩れ点体 $K=D.\mathrm{Kt}$ を与える。$B_F$ を、モジュライ体の選ばれた素点集合 $D.\mathrm{VBad}$ の上にある $F$ の有限素点の集合とする。$w\mid p$ は $w$ の剰余標数が $p$ であることを表す。

三つの宣言はいずれも `TL : ThetaLocalData D (concreteLocalTheory (K := D.Kt))` を受け取る。局所理論は $K$ 上の具体的な局所理論に固定される。有理素数 $p$ に対し、$V_p$ を $p$ の上にある $K$ の有限素点の集合とする。$v\in V_p$ に対し、$d_v=[K_v:\mathbb Q_p]$、$\lambda_v=d_v/[K:\mathbb Q]$ とおく。付値 $\operatorname{ord}_{p,v}$ は $\operatorname{ord}_{p,v}(p)=1$ を満たす。非零元 $x\in K_v$ に対し、この付値はコードの完備化のノルムで $-\log\lVert x\rVert/(d_v\log p)$ と書ける。

入力 `TL` は素数からなる有限な剰余標数の集合 $B$ と、$K$ の各有限素点 $v$ における非零元 $q_v\in K_v$ を与える。$q_v$ の正規化付値は非負であり、$v$ の剰余標数が $B$ の外にあるときは $q_v=1$ である。$F$ の任意の有限素点 $w$ とその上にある $v$ に対し、環準同型 $F_w\to K_v$ を与える。$w\in B_F$ ならば、$q_v^{2\ell}$ はこの準同型による Tate パラメータ $q_w$ の像に等しい。この関係にある素点の剰余標数を $p$ とすると、
$$
\operatorname{ord}_{p,v}(q_v)=\frac{\nu_w(q_w)}{2\ell e_w}
$$
が成り立つ。$e_w$ は $p$ 上の $w$ の分岐指数であり、$\nu_w(q_w)$ は素元の付値を一としたときの Tate パラメータの整数値の付値である。$B_F$ の各素点とその上にある $K$ の各素点の剰余標数は $B$ に属する。また、任意の有理素数 $p$ と $B_F$ の任意の有限な列挙に対し、入力は次の基底変換の等式を与える。
$$
\sum_{v\in V_p}\lambda_v\operatorname{ord}_{p,v}(q_v)
=\frac{1}{2\ell}\sum_{\substack{w\in B_F\\ w\mid p}}\frac{f_w}{[F:\mathbb Q]}\nu_w(q_w).
$$
ここで $f_w$ は $p$ 上の $w$ の剰余次数である。

### `thetaComponent_finite_eq_scaled`

自然数 $n$、添字 $0\le i<n$、有理素数 $p$ を任意にとる。長さ $n$ の標準プロセッションの第 $i$ カプセルのラベル集合を $L_j=\{0,\ldots,j\}$ とする。ここで $j=i+1$ であり、指定ラベルは $j$ である。各素点の組 $c:L_j\to V_p$ に対し、$T_c$ を完備化 $K_{c(k)}$ の $\mathbb Q_p$ 上の具体的なテンソル積、$O_c$ を $T_c$ における $\mathbb Z_p$ の整閉包とする。$a_c$ を第 $j$ 因子の埋め込みによる $q_{c(j)}^{\,j^2}$ の像とする。$a_c$ は $T_c$ の単元である。

有限素点での Θ 成分は、各完備化の $\mathbb Q_p$ 上の自己同型から誘導される所定の自己同型による $a_cO_c$ の像すべての和集合である。この宣言は、その和集合が拡大縮小した整閉包 $a_cO_c$ に等しいことを述べる。$n=0$ のとき、添字の集合は空である。

### `thetaHull_region_finite`

$n=(\ell-1)/2$ とする。これは右辺データ $R=\texttt{TL.rhsData}$ における標準プロセッションの長さである。$0\le i<n$ を満たす任意の添字 $i$ と任意の有理素数 $p$ に対し、上で定めたラベル集合 $L_j$ と領域 $a_cO_c$ を用いる。パケットは、すべての素点の組 $c:L_j\to V_p$ で添字付けられた環 $T_c$ の直積である。その Θ 領域は、有限素点での Θ 成分の直積である。正則包は、各 $b_c$ が $T_c$ の単元である形 $\prod_c b_cO_c$ の領域のうち、Θ 領域を含む最小の領域である。この宣言は、$p$ における正則包の領域が
$$
\prod_{c:L_j\to V_p} a_cO_c
$$
に等しいことを述べる。すなわち、$x=(x_c)_c$ が $p$ における正則包に属することと、すべての組 $c$ について $x_c\in a_cO_c$ であることは同値である。

### `packetVol_finite_thetaHull`

同じ局所 Θ データに加え、`QI : QPilotInputs D` を与える。これは $B_F$ が有限であることと、$F$ のすべての有限素点で剰余次数が正であることを与える。$D$、`TL`、`QI` からなる具体的な変種のデータを $X$ とする。その $q$ の対数に対する $p$ での寄与は
$$
X.\operatorname{logQAt}(p)
=\log p\sum_{\substack{w\in B_F\\w\mid p}}\frac{f_w}{[F:\mathbb Q]}\nu_w(q_w)
$$
である。空和は零とする。$0\le i<(\ell-1)/2$ を満たす任意の添字 $i$ と任意の有理素数 $p$ に対し、上で述べた $p$ における正則包の領域を $H_{i,p}$ とする。$R$ が与える実数値のパケット対数体積は
$$
R.\operatorname{packetVol}(i,p,H_{i,p})
=-j^2\,\frac{X.\operatorname{logQAt}(p)}{2\ell},\qquad j=i+1
$$
を満たす。左辺は `R.vol.packetVol i (.finite p) ((R.thetaHull i).region (.finite p))` に対応する。パケット対数体積は、組の重み $\prod_{k\in L_j}\lambda_{c(k)}$ を用いた各成分の対数体積の総和である。成分ごとに、$O_c$ の加法的 Haar 測度に対する測度の比の対数をとり、$\dim_{\mathbb Q_p}T_c$ で割る。一つのテンソル因子における $q_{c(j)}^{\,j^2}$ による拡大縮小で、成分の対数体積は $-j^2\operatorname{ord}_{p,c(j)}(q_{c(j)})\log p$ となる。素点の重みの和は一なので、他のラベルについて重み付き総和をとると、指定ラベルが取る素点 $c(j)$ についての重み付き総和が残る。右辺の分母 $2\ell$ は `TL` の基底変換の等式に由来する。

[Finite component equality](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCor312FiniteThetaHullVolume.lean:59) · [Finite hull equality](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCor312FiniteThetaHullVolume.lean:99) · [Finite log-volume formula](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCor312FiniteThetaHullVolume.lean:153) · [Local Θ inputs](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteThetaRegion.lean:49) · [Concrete q-pilot inputs](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutQPilot.lean:28) · [Concrete normalized component volume](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteLocalHaar.lean:80) · [Terminology](/home/admin-wsl/Coq/abc/docs/三语术语名词关键对照.md)

[Lean 声明](../../../../Solutions/Source_ReferenceIutCor312FiniteThetaHullVolume.lean) · [项目及公理审查](../receipts/round-ci-023844-960063ad-result.json)
