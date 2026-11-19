# Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean

Upstream revision `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`. Adapted source SHA-256 `f31a6c599d1745189debacad67d0d541087f6555f68c0330285081e63731b2f0`. MCP-CI leaf check `ci-022799-28b9cc35` passed with exit code 0 and no diagnostics. [Source](../../../../Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean#L7) · [Leaf check receipt](../receipts/round-ci-022799-28b9cc35-result.json)

## English

Fix a curve provider $P$ and a tripod point $x$ with parameter $\lambda$. Write $E/F$ for the supplied Legendre curve. Let $K$ be a `CompactlyBounded` datum with $x\in K.\mathrm{set}$ and $c=K.c$. This membership bounds both $\big|\log|\lambda|_v\big|$ and $\big|\log|\lambda-1|_v\big|$ by $c$ on $\mathbb Q(\lambda)$ at every infinite place and at the finite places whose residue characteristic belongs to the specified finite set of primes containing $2$. [Compact bounds](../../../../Definitions/Def_AbcTripod.lean#L169)

Let $\ell$ be an odd prime and $H$ an additive subgroup of $E(\overline F)$ of order $\ell$. Assume that every $F$-automorphism of $\overline F$ sends the points of $H$ into $H$. The hypothesis `IsGraphLineOdd` requires that, at each finite place of the $\ell$-torsion field $L/F$ above a place in `VBadOdd`, the pullback $H_L\subseteq E(L)$ of $H$ is the Tate graph line supplied there. The set `VBadOdd` consists of finite places of the field of moduli with odd residue characteristic that have a place of $F$ above them and for which all such places of $F$ have multiplicative reduction. [Places in VBadOdd](../../../../Solutions/Source_TripodCyclicBoundOdd.lean#L68) · [Graph-line condition](../../../../Solutions/Source_TripodCyclicBoundOdd.lean#L145)

Choose a real $C_0\ge1$ satisfying `LegendreTorsionXBound K.c C₀`. This means that for any complex Legendre elliptic curve with parameter $z$ satisfying $\big|\log|z|\big|\le c$ and $\big|\log|z-1|\big|\le c$, every nonsingular affine point $(a,b)$ killed by an integer $N\ge1$ satisfies $|a|\le C_0N^2$. Define $h(x)$ to be `P.h x` and $h_2(x)$ to be `(P.localData x).heightEq 2`, the part of this height supported over $2$. With this same $C_0$, the theorem `main_bound` gives

$$
\frac{\ell-1}{4}\bigl(h(x)-h_2(x)\bigr)
\le 10\log\ell+2\log(32C_0)+6c+4\log 4.
$$

[Torsion-coordinate bound](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound.lean#L23) · [Height at residue characteristic two](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection_HeightParts.lean#L25) · [Adapted theorem](../../../../Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean#L106) · [Reference theorem](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/CyclicIsogeny.lean#L831)

Galois stability gives $\rho\in F^\times$ whose image in $L$ is the product of the two designated Vélu ratios. Take $S$ to be the union of the finite-place supports of $\rho$, $4$, and $\ell$, and the multiplicative reduction locus `badAll` of $E$. The weighted infinite-place sum of $\log|\rho|_v$ plus the finite sum over $S$ is zero by the product formula. At an infinite place, the compact bounds transport along $\mathbb Q(\lambda)\hookrightarrow F$. Applying `log_infinite_bound` with the chosen $C_0$ gives an upper bound of $2\log(32C_0)+6\log\ell+c$ there. The infinite-place multiplicities sum to $d=[F:\mathbb Q]$, so the bound on that weighted sum is $d$ times this expression. [Vélu descent and product formula](../../../../Solutions/Source_TripodCyclicVeluDescent.lean#L112) · [Infinite-place transport](../../../../Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean#L24) · [Infinite-place sum](../../../../Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean#L140)

At every finite place $v$, `log_apply_le` bounds $\log|\rho|_v$ by $-4\log|\ell|_v$ plus one of three terms.

- At a place of multiplicative reduction and odd residue characteristic, the Tate graph line gives the term $-\frac{\ell-1}{4}\log|j(E)|_v$. The sum of the $j$-logarithms over these places is $d(h(x)-h_2(x))$. [Odd height identity](../../../../Solutions/Source_TripodCyclicBoundOdd.lean#L114)
- At a place of residue characteristic $2$, the term is $\frac92\big|\log|\lambda|_v\big|+\frac12\big|\log|\lambda-1|_v\big|-4\log|4|_v$. Transport from $\mathbb Q(\lambda)$ multiplies the absolute logarithms by the relative local degree. This degree is at most the absolute local degree, so each absolute logarithm is bounded by $c$ times the absolute local degree. The sum of these local degrees in $S$ over $2$ is at most $d$. The two parameter terms therefore contribute at most $5cd$. The sum of $-\log|4|_v$ over these places is bounded by its sum $d\log 4$ over $S$. [Transport at two](../../../../Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean#L38) · [Local degree sum](../../../../Solutions/Source_TripodFinitePrimeCounting.lean#L36) · [Sum at two](../../../../Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean#L159)
- At a place of odd residue characteristic outside `badAll`, the absolute values of $\lambda$, $\lambda-1$, and $4$ are all $1$. The remaining bound is $-4\log|\ell|_v$. [Finite-place estimate](../../../../Solutions/Source_TripodCyclicVeluLog.lean#L132) · [Unit factors](../../../../Solutions/Source_TripodCyclicVeluLog.lean#L169)

The field norm of a positive integer $n$ is $n^d$, so the sum of $-\log|n|_v$ over its finite support is $d\log n$. Apply this identity to $4$ and $\ell$. Combine the finite and infinite estimates in the product formula, move the odd multiplicative contribution to the left, and divide by $d>0$. The terms $6\log\ell$ and $4\log\ell$ give the coefficient $10$, and the terms $c$ and $5c$ give $6c$. [Norm identity](../../../../Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean#L63) · [Global sum](../../../../Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean#L186)

## 中文

固定曲线数据提供者 $P$ 和参数为 $\lambda$ 的 tripod 点 $x$，记给出的 Legendre 曲线为 $E/F$。取表示紧致有界子集的 `CompactlyBounded` 数据 $K$，设 $x\in K.\mathrm{set}$，并令 $c=K.c$。这一成员条件要求，在 $\mathbb Q(\lambda)$ 的所有无限位，以及剩余特征属于包含 $2$ 的指定素数有限集的有限位，$\big|\log|\lambda|_v\big|$ 与 $\big|\log|\lambda-1|_v\big|$ 都不超过 $c$。 [紧致有界条件](../../../../Definitions/Def_AbcTripod.lean#L169)

设 $\ell$ 为奇素数，$H$ 为 $E(\overline F)$ 中阶为 $\ell$ 的加法子群。假设 $\overline F$ 的每个 $F$-自同构都把 $H$ 中的点送到 $H$。假设 `IsGraphLineOdd` 要求在 $\ell$-挠点域 $L/F$ 中位于 `VBadOdd` 上方的每个有限位，$H$ 在 $E(L)$ 中的拉回 $H_L$ 等于该处给出的 Tate 图像直线。`VBadOdd` 由模域上满足以下条件的有限位组成。该位的剩余特征为奇数，在 $F$ 中至少有一个上方位，且曲线在所有这些上方位都有乘法约化。 [VBadOdd 中的位](../../../../Solutions/Source_TripodCyclicBoundOdd.lean#L68) · [图像直线条件](../../../../Solutions/Source_TripodCyclicBoundOdd.lean#L145)

取满足 `LegendreTorsionXBound K.c C₀` 的实数 $C_0\ge1$。即对参数 $z$ 满足 $\big|\log|z|\big|\le c$、$\big|\log|z-1|\big|\le c$ 的每条复 Legendre 椭圆曲线，被整数 $N\ge1$ 消去的任意非奇异仿射点 $(a,b)$ 都满足 $|a|\le C_0N^2$。记 $h(x)$ 为 `P.h x`，$h_2(x)$ 为 `(P.localData x).heightEq 2`，即该高度在剩余特征为 $2$ 的位上的部分。定理 `main_bound` 用同一个 $C_0$ 给出

$$
\frac{\ell-1}{4}\bigl(h(x)-h_2(x)\bigr)
\le 10\log\ell+2\log(32C_0)+6c+4\log 4.
$$

[挠点坐标界](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound.lean#L23) · [剩余特征为二的高度](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection_HeightParts.lean#L25) · [适配定理](../../../../Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean#L106) · [参考定理](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/CyclicIsogeny.lean#L831)

由 Galois 稳定性得到 $\rho\in F^\times$，其在 $L$ 中的像等于两个指定 Vélu 比值的乘积。取 $S$ 为 $\rho$、$4$、$\ell$ 的有限位支集与 $E$ 的乘法约化位集 `badAll` 的并集。由乘积公式，各无限位的 $\log|\rho|_v$ 加权和与 $S$ 上的有限位和相加为零。在无限位，紧致有界条件沿 $\mathbb Q(\lambda)\hookrightarrow F$ 传递。用选定的 $C_0$ 应用 `log_infinite_bound`，得到上界 $2\log(32C_0)+6\log\ell+c$。无限位的重数之和为 $d=[F:\mathbb Q]$，所以加权和的上界是该式乘以 $d$。 [Vélu 下降与乘积公式](../../../../Solutions/Source_TripodCyclicVeluDescent.lean#L112) · [无限位上的传递](../../../../Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean#L24) · [无限位求和](../../../../Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean#L140)

对每个有限位 $v$，`log_apply_le` 将 $\log|\rho|_v$ 控制在 $-4\log|\ell|_v$ 加上下列三种情形中对应的一项。

- 在奇剩余特征的乘法约化位，Tate 图像直线给出项 $-\frac{\ell-1}{4}\log|j(E)|_v$。这些位的 $j$ 不变量绝对值的对数之和为 $d(h(x)-h_2(x))$。 [奇剩余特征处的高度恒等式](../../../../Solutions/Source_TripodCyclicBoundOdd.lean#L114)
- 在剩余特征为 $2$ 的位，对应项是 $\frac92\big|\log|\lambda|_v\big|+\frac12\big|\log|\lambda-1|_v\big|-4\log|4|_v$。从 $\mathbb Q(\lambda)$ 传递时，两个对数的绝对值乘以相对局部次数。相对局部次数不超过绝对局部次数，所以两个绝对值都至多为 $c$ 乘以绝对局部次数。$S$ 中位于 $2$ 上方的局部次数之和至多为 $d$，故两个参数项合计至多为 $5cd$。这些位的 $-\log|4|_v$ 之和至多为它在 $S$ 上的总和 $d\log 4$。 [二处的传递](../../../../Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean#L38) · [局部次数求和](../../../../Solutions/Source_TripodFinitePrimeCounting.lean#L36) · [二处的求和](../../../../Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean#L159)
- 在 `badAll` 之外的奇剩余特征位，$\lambda$、$\lambda-1$ 及 $4$ 的绝对值均为 $1$，所以只剩界 $-4\log|\ell|_v$。 [有限位估计](../../../../Solutions/Source_TripodCyclicVeluLog.lean#L132) · [绝对值为一的因子](../../../../Solutions/Source_TripodCyclicVeluLog.lean#L169)

正整数 $n$ 的域范数是 $n^d$，所以 $-\log|n|_v$ 在其有限位支集上的和是 $d\log n$。将此式用于 $4$ 和 $\ell$。把有限位与无限位的界代入乘积公式，将奇剩余特征的乘法约化位的贡献移到左边，再除以 $d>0$。$6\log\ell$ 与 $4\log\ell$ 合成 $10\log\ell$，$c$ 与 $5c$ 合成 $6c$。 [范数恒等式](../../../../Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean#L63) · [全局求和](../../../../Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean#L186)

## 日本語

曲線データの供給元 $P$ とパラメータ $\lambda$ の tripod の点 $x$ を固定し、$P$ が与える Legendre 曲線を $E/F$ とする。コンパクト有界集合を表す `CompactlyBounded` のデータ $K$ を取り、$x\in K.\mathrm{set}$、$c=K.c$ とする。この所属条件は、$\mathbb Q(\lambda)$ の全無限素点と、剰余標数が $2$ を含む指定された有限個の素数のいずれかである有限素点で、$\big|\log|\lambda|_v\big|$ と $\big|\log|\lambda-1|_v\big|$ がともに $c$ 以下であることを要求する。 [コンパクト有界条件](../../../../Definitions/Def_AbcTripod.lean#L169)

$\ell$ を奇素数、$H$ を $E(\overline F)$ の位数 $\ell$ の加法部分群とする。$\overline F$ の各 $F$-自己同型が $H$ の点を $H$ に移すと仮定する。`IsGraphLineOdd` は、$\ell$ 等分点体 $L/F$ の `VBadOdd` 上の各有限素点で、$H$ の $E(L)$ への引き戻し $H_L$ がその素点の Tate グラフ直線に等しいことを要求する。`VBadOdd` の元はモジュライ体の奇剰余標数の有限素点である。各元の上には $F$ の素点が少なくとも一つあり、そのすべてで曲線は乗法的還元をもつ。 [VBadOdd の素点](../../../../Solutions/Source_TripodCyclicBoundOdd.lean#L68) · [グラフ直線の条件](../../../../Solutions/Source_TripodCyclicBoundOdd.lean#L145)

`LegendreTorsionXBound K.c C₀` を満たす実数 $C_0\ge1$ を取る。これは、パラメータ $z$ が $\big|\log|z|\big|\le c$ と $\big|\log|z-1|\big|\le c$ を満たす複素 Legendre 楕円曲線で、整数 $N\ge1$ 倍で消える任意の非特異なアフィン点 $(a,b)$ が $|a|\le C_0N^2$ を満たすという条件である。`P.h x` を $h(x)$、その高さの $2$ 上での寄与 `(P.localData x).heightEq 2` を $h_2(x)$ と書く。定理 `main_bound` では、この同じ $C_0$ を用いて次が成り立つ。

$$
\frac{\ell-1}{4}\bigl(h(x)-h_2(x)\bigr)
\le 10\log\ell+2\log(32C_0)+6c+4\log 4.
$$

[等分点の座標の上界](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound.lean#L23) · [剰余標数二での高さ](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection_HeightParts.lean#L25) · [適応版の定理](../../../../Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean#L106) · [参照元の定理](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/CyclicIsogeny.lean#L831)

Galois 安定性により、$L$ での像が指定された二つの Vélu 比の積に等しい $\rho\in F^\times$ が得られる。$S$ を $\rho$、$4$、$\ell$ の有限素点の台と、$E$ の乗法的還元の素点集合 `badAll` との和集合とする。積公式により、$\log|\rho|_v$ の無限素点での重み付き和と $S$ 上の有限素点での和を足すと零になる。無限素点では、コンパクト有界条件を $\mathbb Q(\lambda)\hookrightarrow F$ に沿って移す。選んだ $C_0$ で `log_infinite_bound` を適用し、上界 $2\log(32C_0)+6\log\ell+c$ を得る。無限素点の重みの和は $d=[F:\mathbb Q]$ なので、重み付き和の上界はこの式の $d$ 倍である。 [Vélu 比の降下と積公式](../../../../Solutions/Source_TripodCyclicVeluDescent.lean#L112) · [無限素点での移送](../../../../Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean#L24) · [無限素点の和](../../../../Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean#L140)

各有限素点 $v$ で、`log_apply_le` は $\log|\rho|_v$ を $-4\log|\ell|_v$ と次の三つの場合に応じた項との和で抑える。

- 奇剰余標数の乗法的還元の素点では、Tate グラフ直線から項 $-\frac{\ell-1}{4}\log|j(E)|_v$ が得られる。これらの素点における $j$ 不変量の絶対値の対数の和は $d(h(x)-h_2(x))$ である。 [奇剰余標数での高さの恒等式](../../../../Solutions/Source_TripodCyclicBoundOdd.lean#L114)
- 剰余標数が $2$ の素点では、項は $\frac92\big|\log|\lambda|_v\big|+\frac12\big|\log|\lambda-1|_v\big|-4\log|4|_v$ である。$\mathbb Q(\lambda)$ から移すと、二つの対数の絶対値に相対局所次数が掛かる。この次数は絶対局所次数以下なので、各絶対値は $c$ と絶対局所次数の積以下になる。$S$ に含まれる $2$ 上の素点の局所次数を足すと高々 $d$ なので、二つのパラメータの項の和は高々 $5cd$ になる。これらの素点での $-\log|4|_v$ の和は、$S$ 全体での和 $d\log 4$ 以下である。 [二の上での移送](../../../../Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean#L38) · [局所次数の和](../../../../Solutions/Source_TripodFinitePrimeCounting.lean#L36) · [二の上での和](../../../../Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean#L159)
- `badAll` の外にある奇剰余標数の素点では、$\lambda$、$\lambda-1$、$4$ の絶対値はすべて $1$ であり、評価式に残るのは $-4\log|\ell|_v$ だけである。 [有限素点での評価](../../../../Solutions/Source_TripodCyclicVeluLog.lean#L132) · [絶対値が一の因子](../../../../Solutions/Source_TripodCyclicVeluLog.lean#L169)

正整数 $n$ の体ノルムは $n^d$ なので、$-\log|n|_v$ の有限素点の台上での和は $d\log n$ になる。この式を $4$ と $\ell$ に適用する。有限素点と無限素点の上界を積公式に代入し、奇剰余標数の乗法的還元の寄与を左辺に移して $d>0$ で割る。$6\log\ell$ と $4\log\ell$ を足すと $10\log\ell$ になり、$c$ と $5c$ を足すと $6c$ になる。 [ノルムの恒等式](../../../../Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean#L63) · [全素点の和](../../../../Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean#L186)
