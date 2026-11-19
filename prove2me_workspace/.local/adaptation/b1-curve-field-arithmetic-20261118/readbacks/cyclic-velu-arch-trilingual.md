# Torsion translates and the archimedean Vélu bound

## English

### `translate_torsion`

Let $K$ be a number field and $W$ a Weierstrass curve over $K$. Let $H$ be a finite additive subgroup of `W.toAffine.Point` with odd cardinality $\ell$. Take $T\ne 0$ with $[2]T=0$ and take $R$ with $[2]R=T$. Here $0$ denotes the identity and $[n]$ denotes multiplication by $n$. For every $Q\in H$,

$$
T+Q\ne 0,\qquad R+Q\ne 0,\qquad [4\ell](T+Q)=[4\ell](R+Q)=0.
$$

An odd-order subgroup excludes the point $T$ of order two. Since $[2]R=T$, it also excludes $R$. If either translate were zero, the corresponding $T$ or $R$ would equal $-Q\in H$. Multiplication by $4$ kills $T$ and $R$, and multiplication by $\ell$ kills every $Q\in H$. This gives the $4\ell$-torsion relations. [Translation theorem](../../../../Solutions/Source_TripodCyclicVeluArch.lean#L31) · [Reference statement](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/CyclicIsogeny.lean#L312)

### `arch_bound`

Use the same $K,W,H,T,R$. Assume $W=\operatorname{legendre}(\lambda)$ for $\lambda\in K$ and `W.IsElliptic`. Assume $\ell$ is prime and $\ell\ne2$, so the subgroup order is odd. Let $c,C_0\in\mathbb R$ satisfy `LegendreTorsionXBound c C₀`. This hypothesis bounds $\|a\|$ by $C_0N^2$ at every nonsingular affine point $(a,b)$ killed by $N\ge1$ on a complex elliptic Legendre curve. It applies when the absolute logarithms of the complex norms of the parameter and of the parameter minus one are at most $c$. Take any infinite place $v$ of $K$ with

$$
\bigl|\log v(\lambda)\bigr|\le c,\qquad
\bigl|\log v(\lambda-1)\bigr|\le c.
$$

[Archimedean hypotheses](../../../../Solutions/Source_TripodCyclicVeluArch.lean#L56) · [Complex torsion bound](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound.lean#L23)

Write $x(S)$ for `xCoordinate S` and $r$ for `veluRatio H T R`. The ratio is a product over the nonzero subgroup elements. The Vélu identity expresses the product of $r$ and the coordinate difference as a sum over the whole subgroup.

$$
r=\prod_{Q\in H\setminus\{0\}}\frac{x(T)-x(R+Q)}{x(T)-x(Q)},\qquad
r\bigl(x(T)-x(R)\bigr)=\sum_{Q\in H}\bigl(x(T+Q)-x(R+Q)\bigr).
$$

[Vélu ratio](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicVeluRatio.lean:93) · [Vélu identity](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutVeluTracePolynomial.lean:256)

With $\varphi=v.\mathrm{embedding}\colon K\hookrightarrow\mathbb C$, one has $v(a)=\|\varphi(a)\|$. The mapped curve is $\operatorname{legendre}(\varphi(\lambda))$. The point map preserves multiplication by $4\ell$ and carries each nonzero translate to a nonsingular affine point. Apply the complex bound with $N=4\ell$ to each point. Each summand has norm at most $2C_0(4\ell)^2$ by the triangle inequality. There are $\ell$ summands, so

$$
v(r)\,v\bigl(x(T)-x(R)\bigr)\le 2\ell\,C_0(4\ell)^2.
$$

[Embedding norm](/home/admin-wsl/Coq/mathlib4-0df444a/Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean:112) · [Termwise estimate and sum](../../../../Solutions/Source_TripodCyclicVeluArch.lean#L67) · [Reference archimedean bound](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/CyclicIsogeny.lean#L379)

Review `ci-022033-6796478f` passed and lists `propext`, `Classical.choice`, and `Quot.sound` for both declarations. [Review source](../../../../.local/adaptation/b1-curve-field-arithmetic-20261118/ReviewTripodCyclicVeluArch.lean#L9) · [Receipt](../../../../.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-022033-6796478f-result.json)

## 中文

### `translate_torsion`

设 $K$ 为数域，$W$ 为 $K$ 上的 Weierstrass 曲线。设 $H$ 是 `W.toAffine.Point` 的有限加法子群，阶为奇数 $\ell$。取 $T\ne 0$ 满足 $[2]T=0$，再取 $R$ 满足 $[2]R=T$。这里 $0$ 表示单位元，$[n]$ 表示乘以 $n$。对任意 $Q\in H$，有

$$
T+Q\ne 0,\qquad R+Q\ne 0,\qquad [4\ell](T+Q)=[4\ell](R+Q)=0.
$$

奇数阶子群 $H$ 不含阶为二的 $T$。由 $[2]R=T$，$R$ 也在 $H$ 之外。若任一平移后的点为零，则对应的 $T$ 或 $R$ 属于 $H$。乘以 $4$ 消去 $T$ 和 $R$，乘以 $\ell$ 消去 $H$ 中的任意 $Q$，从而得到两个平移点的 $4\ell$ 挠性。 [平移引理](../../../../Solutions/Source_TripodCyclicVeluArch.lean#L31) · [参考陈述](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/CyclicIsogeny.lean#L312)

### `arch_bound`

沿用 $K,W,H,T,R$。设 $\lambda\in K$，$W=\operatorname{legendre}(\lambda)$，并有 `W.IsElliptic`。设 $\ell$ 为素数且 $\ell\ne2$，于是子群阶为奇数。设实数 $c,C_0$ 满足 `LegendreTorsionXBound c C₀`。该假设对复椭圆 Legendre 曲线上的每个非奇异仿射点 $(a,b)$ 给出 $\|a\|\le C_0N^2$，其中该点被 $N\ge1$ 消去。其适用条件是参数及参数减一的复数范数取对数后的绝对值均不超过 $c$。取 $K$ 的任意无穷位 $v$，并假设

$$
\bigl|\log v(\lambda)\bigr|\le c,\qquad
\bigl|\log v(\lambda-1)\bigr|\le c.
$$

[阿基米德定理假设](../../../../Solutions/Source_TripodCyclicVeluArch.lean#L56) · [复数域挠点界](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound.lean#L23)

用 $x(S)$ 表示 `xCoordinate S`，用 $r$ 表示 `veluRatio H T R`。Vélu 比是对子群非零元素的乘积。Vélu 恒等式将 $r$ 与坐标差的乘积写成对整个子群的和。

$$
r=\prod_{Q\in H\setminus\{0\}}\frac{x(T)-x(R+Q)}{x(T)-x(Q)},\qquad
r\bigl(x(T)-x(R)\bigr)=\sum_{Q\in H}\bigl(x(T+Q)-x(R+Q)\bigr).
$$

[Vélu 比](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicVeluRatio.lean:93) · [Vélu 恒等式](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutVeluTracePolynomial.lean:256)

记 $\varphi=v.\mathrm{embedding}\colon K\hookrightarrow\mathbb C$，则 $v(a)=\|\varphi(a)\|$。映射后的曲线为 $\operatorname{legendre}(\varphi(\lambda))$。点映射保持乘以 $4\ell$ 的关系，并将两个非零平移点映为非奇异仿射点。用 $N=4\ell$ 分别应用复数域挠点界。由三角不等式，每个差项的范数至多为 $2C_0(4\ell)^2$。对 $\ell$ 个差项求和得到

$$
v(r)\,v\bigl(x(T)-x(R)\bigr)\le 2\ell\,C_0(4\ell)^2.
$$

[嵌入与范数](/home/admin-wsl/Coq/mathlib4-0df444a/Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean:112) · [逐项估计与求和](../../../../Solutions/Source_TripodCyclicVeluArch.lean#L67) · [参考阿基米德界](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/CyclicIsogeny.lean#L379)

审查 `ci-022033-6796478f` 已通过，两条声明的公理依赖均为 `propext`、`Classical.choice` 和 `Quot.sound`。 [审查源文件](../../../../.local/adaptation/b1-curve-field-arithmetic-20261118/ReviewTripodCyclicVeluArch.lean#L9) · [回执](../../../../.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-022033-6796478f-result.json)

## 日本語

### `translate_torsion`

$K$ を数体、$W$ を $K$ 上の Weierstrass 曲線とする。$H$ を `W.toAffine.Point` の有限加法部分群とし、その位数を奇数 $\ell$ とする。$[2]T=0$ を満たす $T\ne 0$ と、$[2]R=T$ を満たす $R$ を取る。ここで $0$ は単位元を表し、$[n]$ は $n$ 倍写像を表す。任意の $Q\in H$ について、次が成り立つ。

$$
T+Q\ne 0,\qquad R+Q\ne 0,\qquad [4\ell](T+Q)=[4\ell](R+Q)=0.
$$

奇数位数の部分群 $H$ は位数二の点 $T$ を含まない。$[2]R=T$ により $R$ も $H$ の外にある。平行移動した点が零ならば、対応する $T$ または $R$ が $H$ に属することになる。$T$ と $R$ の $4$ 倍、および各 $Q\in H$ の $\ell$ 倍が零であることから、両方の平行移動点が $4\ell$ 倍で零になる。 [平行移動の定理](../../../../Solutions/Source_TripodCyclicVeluArch.lean#L31) · [参照元の定理](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/CyclicIsogeny.lean#L312)

### `arch_bound`

同じ $K,W,H,T,R$ を用いる。$\lambda\in K$ に対して $W=\operatorname{legendre}(\lambda)$ とし、`W.IsElliptic` を仮定する。$\ell$ を $2$ と異なる素数とする。このとき部分群の位数は奇数である。実数 $c,C_0$ は `LegendreTorsionXBound c C₀` を満たすとする。この仮定は、複素 Legendre 楕円曲線上で $N\ge1$ 倍が零となる各非特異アフィン点 $(a,b)$ について、$\|a\|\le C_0N^2$ を与える。パラメータとパラメータから一を引いた値の複素ノルムについて、対数の絶対値はいずれも $c$ 以下とする。次を満たす $K$ の任意の無限素点 $v$ を取る。

$$
\bigl|\log v(\lambda)\bigr|\le c,\qquad
\bigl|\log v(\lambda-1)\bigr|\le c.
$$

[無限素点での評価の仮定](../../../../Solutions/Source_TripodCyclicVeluArch.lean#L56) · [複素数上の捩れ点の評価](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound.lean#L23)

`xCoordinate S` を $x(S)$、`veluRatio H T R` を $r$ と書く。Vélu 比は部分群の非零元にわたる積である。Vélu の恒等式は、$r$ と座標差の積を部分群全体にわたる和として与える。

$$
r=\prod_{Q\in H\setminus\{0\}}\frac{x(T)-x(R+Q)}{x(T)-x(Q)},\qquad
r\bigl(x(T)-x(R)\bigr)=\sum_{Q\in H}\bigl(x(T+Q)-x(R+Q)\bigr).
$$

[Vélu 比](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicVeluRatio.lean:93) · [Vélu の恒等式](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutVeluTracePolynomial.lean:256)

$\varphi=v.\mathrm{embedding}\colon K\hookrightarrow\mathbb C$ とおくと、$v(a)=\|\varphi(a)\|$ である。係数を写した曲線は $\operatorname{legendre}(\varphi(\lambda))$ になる。点の写像は $4\ell$ 倍と可換であり、非零の平行移動点を非特異アフィン点に移す。二つの点のそれぞれに $N=4\ell$ で複素数上の評価を適用する。三角不等式により、差の各項のノルムは $2C_0(4\ell)^2$ 以下である。$\ell$ 項について和を取ると、次を得る。

$$
v(r)\,v\bigl(x(T)-x(R)\bigr)\le 2\ell\,C_0(4\ell)^2.
$$

[埋め込みとノルム](/home/admin-wsl/Coq/mathlib4-0df444a/Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean:112) · [各項の評価と和](../../../../Solutions/Source_TripodCyclicVeluArch.lean#L67) · [参照元の無限素点での評価](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/CyclicIsogeny.lean#L379)

レビュー `ci-022033-6796478f` は成功し、両方の宣言について公理依存として `propext`、`Classical.choice`、`Quot.sound` を報告する。 [レビューのソース](../../../../.local/adaptation/b1-curve-field-arithmetic-20261118/ReviewTripodCyclicVeluArch.lean#L9) · [レビュー結果](../../../../.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-022033-6796478f-result.json)
