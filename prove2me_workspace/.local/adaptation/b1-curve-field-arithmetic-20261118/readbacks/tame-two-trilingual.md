# Tame ramification of the torsion field in residue characteristic 2

## English

Let $E/F$ be the Legendre curve `P.curve x`. Its tripodal field is $F_{\mathrm{tpd}}=\mathbb Q(\lambda)$. Let $\ell$ be an odd prime and $K$ the torsion field of any `R : (P.curve x).ModEllRepData ℓ`. Let $v$ be a finite place of $K$ of residue characteristic 2. Write $w$ and $u$ for the places of $F$ and $F_{\mathrm{tpd}}$ below $v$. Write $I_v$ for the inertia group of $K/F$ at $v$. The ramification index equals the order of $I_v$. The theorem `not_two_dvd_relRamIdx_torsionField` proves that this index is odd.

$$
e(v/w)=|I_v|,\qquad 2\nmid e(v/w).
$$

The proof uses stable reduction at $w$ from `(P.arith x).stable_reduction w`. Here stable reduction means good or multiplicative reduction. [Tripodal field](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FieldTransport.lean#L22) · [Stable reduction](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_GlobalField.lean#L156) · [Provider arithmetic](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveArithmetic.lean#L50) · [Tameness at 2](../../../../Solutions/Source_TripodTameTwo.lean#L167) · [Reference proof](../../../../../refer/iut/Iut/Tripod/TameTwo.lean#L206)

### Integrality of odd torsion

Use a multiplicative valuation $\nu$, so $\nu(z)\le1$ means integral. Take an odd natural number $n$ with $\nu(n)=1$. The reduction-kernel lemma uses the division polynomial `preΨ' n` for $n$. Its coefficients are integral on an integral model and its leading coefficient is $n$. At $\nu(X)>1$, the leading term strictly dominates all lower terms. Thus the polynomial does not vanish at $X$. This excludes an $n$-torsion point with that first coordinate on a model with $a_1=a_3=0$ and the same division polynomial. [Leading-term valuation](../../../../Solutions/Source_ReferenceIutTowerReductionKernel.lean#L29) · [Division polynomial criterion](../../../../Solutions/Source_ReferenceIutTowerReductionKernel.lean#L78)

For a general integral Weierstrass model, `IntegralTorsion` completes the square over the field, where $2\ne0$. This change keeps $X$ and the invariants $b_2,b_4,b_6,b_8$, hence it keeps `preΨ' n`. The argument uses the integral polynomial of the original model. The monic equation in $Y$ then gives

$$
[n]A=O,\quad A=(X,Y)\quad\Longrightarrow\quad \nu(X)\le1\ \land\ \nu(Y)\le1.
$$

Here $A$ is a nonsingular affine point and $O$ is the group identity. [Polynomial under completion of the square](../../../../Solutions/Source_ReferenceIutTowerIntegralTorsion.lean#L57) · [Exclusion of nonintegral $X$](../../../../Solutions/Source_ReferenceIutTowerIntegralTorsion.lean#L69) · [Integral coordinates](../../../../Solutions/Source_ReferenceIutTowerIntegralTorsion.lean#L107)

### An inertia automorphism with square one

Stable reduction gives a change of variables over $F$ to a $w$-integral model with unit $\Delta$ in the good case or unit $c_4$ in the multiplicative case. The model stays integral at $v$, and a coefficient or invariant that is a unit at $w$ stays a unit at $v$. Write $\nu=\nu_v$. Residue characteristic 2 gives $\nu(2)<1$ and $\nu(\ell)=1$. In the multiplicative case, $c_4=b_2^2-24b_4$ and $b_2=a_1^2+4a_2$ give $\nu(a_1)=1$. Inertia fixes the coefficients of the changed model and the change of variables, since they come from $F$. [Stable integral model](../../../../Solutions/Source_TripodTameTwo.lean#L49) · [Integral base change](../../../../Solutions/Source_TripodTameTwo.lean#L70) · [Unit $a_1$](../../../../Solutions/Source_ReferenceIutTowerInertiaInvolution.lean#L98) · [Transport of the point action](../../../../Solutions/Source_TripodTameTwo.lean#L82)

Let $\sigma\in I_v$ with $\sigma^2=1$, and write $\phi$ for its action on the changed model. It acts on coordinates and satisfies $\nu(\sigma z-z)<1$ for every integral $z$. Suppose a nonzero $n$-torsion point $A=(X,Y)$ satisfies $\phi A=-A$, with $n$ odd and $\nu(n)=1$. Its coordinates are integral and $[2]A\ne O$. Write the tangent slope as $s=N/D$ with

$$
N=3X^2+2a_2X+a_4-a_1Y,\qquad D=2Y+a_1X+a_3=Y-\sigma Y\ne0.
$$

In the good case $\nu(D)<1$, and nonsingular reduction gives $\nu(N)=1$. In the multiplicative case $\sigma s-s=-(2s+a_1)$. If $s$ were integral, the right side would have valuation 1, contrary to the inertia congruence. Thus $\nu(s)>1$ in both cases. The term $s^2$ dominates the other terms of $X([2]A)=s^2+a_1s-a_2-2X$. This gives $\nu(X([2]A))>1$, contrary to the integrality of the $n$-torsion point $[2]A$. [Inertia congruence](../../../../Solutions/Source_ReferenceIutTowerInertia.lean#L29) · [Nonsingular reduction](../../../../Solutions/Source_ReferenceIutTowerInertiaInvolution.lean#L38) · [Tangent calculation](../../../../Solutions/Source_ReferenceIutTowerInertiaInvolution.lean#L150)

For any $n$-torsion point $Q$, the difference $A=\phi Q-Q$ is killed by $n$ and satisfies $\phi A=-A$ because $\phi^2=1$. Hence $A=O$ and $\phi Q=Q$. Transport through the change of variables gives this identity on $E(K)[\ell]$ with $n=\ell$. Faithfulness on this torsion gives $\sigma=1$. An even $|I_v|$ would give an element of order two by Cauchy's theorem, contradicting that identity. [Inertia involution](../../../../Solutions/Source_ReferenceIutTowerInertiaInvolution.lean#L241) · [Faithfulness](../../../../Solutions/Source_ReferenceIutTorsionFaithful.lean#L45) · [Inertia and index](../../../../Solutions/Source_ReferenceIutTowerInertia.lean#L71) · [Order-two exclusion](../../../../Solutions/Source_TripodTameTwo.lean#L150)

### Consequence for the tripodal tower

Multiplicativity of ramification indices gives the following residue characteristic 2 consequence. Here $\operatorname{ord}_2$ is the exponent of 2 in a positive integer.

$$
\operatorname{ord}_2(e(v/w))=0,\qquad
\operatorname{ord}_2(e(v/u))=\operatorname{ord}_2(e(w/u)).
$$

The extension $F/F_{\mathrm{tpd}}$ is Galois. Hence $e(w/u)\mid[F:F_{\mathrm{tpd}}]\mid184320=2^{12}\cdot3^2\cdot5$, which gives $\operatorname{ord}_2(e(v/u))\le12$. The theorem `padicValNat_relRamIdx_le` in `Source_TripodWildRamIdx.lean` gives the wild bound for every finite $v$ when $\ell\ge7$. It combines this result with tameness at $p\notin\{2,\ell\}$ and the degree divisibilities. To assemble `TowerLocalFacts`, the proof also needs the unramified case and the $30\ell$ bound. [Index multiplicativity](../../../../Solutions/Source_ReferenceIutTowerTorsionRigid.lean#L159) · [Galois extension](../../../../Solutions/Source_TripodUnramifiedBase.lean#L274) · [Index divides degree](../../../../Solutions/Source_ReferenceIutTowerInertia.lean#L100) · [Tripodal degree](../../../../Solutions/Source_TripodTpdDegree.lean#L22) · [Tameness away from 2 and $\ell$](../../../../Solutions/Source_TripodWildRamIdx.lean#L23) · [Wild bound](../../../../Solutions/Source_TripodWildRamIdx.lean#L48) · [Unramified case](../../../../Solutions/Source_TripodUnramified.lean#L50) · [$30\ell$ bound](../../../../Solutions/Source_TripodTpdInertia.lean#L339) · [Local facts](../../../../Solutions/Source_ReferenceIutTowerLocalFacts.lean#L124) · [Reference assembly](../../../../../refer/iut/Iut/Tripod/TowerFacts.lean#L99)

MCP-CI leaf checks passed for the three supporting modules, `Source_TripodTameTwo.lean`, and `Source_TripodWildRamIdx.lean`. [Reduction kernel](../receipts/round-ci-022346-6bc9f5b8-result.json) · [Integral torsion](../receipts/round-ci-022366-82933329-result.json) · [Inertia involution](../receipts/round-ci-022380-71bbc1ff-result.json) · [Tameness at 2](../receipts/round-ci-022406-aa16afa6-result.json) · [Wild bound](../receipts/round-ci-022410-f598c120-result.json)

## 中文

设 $E/F$ 为 `P.curve x`，其三足域为 $F_{\mathrm{tpd}}=\mathbb Q(\lambda)$。取奇素数 $\ell$ 和任意 `R : (P.curve x).ModEllRepData ℓ`，记其挠点域为 $K$。设 $v$ 为 $K$ 上剩余特征为 2 的有限位，$w,u$ 分别为其下方在 $F,F_{\mathrm{tpd}}$ 上的位。记 $I_v$ 为 $K/F$ 在 $v$ 处的惯性群。分歧指数等于 $I_v$ 的阶。定理 `not_two_dvd_relRamIdx_torsionField` 证明该指数为奇数。

$$
e(v/w)=|I_v|,\qquad 2\nmid e(v/w).
$$

证明取 `(P.arith x).stable_reduction w` 给出的稳定约化，即好约化或乘法约化。 [三足域](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FieldTransport.lean#L22) · [稳定约化](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_GlobalField.lean#L156) · [曲线算术数据](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveArithmetic.lean#L50) · [剩余特征 2 的温和分歧](../../../../Solutions/Source_TripodTameTwo.lean#L167) · [参考证明](../../../../../refer/iut/Iut/Tripod/TameTwo.lean#L206)

### 奇数阶挠点的整性

用乘法赋值 $\nu$，$\nu(z)\le1$ 表示 $z$ 为整元素。对满足 $\nu(n)=1$ 的奇自然数 $n$，约化核引理使用 $n$ 对应的除法多项式 `preΨ' n`。在整模型上，它的系数为整元素，首项系数为 $n$。当 $\nu(X)>1$ 时，首项的赋值严格大于其余各项。因此多项式在 $X$ 处不为零。在满足 $a_1=a_3=0$ 且保有同一除法多项式的模型上，这就排除了横坐标为 $X$ 的 $n$ 挠点。 [首项赋值](../../../../Solutions/Source_ReferenceIutTowerReductionKernel.lean#L29) · [除法多项式判据](../../../../Solutions/Source_ReferenceIutTowerReductionKernel.lean#L78)

对一般的 Weierstrass 整模型，`IntegralTorsion` 在 $2\ne0$ 的域上作配方变换。变换保留横坐标 $X$ 和不变量 $b_2,b_4,b_6,b_8$，故也保留 `preΨ' n`。证明使用原模型的整系数多项式，再由关于 $Y$ 的首一方程得到

$$
[n]A=O,\quad A=(X,Y)\quad\Longrightarrow\quad \nu(X)\le1\ \land\ \nu(Y)\le1.
$$

这里 $A$ 为非奇异仿射点，$O$ 为点群零元。 [配方后的多项式](../../../../Solutions/Source_ReferenceIutTowerIntegralTorsion.lean#L57) · [排除非整横坐标](../../../../Solutions/Source_ReferenceIutTowerIntegralTorsion.lean#L69) · [坐标整性](../../../../Solutions/Source_ReferenceIutTowerIntegralTorsion.lean#L107)

### 平方为恒等的惯性自同构

由稳定约化可在 $F$ 上作变量代换，使模型在 $w$ 处为整。好约化时 $\Delta$ 为单位，乘法约化时 $c_4$ 为单位。整性和单位条件经基变换传到 $v$。对 $\nu=\nu_v$，剩余特征为 2 给出 $\nu(2)<1$ 与 $\nu(\ell)=1$。乘法约化时，由 $c_4=b_2^2-24b_4$ 和 $b_2=a_1^2+4a_2$ 得 $\nu(a_1)=1$。代换参数及变换后的模型系数均来自 $F$，故由惯性固定。 [稳定整模型](../../../../Solutions/Source_TripodTameTwo.lean#L49) · [整性的基变换](../../../../Solutions/Source_TripodTameTwo.lean#L70) · [单位 $a_1$](../../../../Solutions/Source_ReferenceIutTowerInertiaInvolution.lean#L98) · [点作用的传递](../../../../Solutions/Source_TripodTameTwo.lean#L82)

设 $\sigma\in I_v$ 且 $\sigma^2=1$，记其在变换后模型上的点作用为 $\phi$。它按坐标作用，且对每个整元素 $z$ 有 $\nu(\sigma z-z)<1$。假设非零 $n$ 挠点 $A=(X,Y)$ 满足 $\phi A=-A$，其中 $n$ 为奇数且 $\nu(n)=1$。其坐标为整，且 $[2]A\ne O$。记切线斜率为 $s=N/D$，其中

$$
N=3X^2+2a_2X+a_4-a_1Y,\qquad D=2Y+a_1X+a_3=Y-\sigma Y\ne0.
$$

好约化时 $\nu(D)<1$，而非奇异约化给出 $\nu(N)=1$。乘法约化时 $\sigma s-s=-(2s+a_1)$。若 $s$ 为整元素，右边的赋值为 1，与惯性同余矛盾。因此两种情形均有 $\nu(s)>1$。在 $X([2]A)=s^2+a_1s-a_2-2X$ 中，$s^2$ 的赋值严格大于其余各项，故 $\nu(X([2]A))>1$。这与 $n$ 挠点 $[2]A$ 的整性矛盾。 [惯性同余](../../../../Solutions/Source_ReferenceIutTowerInertia.lean#L29) · [非奇异约化](../../../../Solutions/Source_ReferenceIutTowerInertiaInvolution.lean#L38) · [切线计算](../../../../Solutions/Source_ReferenceIutTowerInertiaInvolution.lean#L150)

对任意 $n$ 挠点 $Q$，取 $A=\phi Q-Q$。由 $\phi^2=1$，它仍被 $n$ 消去且满足 $\phi A=-A$。故 $A=O$，即 $\phi Q=Q$。经变量代换传回原曲线，并取 $n=\ell$，得到 $\sigma$ 固定 $E(K)[\ell]$。该作用忠实，故 $\sigma=1$。若 $|I_v|$ 为偶数，Cauchy 定理给出二阶元素，与此矛盾。 [惯性对合](../../../../Solutions/Source_ReferenceIutTowerInertiaInvolution.lean#L241) · [挠点作用的忠实性](../../../../Solutions/Source_ReferenceIutTorsionFaithful.lean#L45) · [惯性群与分歧指数](../../../../Solutions/Source_ReferenceIutTowerInertia.lean#L71) · [排除二阶元素](../../../../Solutions/Source_TripodTameTwo.lean#L150)

### 三足塔中的推论

分歧指数的乘法性给出以下剩余特征为 2 时的等式。$\operatorname{ord}_2$ 表示正整数中 2 的指数。

$$
\operatorname{ord}_2(e(v/w))=0,\qquad
\operatorname{ord}_2(e(v/u))=\operatorname{ord}_2(e(w/u)).
$$

由于 $F/F_{\mathrm{tpd}}$ 为 Galois 扩张，$e(w/u)\mid[F:F_{\mathrm{tpd}}]\mid184320=2^{12}\cdot3^2\cdot5$，故 $\operatorname{ord}_2(e(v/u))\le12$。当 $\ell\ge7$ 时，`Source_TripodWildRamIdx.lean` 中的 `padicValNat_relRamIdx_le` 对每个有限位 $v$ 给出野分歧界。证明还用到 $p\notin\{2,\ell\}$ 时的温和分歧及扩张次数的整除性。组装 `TowerLocalFacts` 时还使用好位上的不分歧定理和 $30\ell$ 界。 [分歧指数的乘法性](../../../../Solutions/Source_ReferenceIutTowerTorsionRigid.lean#L159) · [Galois 扩张](../../../../Solutions/Source_TripodUnramifiedBase.lean#L274) · [分歧指数整除扩张次数](../../../../Solutions/Source_ReferenceIutTowerInertia.lean#L100) · [三足域上的扩张次数](../../../../Solutions/Source_TripodTpdDegree.lean#L22) · [其余温和分歧情形](../../../../Solutions/Source_TripodWildRamIdx.lean#L23) · [野分歧界](../../../../Solutions/Source_TripodWildRamIdx.lean#L48) · [不分歧情形](../../../../Solutions/Source_TripodUnramified.lean#L50) · [$30\ell$ 界](../../../../Solutions/Source_TripodTpdInertia.lean#L339) · [塔的局部事实](../../../../Solutions/Source_ReferenceIutTowerLocalFacts.lean#L124) · [参考组合定理](../../../../../refer/iut/Iut/Tripod/TowerFacts.lean#L99)

三个依赖模块及 `Source_TripodTameTwo.lean`、`Source_TripodWildRamIdx.lean` 的 MCP-CI 叶检查均已通过。 [约化核](../receipts/round-ci-022346-6bc9f5b8-result.json) · [挠点整性](../receipts/round-ci-022366-82933329-result.json) · [惯性对合](../receipts/round-ci-022380-71bbc1ff-result.json) · [剩余特征 2 的温和分歧](../receipts/round-ci-022406-aa16afa6-result.json) · [野分歧界](../receipts/round-ci-022410-f598c120-result.json)

## 日本語

`P.curve x` を $E/F$ とし、三脚体を $F_{\mathrm{tpd}}=\mathbb Q(\lambda)$ とする。奇素数 $\ell$ と任意の `R : (P.curve x).ModEllRepData ℓ` を取り、そのねじれ点体を $K$ とする。$v$ を剰余標数が 2 である $K$ の有限素点とする。$w,u$ をその下にある $F,F_{\mathrm{tpd}}$ の素点とする。$I_v$ を $K/F$ の $v$ における惰性群とする。分岐指数は $I_v$ の位数に等しい。`not_two_dvd_relRamIdx_torsionField` はこの指数が奇数であることを示す。

$$
e(v/w)=|I_v|,\qquad 2\nmid e(v/w).
$$

証明では `(P.arith x).stable_reduction w` が与える半安定還元を用いる。半安定還元とは良い還元または乗法的還元である。 [三脚体](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FieldTransport.lean#L22) · [半安定還元](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_GlobalField.lean#L156) · [曲線の算術データ](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveArithmetic.lean#L50) · [剰余標数 2 での順分岐](../../../../Solutions/Source_TripodTameTwo.lean#L167) · [参照元の証明](../../../../../refer/iut/Iut/Tripod/TameTwo.lean#L206)

### 奇数位数のねじれ点の整性

乗法的付値を $\nu$ とする。$\nu(z)\le1$ は $z$ が整であることを表す。$\nu(n)=1$ を満たす奇数の自然数 $n$ に対し、還元の核に関する補題は $n$ に対応する分点多項式 `preΨ' n` を使う。整モデルでは多項式の係数は整であり、最高次の係数は $n$ である。$\nu(X)>1$ ならば、最高次の項の付値は他のすべての項の付値より大きい。このため多項式は $X$ で零にならない。従って、$a_1=a_3=0$ で同じ分点多項式を持つモデルでは、この第一座標を持つ $n$-ねじれ点は存在しない。 [最高次の項の付値](../../../../Solutions/Source_ReferenceIutTowerReductionKernel.lean#L29) · [分点多項式による判定](../../../../Solutions/Source_ReferenceIutTowerReductionKernel.lean#L78)

一般の Weierstrass 整モデルに対し、`IntegralTorsion` は $2\ne0$ の体上で平方完成を行う。この変換は第一座標の $X$ と不変量 $b_2,b_4,b_6,b_8$ を保つので、`preΨ' n` も保つ。元のモデルの整係数多項式を使い、$Y$ に関するモニックな方程式から次を得る。

$$
[n]A=O,\quad A=(X,Y)\quad\Longrightarrow\quad \nu(X)\le1\ \land\ \nu(Y)\le1.
$$

ここで $A$ は非特異アフィン点、$O$ は加法群の零元である。 [平方完成と多項式](../../../../Solutions/Source_ReferenceIutTowerIntegralTorsion.lean#L57) · [整でない第一座標の排除](../../../../Solutions/Source_ReferenceIutTowerIntegralTorsion.lean#L69) · [座標の整性](../../../../Solutions/Source_ReferenceIutTowerIntegralTorsion.lean#L107)

### 二乗が恒等となる惰性自己同型

半安定還元から、$F$ 上の変数変換で $w$ における整モデルを得る。良い還元の場合は $\Delta$ が単元であり、乗法的還元の場合は $c_4$ が単元である。この整性と単元の条件は基底変換で $v$ に移る。$\nu=\nu_v$ とすると、剰余標数が 2 なので $\nu(2)<1$ と $\nu(\ell)=1$ が成り立つ。乗法的還元の場合、$c_4=b_2^2-24b_4$ と $b_2=a_1^2+4a_2$ から $\nu(a_1)=1$ を得る。変数変換の係数と変換後のモデルの係数は $F$ に属するので、惰性群が固定する。 [半安定な整モデル](../../../../Solutions/Source_TripodTameTwo.lean#L49) · [整性の基底変換](../../../../Solutions/Source_TripodTameTwo.lean#L70) · [単元 $a_1$](../../../../Solutions/Source_ReferenceIutTowerInertiaInvolution.lean#L98) · [点への作用の移行](../../../../Solutions/Source_TripodTameTwo.lean#L82)

$\sigma\in I_v$ が $\sigma^2=1$ を満たすとし、変換後のモデルでの作用を $\phi$ とする。この作用は座標ごとに作用し、整元 $z$ について $\nu(\sigma z-z)<1$ が成り立つ。$n$ を奇数とし、$\nu(n)=1$ とする。非零の $n$-ねじれ点 $A=(X,Y)$ が $\phi A=-A$ を満たすと仮定する。その座標は整であり、$[2]A\ne O$ である。接線の傾きを $s=N/D$ と書く。

$$
N=3X^2+2a_2X+a_4-a_1Y,\qquad D=2Y+a_1X+a_3=Y-\sigma Y\ne0.
$$

良い還元の場合、$\nu(D)<1$ であり、還元が非特異であることから $\nu(N)=1$ となる。乗法的還元の場合、$\sigma s-s=-(2s+a_1)$ である。$s$ が整ならば右辺の付値は 1 となり、惰性の合同条件に矛盾する。従ってどちらの場合も $\nu(s)>1$ である。$X([2]A)=s^2+a_1s-a_2-2X$ では $s^2$ の付値が他の項の付値より大きい。従って $\nu(X([2]A))>1$ となり、$n$-ねじれ点 $[2]A$ の整性に矛盾する。 [惰性の合同条件](../../../../Solutions/Source_ReferenceIutTowerInertia.lean#L29) · [非特異な還元](../../../../Solutions/Source_ReferenceIutTowerInertiaInvolution.lean#L38) · [接線の計算](../../../../Solutions/Source_ReferenceIutTowerInertiaInvolution.lean#L150)

任意の $n$-ねじれ点 $Q$ に対し $A=\phi Q-Q$ とおく。$[n]A=O$ であり、$\phi^2=1$ により $\phi A=-A$ を満たす。従って $A=O$ となり、$\phi Q=Q$ である。変数変換で元のモデルに戻し、$n=\ell$ とすると、$\sigma$ は $E(K)[\ell]$ を各点ごとに固定する。ねじれ点への作用は忠実なので $\sigma=1$ である。$|I_v|$ が偶数ならば Cauchy の定理により位数 2 の元が存在し、これに矛盾する。 [惰性作用の対合](../../../../Solutions/Source_ReferenceIutTowerInertiaInvolution.lean#L241) · [ねじれ点への作用の忠実性](../../../../Solutions/Source_ReferenceIutTorsionFaithful.lean#L45) · [惰性群と分岐指数](../../../../Solutions/Source_ReferenceIutTowerInertia.lean#L71) · [位数 2 の元の排除](../../../../Solutions/Source_TripodTameTwo.lean#L150)

### 三脚体を含む拡大の塔での帰結

分岐指数の乗法性から、剰余標数が 2 の場合に次の等式を得る。$\operatorname{ord}_2$ は正整数における 2 の指数を表す。

$$
\operatorname{ord}_2(e(v/w))=0,\qquad
\operatorname{ord}_2(e(v/u))=\operatorname{ord}_2(e(w/u)).
$$

$F/F_{\mathrm{tpd}}$ は Galois 拡大である。従って $e(w/u)\mid[F:F_{\mathrm{tpd}}]\mid184320=2^{12}\cdot3^2\cdot5$ から $\operatorname{ord}_2(e(v/u))\le12$ となる。$\ell\ge7$ のとき、`Source_TripodWildRamIdx.lean` の `padicValNat_relRamIdx_le` はすべての有限素点 $v$ について野生分岐の上界を与える。証明は $p\notin\{2,\ell\}$ での順分岐と拡大次数の整除性も用いる。`TowerLocalFacts` の組み立てには、さらに良い素点での不分岐性と $30\ell$ の上界を用いる。 [分岐指数の乗法性](../../../../Solutions/Source_ReferenceIutTowerTorsionRigid.lean#L159) · [Galois 拡大](../../../../Solutions/Source_TripodUnramifiedBase.lean#L274) · [拡大次数の整除性](../../../../Solutions/Source_ReferenceIutTowerInertia.lean#L100) · [三脚体上の拡大次数](../../../../Solutions/Source_TripodTpdDegree.lean#L22) · [2 と $\ell$ 以外での順分岐](../../../../Solutions/Source_TripodWildRamIdx.lean#L23) · [野生分岐の上界](../../../../Solutions/Source_TripodWildRamIdx.lean#L48) · [不分岐の場合](../../../../Solutions/Source_TripodUnramified.lean#L50) · [$30\ell$ の上界](../../../../Solutions/Source_TripodTpdInertia.lean#L339) · [塔の局所条件](../../../../Solutions/Source_ReferenceIutTowerLocalFacts.lean#L124) · [参照元の組み立て](../../../../../refer/iut/Iut/Tripod/TowerFacts.lean#L99)

依存する三つのモジュールと `Source_TripodTameTwo.lean`、`Source_TripodWildRamIdx.lean` は MCP-CI の葉モジュール検査に合格した。 [還元の核](../receipts/round-ci-022346-6bc9f5b8-result.json) · [ねじれ点の整性](../receipts/round-ci-022366-82933329-result.json) · [惰性作用の対合](../receipts/round-ci-022380-71bbc1ff-result.json) · [剰余標数 2 での順分岐](../receipts/round-ci-022406-aa16afa6-result.json) · [野生分岐の上界](../receipts/round-ci-022410-f598c120-result.json)
