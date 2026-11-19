# Source_TripodCyclicVeluLog.lean

Upstream revision `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`. Adapted source SHA-256 `068295f7408735b2dc4dc1a569ad65473fc01f151abaa842c0f780961ef1db2b`. MCP-CI leaf check `ci-022671-ef6c0fda` passed with exit code 0 and two tactic linter warnings. [Source](../../../../Solutions/Source_TripodCyclicVeluLog.lean#L6) · [Receipt](../receipts/round-ci-022671-ef6c0fda-result.json)

## English

Fix a tripod point $x$ and curve provider $P$. Write $E/F$ for the curve supplied by $P$, $\lambda=\operatorname{genC}'(P,x)$ for its Legendre parameter, and $j=j(E)$. Let $\ell$ be an odd prime and $H\subset E(\overline F)$ an additive subgroup of order $\ell$. Write $L/F$ for the $\ell$-torsion field and $H_L$ for the pullback of $H$ to $E(L)$. Both estimates take a `Fintype` instance on $H_L$ and assume that $\rho\in F^\times$ maps to the product of the two designated Vélu ratios $\operatorname{veluRatio}(H_L,T_i,R_i)$ in $L$. [Inputs](../../../../Solutions/Source_TripodCyclicVeluLog.lean#L93)

### Finite places

The theorem `log_apply_le` also takes `IsGraphLineOdd`. At each finite place $w$ of $L$ over a `VBadOdd` place of the moduli field, this condition says that $H_L$ equals the pullback of the Tate graph line at $w$. For a finite place $v$ of $F$ with residue characteristic $p_v$, the normalized absolute value $|\cdot|_v$ satisfies

$$
\log|\rho|_v\le 4(-\log|\ell|_v)+
\begin{cases}
-\dfrac{\ell-1}{4}\log|j|_v
    & v\in\operatorname{badAll},\quad p_v\ne 2,\\
\dfrac92\big|\log|\lambda|_v\big|+\dfrac12\big|\log|\lambda-1|_v\big|+4(-\log|4|_v)
    & p_v=2,\\
0   & v\notin\operatorname{badAll},\quad p_v\ne 2.
\end{cases}
$$

[Graph-line condition](../../../../Solutions/Source_TripodCyclicBoundOdd.lean#L145) · [Adapted estimate](../../../../Solutions/Source_TripodCyclicVeluLog.lean#L132) · [Reference estimate](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/CyclicIsogeny.lean#L662)

At an odd multiplicative place, `finite_tate` gives $|\rho|_v^4|j|_v^{\ell-1}\le 1$. Take logarithms and use $|\ell|_v\le1$ to see that $4(-\log|\ell|_v)$ is nonnegative. At the remaining places, take logarithms in `finite_crude`. The chosen square roots of $\lambda$ and $1-\lambda$ contribute $\tfrac12\log|\lambda|_v$ and $\tfrac12\log|\lambda-1|_v$ to the left-hand side. At $p_v=2$, use $\log\max(1,|\lambda|_v)\le\big|\log|\lambda|_v\big|$ to obtain the coefficient $4+\tfrac12=\tfrac92$. At a place outside `badAll` with $p_v\ne2$, stable reduction rules out multiplicative reduction and gives $\operatorname{val}_v(j)\le1$ in the multiplicative valuation. The Legendre valuation calculation forces $|\lambda|_v=|\lambda-1|_v=1$. Also $|4|_v=1$, so only $4(-\log|\ell|_v)$ remains. [Logarithm of the crude bound](../../../../Solutions/Source_TripodCyclicVeluLog.lean#L101) · [Unit factors](../../../../Solutions/Source_TripodCyclicVeluLog.lean#L59) · [Reference valuation calculation](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/TwoAdic.lean#L258)

### Infinite places

For an infinite place $v$, the theorem `log_infinite_bound` takes $1\le C_0$ and `LegendreTorsionXBound c C₀`. This hypothesis bounds the absolute value of the $x$-coordinate of an affine point killed by a positive integer $N$ by $C_0N^2$ on complex Legendre curves with both parameter logarithms bounded in absolute value by $c$. The theorem assumes these two bounds at $v$ on $\log|\lambda|_v$ and $\log|\lambda-1|_v$. Take logarithms in `infinite_bound` and use $2\ell C_0(4\ell)^2=(32C_0)\ell^3$. Each subtracted half-logarithm of a parameter contributes at most $c/2$. The result is

$$
\log|\rho|_v\le 2\log(32C_0)+6\log\ell+c.
$$

[Hypothesis](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound.lean#L23) · [Adapted estimate](../../../../Solutions/Source_TripodCyclicVeluLog.lean#L180) · [Archimedean estimate in the reference](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/CyclicIsogeny.lean#L889)

## 中文

固定 tripod 点 $x$ 和曲线数据提供者 $P$。记 $E/F$ 为 $P$ 给出的曲线，$\lambda=\operatorname{genC}'(P,x)$ 为其 Legendre 参数，$j=j(E)$。设 $\ell$ 为奇素数，$H\subset E(\overline F)$ 为阶为 $\ell$ 的加法子群。记 $L/F$ 为 $\ell$-挠点域，$H_L$ 为 $H$ 在 $E(L)$ 中的拉回。两个估计都需要 $H_L$ 上的 `Fintype` 实例，并假设 $\rho\in F^\times$ 在 $L$ 中的像等于两个指定 Vélu 比值 $\operatorname{veluRatio}(H_L,T_i,R_i)$ 的乘积。 [输入](../../../../Solutions/Source_TripodCyclicVeluLog.lean#L93)

### 有限位

定理 `log_apply_le` 还需要 `IsGraphLineOdd`。这要求对模域中 `VBadOdd` 位上方的每个 $L$ 的有限位 $w$，$H_L$ 都等于 $w$ 处 Tate 图像直线的拉回。对 $F$ 的有限位 $v$，设 $p_v$ 为剩余特征，$|\cdot|_v$ 为归一化绝对值，则

$$
\log|\rho|_v\le 4(-\log|\ell|_v)+
\begin{cases}
-\dfrac{\ell-1}{4}\log|j|_v
    & v\in\operatorname{badAll},\quad p_v\ne 2,\\
\dfrac92\big|\log|\lambda|_v\big|+\dfrac12\big|\log|\lambda-1|_v\big|+4(-\log|4|_v)
    & p_v=2,\\
0   & v\notin\operatorname{badAll},\quad p_v\ne 2.
\end{cases}
$$

[图像直线条件](../../../../Solutions/Source_TripodCyclicBoundOdd.lean#L145) · [适配估计](../../../../Solutions/Source_TripodCyclicVeluLog.lean#L132) · [参考估计](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/CyclicIsogeny.lean#L662)

在奇剩余特征的乘法约化位，`finite_tate` 给出 $|\rho|_v^4|j|_v^{\ell-1}\le 1$。取对数，再用 $|\ell|_v\le1$ 得到 $4(-\log|\ell|_v)$ 非负。其余有限位对 `finite_crude` 取对数。选定的 $\lambda$ 和 $1-\lambda$ 的平方根在左边分别贡献 $\tfrac12\log|\lambda|_v$ 与 $\tfrac12\log|\lambda-1|_v$。当 $p_v=2$ 时，用 $\log\max(1,|\lambda|_v)\le\big|\log|\lambda|_v\big|$ 得到系数 $4+\tfrac12=\tfrac92$。若 $v$ 不在 `badAll` 中且 $p_v\ne2$，由稳定约化及此处无乘法约化可知乘法赋值满足 $\operatorname{val}_v(j)\le1$。Legendre 赋值计算推出 $|\lambda|_v=|\lambda-1|_v=1$。此时 $|4|_v=1$，因此只剩 $4(-\log|\ell|_v)$。 [粗界的对数形式](../../../../Solutions/Source_TripodCyclicVeluLog.lean#L101) · [单位因子](../../../../Solutions/Source_TripodCyclicVeluLog.lean#L59) · [参考赋值计算](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/TwoAdic.lean#L258)

### 无限位

对无限位 $v$，定理 `log_infinite_bound` 需要 $1\le C_0$ 和 `LegendreTorsionXBound c C₀`。后者要求在两个参数对数的绝对值均不超过 $c$ 的复 Legendre 曲线上，被正整数 $N$ 消去的仿射点的横坐标绝对值不超过 $C_0N^2$。定理假设 $\log|\lambda|_v$ 和 $\log|\lambda-1|_v$ 在 $v$ 处满足这两个界。对 `infinite_bound` 取对数，并用 $2\ell C_0(4\ell)^2=(32C_0)\ell^3$。移项后两个参数的负半对数各至多贡献 $c/2$，得到

$$
\log|\rho|_v\le 2\log(32C_0)+6\log\ell+c.
$$

[假设](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound.lean#L23) · [适配估计](../../../../Solutions/Source_TripodCyclicVeluLog.lean#L180) · [参考中的阿基米德估计](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/CyclicIsogeny.lean#L889)

## 日本語

tripod の点 $x$ と曲線データの供給元 $P$ を固定する。$P$ が与える曲線を $E/F$、その Legendre パラメータを $\lambda=\operatorname{genC}'(P,x)$、$j$ 不変量を $j=j(E)$ とする。$\ell$ を奇素数とし、$H\subset E(\overline F)$ を位数 $\ell$ の加法部分群とする。$L/F$ を $\ell$ 等分点体とし、$H_L$ を $H$ の $E(L)$ への引き戻しとする。二つの評価はいずれも $H_L$ の `Fintype` インスタンスを用い、$\rho\in F^\times$ の $L$ での像が、指定された二つの Vélu 比 $\operatorname{veluRatio}(H_L,T_i,R_i)$ の積に等しいと仮定する。 [入力](../../../../Solutions/Source_TripodCyclicVeluLog.lean#L93)

### 有限素点

定理 `log_apply_le` は `IsGraphLineOdd` も仮定する。これは、モジュライ体の `VBadOdd` の素点の上にある $L$ の各有限素点 $w$ で、$H_L$ が $w$ における Tate のグラフ直線の引き戻しに等しいという条件である。$F$ の有限素点 $v$ の剰余標数を $p_v$、正規化した絶対値を $|\cdot|_v$ とすると、次が成り立つ。

$$
\log|\rho|_v\le 4(-\log|\ell|_v)+
\begin{cases}
-\dfrac{\ell-1}{4}\log|j|_v
    & v\in\operatorname{badAll},\quad p_v\ne 2,\\
\dfrac92\big|\log|\lambda|_v\big|+\dfrac12\big|\log|\lambda-1|_v\big|+4(-\log|4|_v)
    & p_v=2,\\
0   & v\notin\operatorname{badAll},\quad p_v\ne 2.
\end{cases}
$$

[グラフ直線の条件](../../../../Solutions/Source_TripodCyclicBoundOdd.lean#L145) · [適応版の評価](../../../../Solutions/Source_TripodCyclicVeluLog.lean#L132) · [参照元の評価](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/CyclicIsogeny.lean#L662)

奇剰余標数の乗法的還元素点では、`finite_tate` により $|\rho|_v^4|j|_v^{\ell-1}\le 1$ が得られる。対数を取り、$|\ell|_v\le1$ から$4(-\log|\ell|_v)$ が非負であることを使う。残りの有限素点では `finite_crude` の対数を取る。選んだ $\lambda$ と $1-\lambda$ の平方根は、それぞれ左辺に $\tfrac12\log|\lambda|_v$ と $\tfrac12\log|\lambda-1|_v$ を与える。$p_v=2$ のときは $\log\max(1,|\lambda|_v)\le\big|\log|\lambda|_v\big|$ を用いて係数 $4+\tfrac12=\tfrac92$ を得る。$v$ が `badAll` の外にあり $p_v\ne2$ のとき、安定還元と乗法的還元の除外により、乗法的付値は $\operatorname{val}_v(j)\le1$ を満たす。Legendre の付値の計算から $|\lambda|_v=|\lambda-1|_v=1$ が従う。このとき $|4|_v=1$ でもあるので、$4(-\log|\ell|_v)$ のみが残る。 [粗い評価の対数](../../../../Solutions/Source_TripodCyclicVeluLog.lean#L101) · [絶対値が 1 の因子](../../../../Solutions/Source_TripodCyclicVeluLog.lean#L59) · [参照元の付値計算](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/TwoAdic.lean#L258)

### 無限素点

無限素点 $v$ に対し、定理 `log_infinite_bound` は $1\le C_0$ と `LegendreTorsionXBound c C₀` を仮定する。後者は、パラメータに関する二つの対数の絶対値が $c$ 以下の複素 Legendre 曲線上で、正整数 $N$ 倍で消えるアフィン点の $x$ 座標の絶対値が $C_0N^2$ 以下になるという条件である。定理は $v$ での $\log|\lambda|_v$ と $\log|\lambda-1|_v$ がこの二つの上界を満たすと仮定する。`infinite_bound` の対数を取り、$2\ell C_0(4\ell)^2=(32C_0)\ell^3$ を使う。パラメータの対数を半分にした二つの項を移項すると、それぞれ高々 $c/2$ を与える。したがって次が成り立つ。

$$
\log|\rho|_v\le 2\log(32C_0)+6\log\ell+c.
$$

[仮定](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound.lean#L23) · [適応版の評価](../../../../Solutions/Source_TripodCyclicVeluLog.lean#L180) · [参照元のアルキメデス評価](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/CyclicIsogeny.lean#L889)
