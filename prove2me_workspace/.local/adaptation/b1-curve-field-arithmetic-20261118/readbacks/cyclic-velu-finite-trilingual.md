# The finite-place Vélu bound from the Newton estimate

## English

Let $K$ be a number field and $W=\operatorname{legendre}(\lambda)$ an elliptic curve with $\lambda\in K^\times$. For a finite place $w$ and $a\ne0$, use the normalized absolute value $|a|_w=(N\mathfrak p_w)^{-\operatorname{ord}_w(a)}$ with $N\mathfrak p_w=p_w^{f_w}$. Here $\operatorname{ord}_w$ gives 1 on a uniformizer, $p_w$ is the residue characteristic, and $f_w$ is the absolute residue degree. [Normalization](../../../../Solutions/Source_TripodFinitePlaceArithmetic.lean#L125)

For a nonsingular affine point $(x,y)$ killed by $n\ge1$, `apply_x_le_legendre` gives $|n|_w^2|x|_w\le\max(1,|\lambda|_w)^2$. If $|\lambda|_w\le1$, the Legendre coefficients are integral. If $|\lambda|_w>1$, use $x=\lambda^2 X$ and $y=\lambda^3 Y$. The new coefficients $a_2=-(\lambda^{-2}+\lambda^{-1})$ and $a_4=\lambda^{-3}$ are integral. The factor $|\lambda|_w^2$ comes from returning to $x$. [Adapted Newton estimate](../../../../Solutions/Source_TripodCyclicVeluFinite.lean#L28) · [Reference Newton estimate](../../../../../refer/iut/Iut/Tripod/TorsionNewton.lean#L141)

For `crude_bound`, take a finite additive subgroup $H\subset W(K)$ of odd prime order $\ell$. Take $T\ne O$ with $[2]T=O$ and $R$ with $[2]R=T$. Write $x(S)$ for the first coordinate, with $x(O)=0$. The reference defines

$$
r=\prod_{Q\in H\setminus\{O\}}\frac{x(T)-x(R+Q)}{x(T)-x(Q)}.
$$

Then for every finite $w$,

$$
|r|_w\,|x(T)-x(R)|_w\,|4\ell|_w^2\le \max(1,|\lambda|_w)^2.
$$

The Vélu identity expresses $r(x(T)-x(R))$ as the sum of $x(T+Q)-x(R+Q)$ over $H$. The translates are nonzero and killed by $4\ell$. The ultrametric inequality bounds the sum by the largest bound on a term. [Ratio definition](../../../../../refer/iut/Iut/Tripod/CyclicPoints.lean#L199) · [Reference crude bound](../../../../../refer/iut/Iut/Tripod/CyclicIsogeny.lean#L347) · [Adapted crude bound](../../../../Solutions/Source_TripodCyclicVeluFinite.lean#L90)

The adapted `finite_crude` applies the estimate to both designated pairs over the $\ell$-torsion field $L/F$. Let $\rho\in F$ map to $r_1r_2$ in $L$ and let $a,b\in F$ be the selected roots of $\lambda$ and $1-\lambda$. The two coordinate differences are the images of $-a$ and $-b$. The absolute values transport through the positive exponent $e(w/v)f(w/v)$ for $w$ above $v$. For every finite $v$ of $F$ this gives

$$
|\rho|_v\,|a|_v\,|b|_v\,|4\ell|_v^4\le\max(1,|\lambda|_v)^4.
$$

[Designated coordinate differences](../../../../Solutions/Source_TripodCyclicVeluPoints.lean#L282) · [Transport](../../../../Solutions/Source_TripodRelativeAbsoluteValue.lean#L17) · [Reference base-field bound](../../../../../refer/iut/Iut/Tripod/CyclicIsogeny.lean#L576)

## 中文

设 $K$ 为数域，$W=\operatorname{legendre}(\lambda)$ 为椭圆曲线，且 $\lambda\in K^\times$。对有限位 $w$ 及 $a\ne0$，用归一化绝对值 $|a|_w=(N\mathfrak p_w)^{-\operatorname{ord}_w(a)}$，其中 $N\mathfrak p_w=p_w^{f_w}$。$\operatorname{ord}_w$ 在素元上取 1，$p_w$ 为剩余特征，$f_w$ 为绝对剩余次数。 [归一化](../../../../Solutions/Source_TripodFinitePlaceArithmetic.lean#L125)

设非奇异仿射点 $(x,y)$ 被 $n\ge1$ 消去。`apply_x_le_legendre` 给出 $|n|_w^2|x|_w\le\max(1,|\lambda|_w)^2$。若 $|\lambda|_w\le1$，Legendre 模型的系数为整。若 $|\lambda|_w>1$，用 $x=\lambda^2 X$、$y=\lambda^3 Y$ 变换，得到整系数 $a_2=-(\lambda^{-2}+\lambda^{-1})$ 和 $a_4=\lambda^{-3}$。还原到 $x$ 时产生因子 $|\lambda|_w^2$。 [适配的 Newton 估计](../../../../Solutions/Source_TripodCyclicVeluFinite.lean#L28) · [参考 Newton 估计](../../../../../refer/iut/Iut/Tripod/TorsionNewton.lean#L141)

对 `crude_bound`，取 $W(K)$ 中奇素数阶 $\ell$ 的有限加法子群 $H$。取 $T\ne O$ 满足 $[2]T=O$，以及 $R$ 满足 $[2]R=T$。记横坐标为 $x(S)$，约定 $x(O)=0$。参考定义为

$$
r=\prod_{Q\in H\setminus\{O\}}\frac{x(T)-x(R+Q)}{x(T)-x(Q)}.
$$

对每个有限位 $w$，有

$$
|r|_w\,|x(T)-x(R)|_w\,|4\ell|_w^2\le \max(1,|\lambda|_w)^2.
$$

Vélu 恒等式把 $r(x(T)-x(R))$ 写为 $x(T+Q)-x(R+Q)$ 对 $H$ 的和。每个平移点均非零，且被 $4\ell$ 消去。超度量不等式用各项上界的最大值控制该和。 [比值定义](../../../../../refer/iut/Iut/Tripod/CyclicPoints.lean#L199) · [参考粗界](../../../../../refer/iut/Iut/Tripod/CyclicIsogeny.lean#L347) · [适配的粗界](../../../../Solutions/Source_TripodCyclicVeluFinite.lean#L90)

适配后的 `finite_crude` 在 $\ell$ 挠点域 $L/F$ 上对两个指定点对应用此界。设 $\rho\in F$ 在 $L$ 中的像为 $r_1r_2$，且 $a,b\in F$ 分别为 $\lambda,1-\lambda$ 的所选平方根。两个坐标差分别是 $-a,-b$ 在 $L$ 中的像。若 $w$ 位于 $v$ 上方，绝对值通过正指数 $e(w/v)f(w/v)$ 传递。于是对 $F$ 的每个有限位 $v$，有

$$
|\rho|_v\,|a|_v\,|b|_v\,|4\ell|_v^4\le\max(1,|\lambda|_v)^4.
$$

[指定坐标差](../../../../Solutions/Source_TripodCyclicVeluPoints.lean#L282) · [绝对值传递](../../../../Solutions/Source_TripodRelativeAbsoluteValue.lean#L17) · [参考基域界](../../../../../refer/iut/Iut/Tripod/CyclicIsogeny.lean#L576)

## 日本語

$K$ を数体、$W=\operatorname{legendre}(\lambda)$ を楕円曲線とし、$\lambda\in K^\times$ とする。有限素点 $w$ と $a\ne0$ に対し、正規化した絶対値を $|a|_w=(N\mathfrak p_w)^{-\operatorname{ord}_w(a)}$ とする。ここで $N\mathfrak p_w=p_w^{f_w}$ であり、$\operatorname{ord}_w$ は素元で 1 を取る。$p_w$ は剰余標数、$f_w$ は絶対剰余次数である。 [正規化](../../../../Solutions/Source_TripodFinitePlaceArithmetic.lean#L125)

$n\ge1$ 倍で零になる非特異アフィン点 $(x,y)$ に対し、`apply_x_le_legendre` は $|n|_w^2|x|_w\le\max(1,|\lambda|_w)^2$ を与える。$|\lambda|_w\le1$ なら Legendre モデルの係数は整である。$|\lambda|_w>1$ なら $x=\lambda^2 X$ と $y=\lambda^3 Y$ によって、整係数 $a_2=-(\lambda^{-2}+\lambda^{-1})$ と $a_4=\lambda^{-3}$ を得る。$x$ に戻すと係数 $|\lambda|_w^2$ が現れる。 [移植した Newton 評価](../../../../Solutions/Source_TripodCyclicVeluFinite.lean#L28) · [参照元の Newton 評価](../../../../../refer/iut/Iut/Tripod/TorsionNewton.lean#L141)

`crude_bound` では、$W(K)$ の奇素数位数 $\ell$ の有限加法部分群 $H$ を取る。$[2]T=O$ を満たす $T\ne O$ と $[2]R=T$ を満たす $R$ を取る。第一座標を $x(S)$ と書き、$x(O)=0$ とする。参照元は次の比を定める。

$$
r=\prod_{Q\in H\setminus\{O\}}\frac{x(T)-x(R+Q)}{x(T)-x(Q)}.
$$

任意の有限素点 $w$ で

$$
|r|_w\,|x(T)-x(R)|_w\,|4\ell|_w^2\le \max(1,|\lambda|_w)^2
$$

が成り立つ。Vélu の恒等式は $r(x(T)-x(R))$ を $x(T+Q)-x(R+Q)$ の $H$ 上の和で表す。平行移動した点は零点と異なり、$4\ell$ 倍で零になる。超距離不等式により、各項の上界の最大値が和の上界になる。 [比の定義](../../../../../refer/iut/Iut/Tripod/CyclicPoints.lean#L199) · [参照元の粗い評価](../../../../../refer/iut/Iut/Tripod/CyclicIsogeny.lean#L347) · [移植した粗い評価](../../../../Solutions/Source_TripodCyclicVeluFinite.lean#L90)

移植した `finite_crude` は、$\ell$-ねじれ点体 $L/F$ 上の指定された二組の点にこの評価を使う。$\rho\in F$ の $L$ における像を $r_1r_2$ とする。$a,b\in F$ は $\lambda,1-\lambda$ の選んだ平方根であり、二つの座標差は $-a,-b$ の像である。$w$ が $v$ の上にあるとき、絶対値は正の指数 $e(w/v)f(w/v)$ によって移される。従って $F$ の任意の有限素点 $v$ で

$$
|\rho|_v\,|a|_v\,|b|_v\,|4\ell|_v^4\le\max(1,|\lambda|_v)^4
$$

が成り立つ。 [指定した座標差](../../../../Solutions/Source_TripodCyclicVeluPoints.lean#L282) · [絶対値の移行](../../../../Solutions/Source_TripodRelativeAbsoluteValue.lean#L17) · [参照元の基礎体での上界](../../../../../refer/iut/Iut/Tripod/CyclicIsogeny.lean#L576)
