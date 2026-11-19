# CanLift 2.7 Galois closure and descent of the $x$-coordinate

## English

### `canLift27UnramifiedGaloisClosure`

Let $\psi\colon Z\to Y$ be a cover of affine orbicurve presentations over $\mathbb C$. Assume $Z$ has multiplicity one at every maximal ideal of its coordinate ring $Z.A$. Then there exist an affine orbicurve presentation $T$, a cover $\gamma\colon T\to Z$, and a group $G$. The group acts faithfully on $T.A$ by $Y.A$-algebra automorphisms. The $Y.A$-algebra map is $\gamma.f\circ\psi.f$. The fixed ring of this action is exactly the image of $Y.A$ under that map. The cover $\gamma$ has ramification index one at every maximal ideal of $T.A$. [Local statement](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftXDescent.lean:29) · [Local proof](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftUnramifiedClosure.lean:100) · [Pinned Galois closure argument](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/U2/GaloisClosure.lean#L171)

### `canLift27ComplexXDescends_of_analytic`

Let $E$ be a complex elliptic Weierstrass curve with $j(E)$ outside $\{0,1728,488095744/125,1556068/81\}$. Write $X_E$ for its level-one unsigned normalization presentation with trivial subgroup. Write $x_E$ for its distinguished element `normalizationBaseX` in $X_E.A$.

Assume `CanLift27ComplexAutomorphismsFixX`. For every such $E$ and every cover $\pi\colon T\to X_E$, each $\mathbb C$-algebra automorphism of $T.A$ fixes $\pi.f(x_E)$. Under this assumption, take any affine orbicurve presentations $Y,Z$ over $\mathbb C$ with covers $\phi\colon Z\to X_E$ and $\psi\colon Z\to Y$. There exists $y\in Y.A$ such that $\psi.f(y)=\phi.f(x_E)$ in $Z.A$. [Analytic hypothesis](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftXDescent.lean:21) · [Descent statement](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftComplex.lean:28) · [Local implication](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftUnramifiedClosure.lean:149) · [Pinned Theorem G](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/U2/CoreMap.lean#L100)

## 中文

### `canLift27UnramifiedGaloisClosure`

设 $\psi\colon Z\to Y$ 是 $\mathbb C$ 上两个仿射轨形曲线表示之间的覆盖。假设 $Z$ 的坐标环 $Z.A$ 的每个极大理想处的重数都是一。则存在仿射轨形曲线表示 $T$、覆盖 $\gamma\colon T\to Z$ 及一个群 $G$。$G$ 通过 $Y.A$-代数自同构忠实地作用于 $T.A$，其中 $Y.A$-代数结构由映射 $\gamma.f\circ\psi.f$ 给出。该作用的不动环恰为 $Y.A$ 在该映射下的像。对 $T.A$ 的每个极大理想，覆盖 $\gamma$ 的分歧指数均为一。 [本地陈述](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftXDescent.lean:29) · [本地证明](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftUnramifiedClosure.lean:100) · [固定版本的 Galois 闭包论证](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/U2/GaloisClosure.lean#L171)

### `canLift27ComplexXDescends_of_analytic`

设 $E$ 为复 Weierstrass 椭圆曲线，且 $j(E)$ 不属于 $\{0,1728,488095744/125,1556068/81\}$。记 $X_E$ 为层级为一、子群为平凡子群的无符号归一化表示，记 $x_E$ 为 $X_E.A$ 中的指定元素 `normalizationBaseX`。

假设 `CanLift27ComplexAutomorphismsFixX` 成立。对每条这样的 $E$ 及每个覆盖 $\pi\colon T\to X_E$，$T.A$ 的每个 $\mathbb C$-代数自同构都固定 $\pi.f(x_E)$。在该假设下，取 $\mathbb C$ 上任意仿射轨形曲线表示 $Y,Z$ 以及覆盖 $\phi\colon Z\to X_E$ 和 $\psi\colon Z\to Y$。则存在 $y\in Y.A$，使得 $\psi.f(y)=\phi.f(x_E)$ 在 $Z.A$ 中成立。 [解析假设](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftXDescent.lean:21) · [下降陈述](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftComplex.lean:28) · [本地定理](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftUnramifiedClosure.lean:149) · [固定版本的定理 G](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/U2/CoreMap.lean#L100)

## 日本語

### `canLift27UnramifiedGaloisClosure`

$\psi\colon Z\to Y$ を $\mathbb C$ 上のアフィン・オービ曲線表示の被覆とする。$Z$ の座標環 $Z.A$ の各極大イデアルにおける重複度は $1$ と仮定する。このとき、アフィン・オービ曲線表示 $T$、被覆 $\gamma\colon T\to Z$、群 $G$ が存在する。$G$ は $Y.A$-代数自己同型として $T.A$ に忠実に作用する。ここで $Y.A$-代数構造は合成写像 $\gamma.f\circ\psi.f$ で定まる。この作用の不変環は、その写像による $Y.A$ の像に等しい。$T.A$ のどの極大イデアルでも $\gamma$ の分岐指数は $1$ である。 [ローカルの命題](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftXDescent.lean:29) · [ローカルの証明](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftUnramifiedClosure.lean:100) · [固定リビジョンの Galois 閉包の議論](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/U2/GaloisClosure.lean#L171)

### `canLift27ComplexXDescends_of_analytic`

$E$ を $\mathbb C$ 上の Weierstrass 楕円曲線とし、$j(E)$ は $\{0,1728,488095744/125,1556068/81\}$ に属さないとする。レベル $1$ と自明な部分群に対する符号なしの正規化表示を $X_E$ と書く。$X_E.A$ の指定された元 `normalizationBaseX` を $x_E$ と書く。

`CanLift27ComplexAutomorphismsFixX` を仮定する。すなわち、この条件を満たす任意の $E$ と任意の被覆 $\pi\colon T\to X_E$ に対し、$T.A$ の各 $\mathbb C$-代数自己同型は $\pi.f(x_E)$ を固定する。この仮定の下で、$\mathbb C$ 上の任意のアフィン・オービ曲線表示 $Y,Z$ と被覆 $\phi\colon Z\to X_E$ および $\psi\colon Z\to Y$ をとる。このとき、$Z.A$ において $\psi.f(y)=\phi.f(x_E)$ を満たす $y\in Y.A$ が存在する。 [解析的仮定](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftXDescent.lean:21) · [降下の命題](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftComplex.lean:28) · [ローカルの定理](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftUnramifiedClosure.lean:149) · [固定リビジョンの定理 G](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/U2/CoreMap.lean#L100)
