# Ramification multiplicities of the sign quotient

Upstream Pi1 revision `ca7def953193f861a462aa0831eec8f0a31ff69f`. Adapted source SHA-256 `d43f05510e5944b5e180802fbf16cc5235a76a46e6379d2ad51eeb0dac032591`. The MCP-CI leaf check and the build with Lean object output both exited with code 0 and reported 18 warnings each. [Adapted source](../../../../Solutions/Source_ReferenceIutCanLiftSignMultiplicity.lean#L2) · [Leaf check ci-022820-4b309914](../receipts/round-ci-022820-4b309914-result.json) · [Leaf build ci-022827-32a80b79](../receipts/round-ci-022827-32a80b79-result.json)

## English

Let $\Omega/k$ be a field extension with $k$ of characteristic zero. Take $t,y\in\Omega$ with $t$ transcendental over $k$. Write $N=k(t)(y)$ and let $A$ be the integral closure of $k[t]$ in $N$. The definition `signQuotientMultiplicity` assigns to an ideal $v$ of $k[t]$ the value $m_k(v)=v.\mathrm{ramificationIdxIn}(A)$. For a finite Galois extension $N/k(t)$, take a maximal ideal $w$ of $A$ and set $v=w\cap k[t]$. The theorem `signQuotientMultiplicity_eq_index` gives $e(w/v)=m_k(v)$. The Galois action on the normalization gives the same index at every prime above $v$, so the index agrees with the one used in the definition. [Multiplicity definition](../../../../Solutions/Source_ReferenceIutCanLiftSignMultiplicity.lean#L105) · [Index theorem](../../../../Solutions/Source_ReferenceIutCanLiftSignMultiplicity.lean#L114) · [Pi1 index theorem](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/HemiTY.lean#L155)

When $\Omega$ is algebraically closed and $y^2+by=c$ with $b,c\in k(t)$, the two possible roots of $Y^2+bY-c$ are $y$ and $-y-b$. Both belong to $N$. The equation gives finiteness, the splitting field gives normality, and characteristic zero gives separability. These facts supply the finite Galois hypotheses. [Finiteness](../../../../Solutions/Source_ReferenceIutCanLiftSignMultiplicity.lean#L38) · [Splitting field argument](../../../../Solutions/Source_ReferenceIutCanLiftSignMultiplicity.lean#L43) · [Galois extension](../../../../Solutions/Source_ReferenceIutCanLiftSignMultiplicity.lean#L91)

For constant extension, take a field tower $k\subseteq K\subseteq\Omega$ with $K$ of characteristic zero, $\Omega$ algebraically closed, and $t$ transcendental over $K$. Keep the quadratic equation with coefficients in $k(t)$. Let $N'=K(t)(y)=K(t)(N)$, and let $A'$ be the integral closure of $K[t]$ in $N'$. For a maximal ideal $v'$ of $K[t]$ with nonzero contraction $v=v'\cap k[t]$, `signQuotientMultiplicity_constantExtension` gives

$$
m_K(v')=m_k(v).
$$

[Constant-extension theorem](../../../../Solutions/Source_ReferenceIutCanLiftSignMultiplicity.lean#L167) · [Pi1 nonzero-contraction case](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/HemiTY.lean#L256)

Lift $v'$ to a maximal ideal $w'$ of $A'$ and contract $w'$ to $w$ in $A$. The inclusions form a commutative square, so $w\cap k[t]=v$. Since $v\ne0$, the prime $w$ is nonzero and hence maximal in the Dedekind domain $A$. The ramification-index comparison gives $e(w'/v')=e(w/v)$. Apply the index theorem on both sides to obtain the multiplicity equality. The descended-cover proof uses this equality after contracting along the polynomial-line isomorphism. [Lift and compare](../../../../Solutions/Source_ReferenceIutCanLiftSignMultiplicity.lean#L188) · [Ramification-index comparison](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L371) · [Use in cover descent](../../../../Solutions/Source_ReferenceIutCanLiftDescendedCover.lean#L85)

MCP-CI review `ci-022835-61a98993` printed only `propext`, `Classical.choice`, and `Quot.sound` for both theorems. [Review source](../ReviewCanLiftCoverTransport.lean#L16) · [Review receipt](../receipts/round-ci-022835-61a98993-result.json)

## 中文

设 $\Omega/k$ 为域扩张，$k$ 的特征为零。取 $t,y\in\Omega$，其中 $t$ 在 $k$ 上超越。记 $N=k(t)(y)$，令 $A$ 为 $k[t]$ 在 $N$ 中的整闭包。定义 `signQuotientMultiplicity` 对 $k[t]$ 的理想 $v$ 赋值 $m_k(v)=v.\mathrm{ramificationIdxIn}(A)$。设 $N/k(t)$ 是有限 Galois 扩张，取 $A$ 的极大理想 $w$，令 $v=w\cap k[t]$。定理 `signQuotientMultiplicity_eq_index` 给出 $e(w/v)=m_k(v)$。归一化环上的 Galois 作用保证 $v$ 上方各素理想的分歧指数相同，因而等于定义中所取的指数。 [重数定义](../../../../Solutions/Source_ReferenceIutCanLiftSignMultiplicity.lean#L105) · [分歧指数定理](../../../../Solutions/Source_ReferenceIutCanLiftSignMultiplicity.lean#L114) · [Pi1 分歧指数定理](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/HemiTY.lean#L155)

若 $\Omega$ 为代数闭域，且 $y^2+by=c$，其中 $b,c\in k(t)$，则 $Y^2+bY-c$ 的两个可能的根为 $y$ 和 $-y-b$，均在 $N$ 中。二次方程给出有限性，分裂域给出正规性，特征零给出可分性。由此得到有限 Galois 扩张所需的条件。 [有限性](../../../../Solutions/Source_ReferenceIutCanLiftSignMultiplicity.lean#L38) · [分裂域论证](../../../../Solutions/Source_ReferenceIutCanLiftSignMultiplicity.lean#L43) · [Galois 扩张](../../../../Solutions/Source_ReferenceIutCanLiftSignMultiplicity.lean#L91)

对于常数扩张，取域塔 $k\subseteq K\subseteq\Omega$，其中 $K$ 的特征为零，$\Omega$ 为代数闭域，且 $t$ 在 $K$ 上超越。仍取系数在 $k(t)$ 中的上述二次方程。记 $N'=K(t)(y)=K(t)(N)$，令 $A'$ 为 $K[t]$ 在 $N'$ 中的整闭包。若 $K[t]$ 的极大理想 $v'$ 的收缩 $v=v'\cap k[t]$ 非零，则 `signQuotientMultiplicity_constantExtension` 给出

$$
m_K(v')=m_k(v).
$$

[常数扩张定理](../../../../Solutions/Source_ReferenceIutCanLiftSignMultiplicity.lean#L167) · [Pi1 的非零收缩情形](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/HemiTY.lean#L256)

将 $v'$ 提升为 $A'$ 的极大理想 $w'$，再将 $w'$ 收缩到 $A$ 得到 $w$。环的包含映射组成交换方块，因此 $w\cap k[t]=v$。由 $v\ne0$ 得到 $w$ 是 Dedekind 整环 $A$ 的非零素理想，因而为极大理想。分歧指数比较给出 $e(w'/v')=e(w/v)$。对两边分别应用分歧指数定理，得到重数等式。覆盖下降的证明先沿多项式直线的同构收缩理想，再使用这个等式。 [提升与比较](../../../../Solutions/Source_ReferenceIutCanLiftSignMultiplicity.lean#L188) · [分歧指数比较](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L371) · [覆盖下降中的使用](../../../../Solutions/Source_ReferenceIutCanLiftDescendedCover.lean#L85)

MCP-CI 审查 `ci-022835-61a98993` 对两条定理各自仅列出公理 `propext`、`Classical.choice` 和 `Quot.sound`。 [审查源码](../ReviewCanLiftCoverTransport.lean#L16) · [审查回执](../receipts/round-ci-022835-61a98993-result.json)

## 日本語

$\Omega/k$ を体の拡大とし、$k$ の標数を零とする。$t,y\in\Omega$ を取り、$t$ は $k$ 上超越的とする。$N=k(t)(y)$ と書き、$A$ を $k[t]$ の $N$ における整閉包とする。定義 `signQuotientMultiplicity` は $k[t]$ のイデアル $v$ に $m_k(v)=v.\mathrm{ramificationIdxIn}(A)$ を対応させる。$N/k(t)$ を有限 Galois 拡大とし、$A$ の極大イデアル $w$ に対して $v=w\cap k[t]$ と置く。定理 `signQuotientMultiplicity_eq_index` は $e(w/v)=m_k(v)$ を与える。正規化環への Galois 作用により $v$ の上の各素イデアルの分岐指数が一致するため、定義で選んだ分岐指数と等しくなる。 [重複度の定義](../../../../Solutions/Source_ReferenceIutCanLiftSignMultiplicity.lean#L105) · [分岐指数の定理](../../../../Solutions/Source_ReferenceIutCanLiftSignMultiplicity.lean#L114) · [Pi1 の分岐指数の定理](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/HemiTY.lean#L155)

$\Omega$ が代数閉体で、$b,c\in k(t)$ に対して $y^2+by=c$ が成り立つとき、$Y^2+bY-c$ の根は $y$ と $-y-b$ であり、いずれも $N$ に属する。二次方程式から有限性、分解体から正規性、標数零から分離性が従う。これにより有限 Galois 拡大の仮定を満たす。 [有限性](../../../../Solutions/Source_ReferenceIutCanLiftSignMultiplicity.lean#L38) · [分解体の議論](../../../../Solutions/Source_ReferenceIutCanLiftSignMultiplicity.lean#L43) · [Galois 拡大](../../../../Solutions/Source_ReferenceIutCanLiftSignMultiplicity.lean#L91)

定数体の拡大では、体の塔 $k\subseteq K\subseteq\Omega$ を取り、$K$ の標数を零、$\Omega$ を代数閉体とし、$t$ は $K$ 上超越的とする。係数が $k(t)$ に属する上の二次方程式を用いる。$N'=K(t)(y)=K(t)(N)$ とし、$A'$ を $K[t]$ の $N'$ における整閉包とする。$K[t]$ の極大イデアル $v'$ の縮約 $v=v'\cap k[t]$ が零でなければ、`signQuotientMultiplicity_constantExtension` により

$$
m_K(v')=m_k(v)
$$

が成り立つ。 [定数体拡大の定理](../../../../Solutions/Source_ReferenceIutCanLiftSignMultiplicity.lean#L167) · [Pi1 で縮約が零でない場合](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/HemiTY.lean#L256)

$v'$ を $A'$ の極大イデアル $w'$ に持ち上げ、$w'$ を $A$ に縮約して $w$ を得る。環の包含がつくる四角形は可換なので、$w\cap k[t]=v$ となる。$v\ne0$ なので $w$ は Dedekind 整域 $A$ の零でない素イデアルであり、したがって極大である。分岐指数の比較により $e(w'/v')=e(w/v)$ を得る。両辺に分岐指数の定理を適用すると重複度の等式が従う。被覆の降下の証明では、多項式環の同型に沿ってイデアルを縮約した後でこの等式を使う。 [持ち上げと比較](../../../../Solutions/Source_ReferenceIutCanLiftSignMultiplicity.lean#L188) · [分岐指数の比較](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L371) · [被覆の降下での使用](../../../../Solutions/Source_ReferenceIutCanLiftDescendedCover.lean#L85)

MCP-CI レビュー `ci-022835-61a98993` は、二つの定理の公理としてそれぞれ `propext`、`Classical.choice`、`Quot.sound` だけを出力した。 [レビューのソース](../ReviewCanLiftCoverTransport.lean#L16) · [レビュー結果](../receipts/round-ci-022835-61a98993-result.json)
