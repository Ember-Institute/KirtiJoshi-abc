# Ramification under a change of parameter

Upstream Pi1 revision `ca7def953193f861a462aa0831eec8f0a31ff69f`. Adapted source SHA-256 `297027c9b25b698e4d2eca428827c1ac11699462e6e5200b8fa83a8290742fb9`. The MCP-CI leaf check and the build with Lean object output both exited with code 0 and reported 17 warnings each. [Adapted source](../../../../Solutions/Source_ReferenceIutCanLiftChangeParameter.lean#L2) · [Leaf check ci-022826-4ed1bcf3](../receipts/round-ci-022826-4ed1bcf3-result.json) · [Leaf build ci-022831-fd4b0e80](../receipts/round-ci-022831-fd4b0e80-result.json)

## English

Let $\Omega/k$ be a field extension, $t\in\Omega$ transcendental over $k$, and $k(t)\subseteq F\subseteq\Omega$. For $s\in F$, `changeParameterField` views the same subfield $F$ over $k(s)$. If $s$ is integral over $k[t]$ and $t$ is integral over $k[s]$, transitivity of integrality identifies the two integral closures in $F$. Write $R_t$ and $R_s$ for these rings. `changeParameterCoordEquiv` gives a $k$-algebra isomorphism $\beta:R_t\to R_s$ that fixes the image in $\Omega$ of every element. [Field over the new parameter](../../../../Solutions/Source_ReferenceIutCanLiftChangeParameter.lean#L50) · [Normalization rings](../../../../Solutions/Source_ReferenceIutCanLiftChangeParameter.lean#L126) · [Pi1 normalization isomorphism](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L296)

When $k$ has characteristic zero and $F/k(t)$ is finite, `finiteDimensional_changeParameter` gives finiteness over $k(s)$ using integrality of $t$ over $k[s]$. Indeed, take a primitive element $\alpha$ for $F/k(t)$. The field $k(s)(t)$ is finite over $k(s)$ and contains $k(t)$, so $\alpha$ is algebraic over $k(s)$. Adjoining $t$ and $\alpha$ gives $F=k(s)(t,\alpha)$. The module also proves the algebraic exchange law. If $s$ is transcendental over $k$ and algebraic over $k[t]$, then $t$ is algebraic over $k[s]$. [Finiteness](../../../../Solutions/Source_ReferenceIutCanLiftChangeParameter.lean#L179) · [Algebraic exchange](../../../../Solutions/Source_ReferenceIutCanLiftChangeParameter.lean#L215) · [Pi1 finiteness](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L335) · [Pi1 exchange](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Descent.lean#L186)

For $s,t$ transcendental over $k$ and integral over the other parameter's polynomial ring, let $e:k[t]\simeq k[s]$ carry $t$ to $s$. Write $\iota_s:k[s]\hookrightarrow R_s$ for the inclusion. The map `parameterMap` from $k[t]$ to $R_t$ is

$$
\varphi=\beta^{-1}\circ\iota_s\circ e.
$$

It is integral and injective. Under the embedding $R_t\subseteq\Omega$, the image of $p(t)$ is $p(s)$ for every $p\in k[X]$. Conversely, `isIntegral_old_parameter` starts with an integral $k$-algebra map $k[t]\to R_t$ that sends $t$ to $s$. Integrality gives a monic equation for the element $t\in R_t$ over the image of that map. Evaluating coefficients at $s$ puts the equation over $k[s]$. [Polynomial line isomorphism](../../../../Solutions/Source_ReferenceIutCanLiftChangeParameter.lean#L254) · [Parameter map](../../../../Solutions/Source_ReferenceIutCanLiftChangeParameter.lean#L315) · [Integral map implies integrality of the old parameter](../../../../Solutions/Source_ReferenceIutCanLiftChangeParameter.lean#L287) · [Pi1 parameter map](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L432) · [Pi1 integrality lemma](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L629)

Assume also that $k$ has characteristic zero and $F/k(t)$ is finite. Write $f^*w$ for contraction along $f$ and $e_f(w)$ for the ramification index over that contraction. For any natural-number-valued function $m$ on ideals of $k[t]$, `parameterMap_ramification_iff` gives

$$
\bigl(\forall w\in\operatorname{MaxSpec} R_t,\quad e_\varphi(w)=m(\varphi^*w)\bigr)
\quad\Longleftrightarrow\quad
\bigl(\forall w_s\in\operatorname{MaxSpec} R_s,\quad e_{\iota_s}(w_s)=m(e^*(\iota_s^*w_s))\bigr).
$$

The two rings have corresponding maximal ideals $w_s=(\beta^{-1})^*w$. The two isomorphisms in $\varphi$ preserve the ramification index, and composition of contractions identifies the ideals supplied to $m$. [Ramification equivalence](../../../../Solutions/Source_ReferenceIutCanLiftChangeParameter.lean#L354) · [Pi1 ramification equivalence](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L494)

MCP-CI review `ci-022835-61a98993` printed only `propext`, `Classical.choice`, and `Quot.sound` for `changeParameterCoordEquiv`, `finiteDimensional_changeParameter`, and `parameterMap_ramification_iff`. [Review source](../ReviewCanLiftCoverTransport.lean#L13) · [Review receipt](../receipts/round-ci-022835-61a98993-result.json)

## 中文

设 $\Omega/k$ 为域扩张，$t\in\Omega$ 在 $k$ 上超越，且 $k(t)\subseteq F\subseteq\Omega$。对 $s\in F$，`changeParameterField` 将同一个子域 $F$ 看作 $k(s)$ 上的中间域。若 $s$ 在 $k[t]$ 上整且 $t$ 在 $k[s]$ 上整，则由整性的传递性可知，两者在 $F$ 中的整闭包一致。分别记这两个环为 $R_t$ 和 $R_s$。`changeParameterCoordEquiv` 给出 $k$-代数同构 $\beta:R_t\to R_s$，保持每个元素在 $\Omega$ 中的像。 [新参数上的中间域](../../../../Solutions/Source_ReferenceIutCanLiftChangeParameter.lean#L50) · [归一化环](../../../../Solutions/Source_ReferenceIutCanLiftChangeParameter.lean#L126) · [Pi1 的归一化环同构](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L296)

若 $k$ 的特征为零且 $F/k(t)$ 有限，`finiteDimensional_changeParameter` 由 $t$ 在 $k[s]$ 上整推出 $F/k(s)$ 有限。取 $F/k(t)$ 的本原元 $\alpha$。$k(s)(t)$ 在 $k(s)$ 上有限且包含 $k(t)$，因此 $\alpha$ 在 $k(s)$ 上代数。添入 $t$ 和 $\alpha$ 得到 $F=k(s)(t,\alpha)$。模块还证明了代数性的交换律。若 $s$ 在 $k$ 上超越且在 $k[t]$ 上代数，则 $t$ 在 $k[s]$ 上代数。 [有限性](../../../../Solutions/Source_ReferenceIutCanLiftChangeParameter.lean#L179) · [代数性交换律](../../../../Solutions/Source_ReferenceIutCanLiftChangeParameter.lean#L215) · [Pi1 的有限性引理](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L335) · [Pi1 的交换律](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Descent.lean#L186)

设 $s,t$ 均在 $k$ 上超越，且各自在另一个参数的多项式环上整。令 $e:k[t]\simeq k[s]$ 为将 $t$ 送到 $s$ 的同构，$\iota_s:k[s]\hookrightarrow R_s$ 为包含映射。`parameterMap` 给出的 $k[t]\to R_t$ 为

$$
\varphi=\beta^{-1}\circ\iota_s\circ e.
$$

此映射是整的且为单射。在嵌入 $R_t\subseteq\Omega$ 下，每个 $p\in k[X]$ 对应的 $p(t)$ 的像是 $p(s)$。反过来，`isIntegral_old_parameter` 从将 $t$ 送到 $s$ 的整 $k$-代数映射 $k[t]\to R_t$ 出发。由整性，$R_t$ 中的元素 $t$ 在映射的像上满足首一方程。将系数在 $s$ 处求值，得到 $t$ 在 $k[s]$ 上的首一方程。 [多项式直线同构](../../../../Solutions/Source_ReferenceIutCanLiftChangeParameter.lean#L254) · [参数映射](../../../../Solutions/Source_ReferenceIutCanLiftChangeParameter.lean#L315) · [由映射的整性推出旧参数的整性](../../../../Solutions/Source_ReferenceIutCanLiftChangeParameter.lean#L287) · [Pi1 的参数映射](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L432) · [Pi1 的整性引理](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L629)

再假设 $k$ 的特征为零且 $F/k(t)$ 有限。以 $f^*w$ 表示沿 $f$ 的收缩，以 $e_f(w)$ 表示相对于该收缩的分歧指数。对 $k[t]$ 的任意理想上的自然数值函数 $m$，`parameterMap_ramification_iff` 给出

$$
\bigl(\forall w\in\operatorname{MaxSpec} R_t,\quad e_\varphi(w)=m(\varphi^*w)\bigr)
\quad\Longleftrightarrow\quad
\bigl(\forall w_s\in\operatorname{MaxSpec} R_s,\quad e_{\iota_s}(w_s)=m(e^*(\iota_s^*w_s))\bigr).
$$

两环的极大理想按 $w_s=(\beta^{-1})^*w$ 对应。$\varphi$ 中的两个同构保持分歧指数，收缩的复合则保证代入 $m$ 的理想相同。 [分歧等价定理](../../../../Solutions/Source_ReferenceIutCanLiftChangeParameter.lean#L354) · [Pi1 的分歧等价定理](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L494)

MCP-CI 审查 `ci-022835-61a98993` 对 `changeParameterCoordEquiv`、`finiteDimensional_changeParameter` 和 `parameterMap_ramification_iff` 仅列出公理 `propext`、`Classical.choice` 和 `Quot.sound`。 [审查源码](../ReviewCanLiftCoverTransport.lean#L13) · [审查回执](../receipts/round-ci-022835-61a98993-result.json)

## 日本語

$\Omega/k$ を体の拡大とし、$t\in\Omega$ は $k$ 上超越的で、$k(t)\subseteq F\subseteq\Omega$ とする。$s\in F$ に対し、`changeParameterField` は同じ部分体 $F$ を $k(s)$ 上の中間体とみなす。$s$ が $k[t]$ 上整であり、$t$ が $k[s]$ 上整であれば、整性の推移性から二つの $F$ における整閉包は一致する。これらの環をそれぞれ $R_t$ と $R_s$ と書く。`changeParameterCoordEquiv` は各元の $\Omega$ での像を保つ $k$-代数同型 $\beta:R_t\to R_s$ を与える。 [新しいパラメータ上の中間体](../../../../Solutions/Source_ReferenceIutCanLiftChangeParameter.lean#L50) · [正規化環](../../../../Solutions/Source_ReferenceIutCanLiftChangeParameter.lean#L126) · [Pi1 の正規化環の同型](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L296)

$k$ の標数が零で $F/k(t)$ が有限ならば、`finiteDimensional_changeParameter` は $t$ が $k[s]$ 上整であることから $F/k(s)$ の有限性を導く。$F/k(t)$ の原始元 $\alpha$ を取る。$k(s)(t)$ は $k(s)$ 上有限で $k(t)$ を含むため、$\alpha$ は $k(s)$ 上代数的である。$t$ と $\alpha$ を添加すると $F=k(s)(t,\alpha)$ を得る。このモジュールは代数性の交換則も証明する。$s$ が $k$ 上超越的で $k[t]$ 上代数的ならば、$t$ は $k[s]$ 上代数的である。 [有限性](../../../../Solutions/Source_ReferenceIutCanLiftChangeParameter.lean#L179) · [代数性の交換則](../../../../Solutions/Source_ReferenceIutCanLiftChangeParameter.lean#L215) · [Pi1 の有限性の補題](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L335) · [Pi1 の交換則](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Descent.lean#L186)

$s,t$ はいずれも $k$ 上超越的で、互いに相手のパラメータの多項式環上整とする。$t$ を $s$ に移す同型を $e:k[t]\simeq k[s]$、包含を $\iota_s:k[s]\hookrightarrow R_s$ とする。`parameterMap` が与える $k[t]\to R_t$ は

$$
\varphi=\beta^{-1}\circ\iota_s\circ e
$$

である。この写像は整かつ単射である。埋め込み $R_t\subseteq\Omega$ のもとで、各 $p\in k[X]$ について $p(t)$ の像は $p(s)$ である。逆に、`isIntegral_old_parameter` では、$t$ を $s$ に移す整な $k$-代数写像 $k[t]\to R_t$ を仮定する。整性から、$R_t$ の元 $t$ は写像の像上のモニック方程式を満たす。係数を $s$ で評価すると、$t$ の $k[s]$ 上のモニック方程式を得る。 [多項式環の同型](../../../../Solutions/Source_ReferenceIutCanLiftChangeParameter.lean#L254) · [パラメータ写像](../../../../Solutions/Source_ReferenceIutCanLiftChangeParameter.lean#L315) · [写像の整性から従う元のパラメータの整性](../../../../Solutions/Source_ReferenceIutCanLiftChangeParameter.lean#L287) · [Pi1 のパラメータ写像](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L432) · [Pi1 の整性の補題](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L629)

さらに $k$ の標数は零で $F/k(t)$ は有限とする。$f$ に沿った縮約を $f^*w$、その縮約上での分岐指数を $e_f(w)$ と書く。$k[t]$ のイデアルに自然数を対応させる任意の関数 $m$ に対し、`parameterMap_ramification_iff` により

$$
\bigl(\forall w\in\operatorname{MaxSpec} R_t,\quad e_\varphi(w)=m(\varphi^*w)\bigr)
\quad\Longleftrightarrow\quad
\bigl(\forall w_s\in\operatorname{MaxSpec} R_s,\quad e_{\iota_s}(w_s)=m(e^*(\iota_s^*w_s))\bigr)
$$

が成り立つ。二つの環の極大イデアルは $w_s=(\beta^{-1})^*w$ で対応する。$\varphi$ を構成する二つの同型は分岐指数を保つ。縮約の合成により、$m$ の引数となるイデアルも一致する。 [分岐条件の同値性](../../../../Solutions/Source_ReferenceIutCanLiftChangeParameter.lean#L354) · [Pi1 の分岐条件の同値性](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L494)

MCP-CI レビュー `ci-022835-61a98993` は、`changeParameterCoordEquiv`、`finiteDimensional_changeParameter`、`parameterMap_ramification_iff` の公理として `propext`、`Classical.choice`、`Quot.sound` だけを出力した。 [レビューのソース](../ReviewCanLiftCoverTransport.lean#L13) · [レビュー結果](../receipts/round-ci-022835-61a98993-result.json)
