# Étaleness after extending the constant field

Upstream Pi1 revision `ca7def953193f861a462aa0831eec8f0a31ff69f`. Adapted source SHA-256 `1e9c4a4e82d494177dcf52325bd7a60ae2f47b9ba2173b48f7a724d631ce3c14`. The MCP-CI leaf check and the build with Lean object output both exited with code 0 and reported 15 tactic-suggestion warnings each. [Adapted source](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionForward.lean#L2) · [Leaf check ci-022802-e3b86255](../receipts/round-ci-022802-e3b86255-result.json) · [Leaf build ci-022821-252c5286](../receipts/round-ci-022821-252c5286-result.json)

## English

Let $k\to K\to\Omega$ be a field tower, with $k$ of characteristic zero and $\Omega$ algebraically closed. Let $t\in\Omega$ be transcendental over $K$. For a finite extension $F_2/k(t)$ in $\Omega$, set $F_2'=K(t)(F_2)$ and take any $K(t)\subseteq F_1'\subseteq F_2'$. Write $A(F)$ for the integral closure of $k[t]$ in $F$ and $A'(F')$ for the integral closure of $K[t]$ in $F'$. If a maximal ideal $w'$ of $A'(F_2')$ contracts to zero in $A(F_2)$, `ramificationIdx_constantExtension_of_comap_bot` gives ramification index $1$ over $A'(F_1')$. [Zero-contraction theorem](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionForward.lean#L53) · [Pi1 zero-contraction case](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/BaseChange.lean#L863)

Choose a finite Galois extension $N/k(t)$ containing $F_2$ and put $N'=K(t)(N)$. Lift $w'$ to a maximal ideal $u'$ of $A'(N')$. Its contraction $u$ to $A(N)$ contracts further to zero in $A(F_2)$, so integrality of $A(F_2)\subseteq A(N)$ gives $u=0$. An inertia element at $u'$ restricts to an inertia element at $u$. Since $u=0$, this restriction fixes $A(N)$ pointwise and thus fixes its fraction field $N$. Restriction from $\operatorname{Gal}(N'/K(t))$ is injective because $K(t)$ and $N$ generate $N'$. The inertia group at $u'$ is therefore trivial, so the inertia criterion gives index $1$ at $w'$. [Inertia argument](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionForward.lean#L26) · [Pi1 inertia lemma](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/BaseChange.lean#L425) · [Inertia criterion](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/FunctionFieldNormalizationInertia.lean#L123)

For `etale_constantExtension`, also take $k(t)\subseteq F_1\subseteq F_2$ and require $F_1'=K(t)(F_1)$. Write $A_i=A(F_i)$ and $A_i'=A'(F_i')$. Let $m_i$ and $m_i'$ assign natural numbers to ideals of $A_i$ and $A_i'$ respectively. For each $i=1,2$, assume two rules for a maximal ideal $q'$ of $A_i'$ with contraction $q$ to $A_i$. If $q=0$, require $m_i'(q')=1$. If $q\ne0$, require $m_i'(q')=m_i(q)$. If $e(w/v)m_2(w)=m_1(v)$ for every maximal $w$ of $A_2$ and its contraction $v$ to $A_1$, then

$$
e(w'/v')\,m_2'(w')=m_1'(v')
$$

for every maximal $w'$ of $A_2'$ and its contraction $v'$ to $A_1'$. Here $e$ denotes the ramification index for the indicated inclusion. [Forward theorem](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionForward.lean#L102) · [Pi1 forward theorem](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L148)

Let $w$ be the contraction of $w'$ to $A_2$. Integrality gives maximality of $v'$. The commutative square of inclusions identifies the contraction of $v'$ to $A_1$ with the contraction of $w$ to $A_1$. When $w=0$, that contraction is also zero. Both upper multiplicities and the upper ramification index then equal $1$. When $w\ne0$, it is maximal in the Dedekind domain $A_2$, and integrality makes its contraction $v$ to $A_1$ nonzero. Use $e(w'/v')=e(w/v)$ and both multiplicity equalities to obtain the upper identity from the lower one. [Proof by contraction](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionForward.lean#L133) · [Index equality](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L371)

MCP-CI review `ci-022835-61a98993` printed only `propext`, `Classical.choice`, and `Quot.sound` for `ramificationIdx_constantExtension_of_comap_bot` and `etale_constantExtension`. [Review source](../ReviewCanLiftCoverTransport.lean#L11) · [Review receipt](../receipts/round-ci-022835-61a98993-result.json)

## 中文

设 $k\to K\to\Omega$ 为域塔，其中 $k$ 的特征为零，$\Omega$ 为代数闭域，且 $t\in\Omega$ 在 $K$ 上超越。对 $\Omega$ 内的有限扩张 $F_2/k(t)$，令 $F_2'=K(t)(F_2)$，并任取 $K(t)\subseteq F_1'\subseteq F_2'$。记 $A(F)$ 为 $k[t]$ 在 $F$ 中的整闭包，$A'(F')$ 为 $K[t]$ 在 $F'$ 中的整闭包。若 $A'(F_2')$ 的极大理想 $w'$ 在 $A(F_2)$ 中的收缩为零，则 `ramificationIdx_constantExtension_of_comap_bot` 给出 $w'$ 在 $A'(F_1')$ 上的分歧指数为 $1$。 [零收缩定理](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionForward.lean#L53) · [Pi1 的零收缩情形](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/BaseChange.lean#L863)

取包含 $F_2$ 的有限 Galois 扩张 $N/k(t)$，令 $N'=K(t)(N)$。将 $w'$ 提升为 $A'(N')$ 的极大理想 $u'$。$u'$ 在 $A(N)$ 中的收缩 $u$ 进一步收缩到 $A(F_2)$ 为零，由 $A(F_2)\subseteq A(N)$ 的整性得 $u=0$。$u'$ 的惯性群元素限制为 $u$ 的惯性群元素。由于 $u=0$，限制逐点固定 $A(N)$，从而固定其分式域 $N$。$K(t)$ 与 $N$ 生成 $N'$，所以从 $\operatorname{Gal}(N'/K(t))$ 出发的限制映射为单射。于是 $u'$ 的惯性群平凡，由惯性判据得 $w'$ 的分歧指数为 $1$。 [惯性群论证](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionForward.lean#L26) · [Pi1 惯性群引理](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/BaseChange.lean#L425) · [惯性判据](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/FunctionFieldNormalizationInertia.lean#L123)

对 `etale_constantExtension`，再取 $k(t)\subseteq F_1\subseteq F_2$，并要求 $F_1'=K(t)(F_1)$。记 $A_i=A(F_i)$，$A_i'=A'(F_i')$。令 $m_i$ 和 $m_i'$ 分别为 $A_i$ 和 $A_i'$ 的理想上的自然数值函数。对 $i=1,2$ 的每个 $A_i'$ 的极大理想 $q'$，设其在 $A_i$ 中的收缩为 $q$。要求 $q=0$ 时 $m_i'(q')=1$，且 $q\ne0$ 时 $m_i'(q')=m_i(q)$。若对 $A_2$ 的每个极大理想 $w$ 及其在 $A_1$ 中的收缩 $v$ 均有 $e(w/v)m_2(w)=m_1(v)$，则对 $A_2'$ 的每个极大理想 $w'$ 及其在 $A_1'$ 中的收缩 $v'$ 成立

$$
e(w'/v')\,m_2'(w')=m_1'(v').
$$

其中 $e$ 表示相应包含映射的分歧指数。 [常数扩张定理](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionForward.lean#L102) · [Pi1 常数扩张定理](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L148)

记 $w$ 为 $w'$ 在 $A_2$ 中的收缩。由整性，$v'$ 为极大理想。包含映射组成交换方块，所以 $v'$ 和 $w$ 在 $A_1$ 中的收缩相等。当 $w=0$ 时，该收缩也为零，两项上方重数和上方分歧指数均为 $1$。当 $w\ne0$ 时，$w$ 在 Dedekind 整环 $A_2$ 中为极大理想，且整性保证其在 $A_1$ 中的收缩 $v$ 非零。将 $e(w'/v')=e(w/v)$ 和两项重数等式代入，即可由下方等式得到上方等式。 [按收缩分类的证明](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionForward.lean#L133) · [分歧指数等式](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L371)

MCP-CI 审查 `ci-022835-61a98993` 对 `ramificationIdx_constantExtension_of_comap_bot` 和 `etale_constantExtension` 仅列出公理 `propext`、`Classical.choice` 和 `Quot.sound`。 [审查源码](../ReviewCanLiftCoverTransport.lean#L11) · [审查回执](../receipts/round-ci-022835-61a98993-result.json)

## 日本語

$k\to K\to\Omega$ を体の塔とし、$k$ の標数を零、$\Omega$ を代数閉体とする。$t\in\Omega$ は $K$ 上超越的とする。$\Omega$ 内の有限拡大 $F_2/k(t)$ に対し $F_2'=K(t)(F_2)$ とし、任意の $K(t)\subseteq F_1'\subseteq F_2'$ を取る。$A(F)$ を $k[t]$ の $F$ における整閉包、$A'(F')$ を $K[t]$ の $F'$ における整閉包とする。$A'(F_2')$ の極大イデアル $w'$ の $A(F_2)$ への縮約が零ならば、`ramificationIdx_constantExtension_of_comap_bot` により、$w'$ の $A'(F_1')$ 上の分岐指数は $1$ となる。 [零に縮約する場合の定理](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionForward.lean#L53) · [Pi1 で縮約が零の場合](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/BaseChange.lean#L863)

$F_2$ を含む有限 Galois 拡大 $N/k(t)$ を取り、$N'=K(t)(N)$ とする。$w'$ を $A'(N')$ の極大イデアル $u'$ に持ち上げる。$u'$ の $A(N)$ への縮約 $u$ はさらに $A(F_2)$ で零に縮約するため、$A(F_2)\subseteq A(N)$ の整性から $u=0$ となる。$u'$ の惰性群の元を制限すると $u$ の惰性群の元になる。$u=0$ なので、この制限は $A(N)$ の各元を固定し、その分数体 $N$ も固定する。$K(t)$ と $N$ が $N'$ を生成するので、$\operatorname{Gal}(N'/K(t))$ からの制限写像は単射である。よって $u'$ の惰性群は自明であり、惰性群による判定から $w'$ の分岐指数は $1$ となる。 [惰性群の議論](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionForward.lean#L26) · [Pi1 の惰性群の補題](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/BaseChange.lean#L425) · [惰性群による判定](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/FunctionFieldNormalizationInertia.lean#L123)

`etale_constantExtension` では、さらに $k(t)\subseteq F_1\subseteq F_2$ とし、$F_1'=K(t)(F_1)$ を仮定する。$A_i=A(F_i)$、$A_i'=A'(F_i')$ とする。$m_i$ と $m_i'$ はそれぞれ $A_i$ と $A_i'$ のイデアルに自然数を対応させる関数である。$i=1,2$ について、$A_i'$ の極大イデアル $q'$ の $A_i$ への縮約を $q$ とする。$q=0$ ならば $m_i'(q')=1$、$q\ne0$ ならば $m_i'(q')=m_i(q)$ と仮定する。$A_2$ の各極大イデアル $w$ とその $A_1$ への縮約 $v$ が $e(w/v)m_2(w)=m_1(v)$ を満たすならば、$A_2'$ の各極大イデアル $w'$ とその $A_1'$ への縮約 $v'$ について

$$
e(w'/v')\,m_2'(w')=m_1'(v')
$$

が成り立つ。ここで $e$ は対応する包含に関する分岐指数である。 [定数体拡大の定理](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionForward.lean#L102) · [Pi1 の定数体拡大の定理](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L148)

$w$ を $w'$ の $A_2$ への縮約とする。整性から $v'$ は極大である。環の包含がつくる四角形は可換なので、$v'$ と $w$ の $A_1$ への縮約は一致する。$w=0$ のとき、その縮約も零である。したがって、拡大後の二つの重複度と分岐指数はいずれも $1$ となる。$w\ne0$ のとき、$w$ は Dedekind 整域 $A_2$ の極大イデアルであり、整性からその $A_1$ への縮約 $v$ は零でない。$e(w'/v')=e(w/v)$ と二つの重複度の等式を用いると、拡大前の等式から拡大後の等式が従う。 [縮約を用いた証明](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionForward.lean#L133) · [分岐指数の等式](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L371)

MCP-CI レビュー `ci-022835-61a98993` は、`ramificationIdx_constantExtension_of_comap_bot` と `etale_constantExtension` の公理として `propext`、`Classical.choice`、`Quot.sound` だけを出力した。 [レビューのソース](../ReviewCanLiftCoverTransport.lean#L11) · [レビュー結果](../receipts/round-ci-022835-61a98993-result.json)
