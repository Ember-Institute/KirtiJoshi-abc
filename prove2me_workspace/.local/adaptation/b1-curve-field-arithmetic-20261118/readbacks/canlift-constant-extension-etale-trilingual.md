# Source_ReferenceIutCanLiftConstantExtensionEtale.lean

Upstream Pi1 revision `ca7def953193f861a462aa0831eec8f0a31ff69f`. Adapted source SHA-256 `5008e9f17794828ad7614d611deb36dc34028dbe0d0742fd715bbfe6c374caef`. MCP-CI leaf check `ci-022776-9b67f9ef` passed with exit code 0 and 23 warnings. [Source](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionEtale.lean#L2) · [Leaf check receipt](../receipts/round-ci-022776-9b67f9ef-result.json)

## English

Let $k\to K\to\Omega$ be a field tower. Assume $k$ is algebraically closed of characteristic zero, $\Omega$ is algebraically closed, and $t\in\Omega$ is transcendental over $K$. For a finite intermediate extension $F/k(t)$ in $\Omega$, set $F'=K(t)(F)$. Write $A(F)$ for the integral closure of $k[t]$ in $F$ and $A'(F')$ for the integral closure of $K[t]$ in $F'$. The theorem `exists_maximal_comap_constantExtension` gives, for every maximal ideal $w$ of $A(F)$, a maximal ideal $w'$ of $A'(F')$ whose contraction along `constantExtensionMap` is $w$. [Adapted lifting theorem](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionEtale.lean#L123) · [Pi1 lifting theorem](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/BaseChange.lean#L920)

To lift $w$, take a finite Galois extension $N/k(t)$ containing $F$ and its finite Galois compositum $N'=K(t)(N)$. Lift $w$ by integrality to a maximal ideal $u$ in $A(N)$. Its contraction $p$ to $k[t]$ is maximal. In the polynomial coordinates $k[t]\simeq k[X]$, a generator of $p$ has a root $c\in k$ because $k$ is algebraically closed. Maximality identifies $p$ with the kernel of evaluation at $c$. Evaluation at the image of $c$ in $K$ gives a maximal ideal of $K[t]$ contracting to $p$. Lift this ideal to a maximal ideal $u_1'$ of $A'(N')$. Its contraction to $A(N)$ lies over $p$, so Galois transitivity gives an automorphism of $N$ over $k(t)$ sending that contraction to $u$. Surjectivity of Galois restriction over algebraically closed $k$ lifts that automorphism to $N'$ over $K(t)$. Acting on $u_1'$ gives a maximal ideal contracting to $u$ by equivariance. Contract it to $A'(F')$ to obtain $w'$. [Evaluation on the line](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionEtale.lean#L28) · [Galois lifting](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionEtale.lean#L92) · [Surjectivity of restriction](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionGalois.lean#L261)

For `etale_of_constantExtension`, take $k(t)\subseteq F_1\subseteq F_2$ with $F_2/k(t)$ finite, and take $F_1'\subseteq F_2'$ over $K(t)$. The given inclusions $F_i\subseteq F_i'$ and $F_i'\subseteq K(t)(F_i)$ impose $F_i'=K(t)(F_i)$ inside $\Omega$ for $i=1,2$. Write $A_i=A(F_i)$ and $A_i'=A'(F_i')$. Let $m_i$ and $m_i'$ be natural-number-valued functions on the ideals of $A_i$ and $A_i'$ respectively. Assume $m_i'(q')=m_i(q)$ whenever $q'$ is maximal in $A_i'$ and its contraction $q$ to $A_i$ is nonzero. The hypothesis `C` requires the following identity for every maximal $w'$ in $A_2'$, with $v'$ its contraction to $A_1'$.

$$
e(w'/v')\,m_2'(w')=m_1'(v').
$$

It gives the following identity for every maximal $w$ in $A_2$, with $v$ its contraction to $A_1$.

$$
e(w/v)\,m_2(w)=m_1(v).
$$

[Adapted descent theorem](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionEtale.lean#L149) · [Pi1 descent theorem](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L182)

For such a $w$, use the lifting theorem to choose a maximal $w'$ contracting to it. The lemma `notFieldRing` and maximality give $w\ne0$. This allows the use of both the ramification-index equality $e(w'/v')=e(w/v)$ and the compatibility for $m_2$. The ideal $v'$ is maximal by integrality of $A_1'\to A_2'$. The ring inclusions form a commutative square, so $v'$ contracts to $v$ in $A_1$. A nonzero element of $w$ is integral over $A_1$, which gives $v\ne0$. This is the condition for the compatibility for $m_1$. Substituting the equalities for the index and the two multiplicities into the identity at $w'$ proves the identity at $w$. [Nonzero maximal ideal](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/FunctionFieldNormalization.lean#L107) · [Index equality](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L371) · [Descent proof](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionEtale.lean#L168)

## 中文

设 $k\to K\to\Omega$ 为域塔，其中 $k$ 是特征零代数闭域，$\Omega$ 是代数闭域，且 $t\in\Omega$ 在 $K$ 上超越。对 $\Omega$ 内的有限中间扩张 $F/k(t)$，令 $F'=K(t)(F)$。记 $A(F)$ 为 $k[t]$ 在 $F$ 中的整闭包，$A'(F')$ 为 $K[t]$ 在 $F'$ 中的整闭包。定理 `exists_maximal_comap_constantExtension` 对 $A(F)$ 的每个极大理想 $w$ 给出 $A'(F')$ 的极大理想 $w'$，使 $w'$ 沿 `constantExtensionMap` 收缩为 $w$。 [适配的提升定理](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionEtale.lean#L123) · [Pi1 提升定理](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/BaseChange.lean#L920)

取包含 $F$ 的有限 Galois 扩张 $N/k(t)$ 及其有限 Galois 合成域 $N'=K(t)(N)$。利用整扩张将 $w$ 提升为 $A(N)$ 的极大理想 $u$。$u$ 在 $k[t]$ 中的收缩 $p$ 也是极大理想。在多项式坐标 $k[t]\simeq k[X]$ 下，由 $k$ 的代数闭性，$p$ 的生成元有根 $c\in k$。由极大性，$p$ 是在 $c$ 处求值的核。在 $c$ 的 $K$ 中像处求值，得到一个收缩为 $p$ 的 $K[t]$ 极大理想。将该理想提升为 $A'(N')$ 的极大理想 $u_1'$。其在 $A(N)$ 中的收缩位于 $p$ 上方，因此 Galois 作用的传递性给出一个 $N$ 的 $k(t)$-自同构，将该收缩送到 $u$。由代数闭常数域 $k$ 上的 Galois 限制满射性，将此自同构提升到 $N'$ 上的 $K(t)$-自同构。将它作用于 $u_1'$，由等变性得到收缩为 $u$ 的极大理想。再收缩到 $A'(F')$，即得 $w'$。 [直线上的求值](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionEtale.lean#L28) · [Galois 提升](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionEtale.lean#L92) · [限制映射的满射性](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionGalois.lean#L261)

对于 `etale_of_constantExtension`，取 $k(t)\subseteq F_1\subseteq F_2$，其中 $F_2/k(t)$ 有限，并取 $K(t)$ 上的 $F_1'\subseteq F_2'$。给定的包含关系 $F_i\subseteq F_i'$ 和 $F_i'\subseteq K(t)(F_i)$ 要求对 $i=1,2$ 在 $\Omega$ 内有 $F_i'=K(t)(F_i)$。记 $A_i=A(F_i)$、$A_i'=A'(F_i')$。$m_i$、$m_i'$ 分别为 $A_i$、$A_i'$ 的理想上的自然数值函数。假设对每个 $A_i'$ 的极大理想 $q'$，若其在 $A_i$ 中的收缩 $q$ 非零，则 $m_i'(q')=m_i(q)$。假设 `C` 要求对 $A_2'$ 的每个极大理想 $w'$ 及其在 $A_1'$ 中的收缩 $v'$，下式都成立。

$$
e(w'/v')\,m_2'(w')=m_1'(v').
$$

定理给出对 $A_2$ 的每个极大理想 $w$，设 $v$ 为其在 $A_1$ 中的收缩，则有

$$
e(w/v)\,m_2(w)=m_1(v).
$$

[适配的下降定理](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionEtale.lean#L149) · [Pi1 下降定理](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L182)

给定这样的 $w$，由提升定理取收缩为 $w$ 的极大理想 $w'$。由引理 `notFieldRing` 和 $w$ 的极大性得到 $w\ne0$。因此可以应用分歧指数等式 $e(w'/v')=e(w/v)$ 以及 $m_2$ 的相容条件。由 $A_1'\to A_2'$ 的整性，$v'$ 是极大理想。各环的包含映射构成交换方块，所以 $v'$ 收缩到 $A_1$ 得 $v$。取 $w$ 中的非零元素，利用它在 $A_1$ 上的整性得到 $v\ne0$，从而可以应用 $m_1$ 的相容条件。将分歧指数和两项重数的等式代入 $w'$ 处的等式，即得 $w$ 处的等式。 [极大理想非零](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/FunctionFieldNormalization.lean#L107) · [分歧指数等式](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L371) · [下降证明](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionEtale.lean#L168)

## 日本語

$k\to K\to\Omega$ を体の塔とする。$k$ は標数零の代数閉体、$\Omega$ は代数閉体とし、$t\in\Omega$ は $K$ 上超越的とする。$\Omega$ 内の有限中間拡大 $F/k(t)$ に対し、$F'=K(t)(F)$ とする。$A(F)$ は $k[t]$ の $F$ における整閉包、$A'(F')$ は $K[t]$ の $F'$ における整閉包とする。定理 `exists_maximal_comap_constantExtension` は、$A(F)$ の任意の極大イデアル $w$ に対し、`constantExtensionMap` に沿う縮約が $w$ になる $A'(F')$ の極大イデアル $w'$ を与える。 [適応版の持ち上げ定理](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionEtale.lean#L123) · [Pi1 の持ち上げ定理](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/BaseChange.lean#L920)

$F$ を含む有限 Galois 拡大 $N/k(t)$ と、その合成体である有限 Galois 拡大 $N'/K(t)$ を取る。ここで $N'=K(t)(N)$ である。整拡大に沿って $w$ を $A(N)$ の極大イデアル $u$ に持ち上げる。$u$ の $k[t]$ への縮約 $p$ も極大である。多項式座標 $k[t]\simeq k[X]$ を使うと、$k$ の代数閉性により $p$ の生成元は根 $c\in k$ をもつ。極大性により、$p$ は $c$ での評価写像の核となる。$c$ の $K$ での像で評価すると、$p$ に縮約する $K[t]$ の極大イデアルを得る。そのイデアルを $A'(N')$ の極大イデアル $u_1'$ に持ち上げる。$u_1'$ の $A(N)$ への縮約は $p$ の上にあるため、Galois 作用の推移性により、その縮約を $u$ に移す $N$ の $k(t)$-自己同型が存在する。代数閉定数体 $k$ 上での制限写像の全射性により、この自己同型を $N'$ の $K(t)$-自己同型に持ち上げる。それを $u_1'$ に作用させると、縮約と作用の両立性により $u$ に縮約する極大イデアルを得る。そのイデアルを $A'(F')$ に縮約して $w'$ を得る。 [直線上での評価](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionEtale.lean#L28) · [Galois の持ち上げ](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionEtale.lean#L92) · [制限写像の全射性](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionGalois.lean#L261)

`etale_of_constantExtension` では、$k(t)\subseteq F_1\subseteq F_2$ と $K(t)$ 上の $F_1'\subseteq F_2'$ を取り、$F_2/k(t)$ を有限拡大とする。与えられた包含関係 $F_i\subseteq F_i'$ と $F_i'\subseteq K(t)(F_i)$ は、$i=1,2$ に対して $\Omega$ 内で $F_i'=K(t)(F_i)$ となる条件である。$A_i=A(F_i)$、$A_i'=A'(F_i')$ と書く。$m_i$ と $m_i'$ は、それぞれ $A_i$ と $A_i'$ のイデアルに自然数を対応させる関数である。$A_i'$ の極大イデアル $q'$ の $A_i$ への縮約 $q$ が零でないとき、$m_i'(q')=m_i(q)$ と仮定する。仮定 `C` は、$A_2'$ の各極大イデアル $w'$ とその $A_1'$ への縮約 $v'$ に対して次の等式を要求する。

$$
e(w'/v')\,m_2'(w')=m_1'(v').
$$

そして $A_2$ の各極大イデアル $w$ とその $A_1$ への縮約 $v$ に対し、次の等式を与える。

$$
e(w/v)\,m_2(w)=m_1(v).
$$

[適応版の降下定理](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionEtale.lean#L149) · [Pi1 の降下定理](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L182)

極大イデアル $w$ に対し、持ち上げ定理により $w$ に縮約する極大イデアル $w'$ を取る。補題 `notFieldRing` と $w$ の極大性により $w\ne0$ である。したがって、分岐指数の等式 $e(w'/v')=e(w/v)$ と $m_2$ の両立条件を使える。$A_1'\to A_2'$ の整性により、$v'$ は極大である。環の包含がつくる四角形が可換なので、$v'$ の $A_1$ への縮約は $v$ である。$w$ の零でない元が $A_1$ 上整であることから $v\ne0$ を得る。これにより $m_1$ の両立条件を使える。分岐指数と二つの重複度の等式を $w'$ での等式に代入すると、$w$ での等式が得られる。 [極大イデアルの非零性](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/FunctionFieldNormalization.lean#L107) · [分岐指数の等式](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L371) · [降下の証明](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionEtale.lean#L168)
