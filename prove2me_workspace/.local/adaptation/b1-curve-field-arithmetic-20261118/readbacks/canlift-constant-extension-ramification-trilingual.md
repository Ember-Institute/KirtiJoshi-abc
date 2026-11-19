# Source_ReferenceIutCanLiftConstantExtensionRamification.lean

Upstream Pi1 revision `ca7def953193f861a462aa0831eec8f0a31ff69f`. Adapted source SHA-256 `61aedcbc150fac8616ecff51e871e3a326feff1b470e6b8982254f6b4a9f5376`. MCP-CI leaf check `ci-022737-030eb4a9` and leaf build with Lean object output `ci-022744-965f1203` both exited with code 0 and 32 tactic-suggestion warnings each. [Source](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L2) · [Leaf check receipt](../receipts/round-ci-022737-030eb4a9-result.json) · [Leaf build receipt](../receipts/round-ci-022744-965f1203-result.json)

## English

Let $k\to K\to\Omega$ be a tower of fields, with $k$ of characteristic zero and $\Omega$ algebraically closed. Let $t\in\Omega$ be transcendental over $K$. Inside $\Omega$, take $k(t)\subseteq F_1\subseteq F_2$ with $F_2$ finite over $k(t)$. For $i=1,2$, let $F_i'=K(t)(F_i)$ be the compositum inside $\Omega$. In the Lean signature, the inclusions $F_i\subseteq F_i'$ and $F_i'\subseteq K(t)(F_i)$ express these compositum conditions, with $F_1'\subseteq F_2'$ supplied as an inclusion. Write $A_i$ for the integral closure of $k[t]$ in $F_i$ and $A_i'$ for the integral closure of $K[t]$ in $F_i'$. The map $A_i\to A_i'$ is `constantExtensionMap`. [Normalization map](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtension.lean#L67) · [Theorem signature](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L371)

Take a maximal ideal $w'$ in $A_2'$ whose contraction $w$ along $A_2\to A_2'$ is nonzero. For an ideal $P$ of $B$, write $e_{B/A}(P)$ for the ramification index of $P$ over its contraction to $A$ along the given ring inclusion. The theorem `ramificationIdx_constantExtension_eq` gives

$$
e_{A_2'/A_1'}(w')=e_{A_2/A_1}(w).
$$

[Adapted theorem](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L371) · [Pi1 nonzero-contraction branch](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/BaseChange.lean#L870)

A polynomial lemma identifies the bottom normalization rings with $k[X]$ and $K[X]$. The map between them sends each polynomial to its coefficientwise image. A generator of a nonzero prime of $k[X]$ is irreducible and therefore separable in characteristic zero. Its image is squarefree in $K[X]$. If a prime of $K[X]$ contracts to the given nonzero prime, the generator's image lies in the prime and outside its square. This gives the witness for comparing the indices over the two bottom rings. [Polynomial coordinates](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L44) · [Squarefree image](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L154) · [Pi1 polynomial lemma](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/BaseChange.lean#L241)

Choose a finite Galois extension $N/k(t)$ containing $F_2$ such that $N'=K(t)(N)$ is finite Galois over $K(t)$. Lift $w'$ to a maximal ideal $u'$ of the normalization ring in $N'$ and contract $u'$ to $u$ in the normalization ring in $N$. The contraction of $u$ to $A_2$ is $w$, so $u$ is a nonzero prime and hence maximal in the normalization ring, which is Dedekind. Over the bottom rings, the index at $u$ is at most the index at $u'$. To get this inequality, write the image of the lower prime generator as $gr$, where $g$ generates the prime below $u'$ in $K[X]$ and $r$ lies outside that prime. If $e$ is the lower index, the image of $gr$ lies in $(u')^e$. The image of $r$ lies outside $u'$, so the image of $g$ lies in $(u')^e$. Ideal factorization in the upper Dedekind domain gives the bound. The Galois inertia formula then gives $|I_u|\le |I_{u'}|$. Restriction injects $I_{u'}$ into $I_u$, so it identifies the two inertia groups. [Comparison of indices](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L78) · [Inertia groups](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L302) · [Choice of primes](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L383)

For $i=1,2$, the same restriction identifies $I_{u'}\cap\operatorname{Gal}(N'/F_i')$ with $I_u\cap\operatorname{Gal}(N/F_i)$. This uses the equivalence between fixing the compositum pointwise and fixing the lower field pointwise after restriction. The tower identity multiplies $e_{A_2/A_1}(w)$ by the order of the intersection for $F_2$ to obtain the order for $F_1$. The same identity holds over $K(t)$ with $w'$ and the two primed fields. The intersection orders agree, and the common factor for $i=2$ is positive, so cancellation gives the stated equality. [Intersections with fixing subgroups](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L315) · [Tower identity](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L345) · [Pi1 tower identity](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/SubfieldGalois.lean#L226)

## 中文

设 $k\to K\to\Omega$ 为域塔，其中 $k$ 为特征零，$\Omega$ 为代数闭域。取在 $K$ 上超越的 $t\in\Omega$。在 $\Omega$ 中取 $k(t)\subseteq F_1\subseteq F_2$，其中 $F_2/k(t)$ 有限。对 $i=1,2$，令 $F_i'=K(t)(F_i)$ 为 $\Omega$ 内的合成域。Lean 签名用 $F_i\subseteq F_i'$ 和 $F_i'\subseteq K(t)(F_i)$ 表达这一条件，并显式给出 $F_1'\subseteq F_2'$。记 $A_i$ 为 $k[t]$ 在 $F_i$ 中的整闭包，$A_i'$ 为 $K[t]$ 在 $F_i'$ 中的整闭包。映射 $A_i\to A_i'$ 是 `constantExtensionMap`。 [归一化环映射](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtension.lean#L67) · [定理签名](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L371)

取 $A_2'$ 的极大理想 $w'$，要求它沿 $A_2\to A_2'$ 的收缩 $w$ 非零。对 $B$ 中的理想 $P$，用 $e_{B/A}(P)$ 表示 $P$ 相对于其沿给定环嵌入收缩到 $A$ 的理想的分歧指数。定理 `ramificationIdx_constantExtension_eq` 给出

$$
e_{A_2'/A_1'}(w')=e_{A_2/A_1}(w).
$$

[适配定理](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L371) · [Pi1 中收缩非零的分支](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/BaseChange.lean#L870)

多项式引理把底域的归一化环分别识别为 $k[X]$ 和 $K[X]$。两者之间的映射逐项映射多项式系数。$k[X]$ 的非零素理想的生成元不可约，在特征零下因而可分。它在 $K[X]$ 中的像无平方因子。若 $K[X]$ 的一个素理想收缩为给定的非零素理想，则该生成元的像属于上方素理想，且在其平方之外。这个元素用于比较两个底环上的分歧指数。 [多项式坐标](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L44) · [像无平方因子](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L154) · [Pi1 多项式引理](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/BaseChange.lean#L241)

取包含 $F_2$ 的有限 Galois 扩张 $N/k(t)$，使 $N'=K(t)(N)$ 在 $K(t)$ 上有限 Galois。把 $w'$ 提升为 $N'$ 的归一化环中的极大理想 $u'$，再将 $u'$ 收缩为 $N$ 的归一化环中的理想 $u$。$u$ 在 $A_2$ 上的收缩是 $w$，所以 $u$ 是 Dedekind 归一化环中的非零素理想，因而为极大理想。相对于各自底环，$u$ 处的分歧指数不超过 $u'$ 处的分歧指数。为得出此不等式，把下方素理想的生成元的像写成 $gr$，其中 $g$ 生成 $u'$ 收缩到 $K[X]$ 的素理想，$r$ 在该素理想之外。若下方分歧指数为 $e$，则 $gr$ 的像属于 $(u')^e$。$r$ 的像不属于 $u'$，所以 $g$ 的像属于 $(u')^e$。上方 Dedekind 整环中的理想分解给出所需的界。Galois 扩张的惯性群阶公式随即给出 $|I_u|\le |I_{u'}|$。限制映射把 $I_{u'}$ 单射到 $I_u$，于是它给出两个惯性群的同构。 [分歧指数比较](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L78) · [惯性群](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L302) · [选取理想](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L383)

对 $i=1,2$，同一限制映射还把 $I_{u'}\cap\operatorname{Gal}(N'/F_i')$ 与 $I_u\cap\operatorname{Gal}(N/F_i)$ 对应起来。这里用到逐点固定合成域当且仅当限制后逐点固定下方域。塔公式将 $e_{A_2/A_1}(w)$ 乘以 $F_2$ 对应的交子群的阶，得到 $F_1$ 对应的交子群的阶。对 $K(t)$ 上的 $w'$ 和两个带撇的域，同一公式成立。两边的交子群阶分别相等，且 $i=2$ 对应的共同因子为正，约去后得到所述等式。 [与逐点固定子群的交](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L315) · [塔公式](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L345) · [Pi1 塔公式](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/SubfieldGalois.lean#L226)

## 日本語

$k\to K\to\Omega$ を体の塔とし、$k$ の標数を零、$\Omega$ を代数閉体とする。$K$ 上超越的な $t\in\Omega$ を取る。$\Omega$ の中で $k(t)\subseteq F_1\subseteq F_2$ とし、$F_2/k(t)$ は有限拡大とする。$i=1,2$ に対し、$F_i'=K(t)(F_i)$ を $\Omega$ 内の合成体とする。Lean の定理の型では、$F_i\subseteq F_i'$ と $F_i'\subseteq K(t)(F_i)$ が合成体の条件を表し、包含関係 $F_1'\subseteq F_2'$ も明示的に与える。$A_i$ を $k[t]$ の $F_i$ における整閉包、$A_i'$ を $K[t]$ の $F_i'$ における整閉包とする。写像 $A_i\to A_i'$ は `constantExtensionMap` である。 [正規化環の写像](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtension.lean#L67) · [定理の型](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L371)

$A_2'$ の極大イデアル $w'$ を取り、$A_2\to A_2'$ に沿ったその縮約 $w$ が零でないとする。$B$ のイデアル $P$ に対し、与えられた環の包含に沿って $P$ を $A$ に縮約したイデアルの上の分岐指数を $e_{B/A}(P)$ と書く。定理 `ramificationIdx_constantExtension_eq` は次の等式を与える。

$$
e_{A_2'/A_1'}(w')=e_{A_2/A_1}(w).
$$

[適応版の定理](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L371) · [Pi1 で縮約が零でない場合](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/BaseChange.lean#L870)

多項式の補題は、基礎体の正規化環をそれぞれ $k[X]$ と $K[X]$ と同一視する。二つの環の間の写像は、多項式の各係数を移す。$k[X]$ の零でない素イデアルの生成元は既約であり、標数零なので分離的である。その $K[X]$ での像は平方因子をもたない。$K[X]$ の素イデアルを縮約してこの零でない素イデアルが得られる場合、生成元の像は上の素イデアルに属し、その二乗には属さない。この元を用いて二つの基礎環の上の分岐指数を比較する。 [多項式座標](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L44) · [像の平方因子](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L154) · [Pi1 の多項式の補題](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/BaseChange.lean#L241)

$F_2$ を含む有限 Galois 拡大 $N/k(t)$ で、$N'=K(t)(N)$ が $K(t)$ 上の有限 Galois 拡大となるものを取る。$w'$ を $N'$ の正規化環の極大イデアル $u'$ に持ち上げ、$u'$ を $N$ の正規化環のイデアル $u$ に縮約する。$u$ の $A_2$ への縮約が $w$ なので、$u$ は Dedekind 整域である正規化環の零でない素イデアルであり、したがって極大である。それぞれの基礎環の上で、$u$ の分岐指数は $u'$ の分岐指数以下である。この不等式を得るため、下の素イデアルの生成元の像を $gr$ と書く。ここで $g$ は $u'$ の下にある $K[X]$ の素イデアルを生成し、$r$ はその素イデアルに属さない。下の分岐指数を $e$ とすると、$gr$ の像は $(u')^e$ に属する。$r$ の像は $u'$ に属さないため、$g$ の像は $(u')^e$ に属する。上の Dedekind 整域でのイデアル分解から不等式が従う。Galois 拡大での惰性群の位数の公式により、$|I_u|\le |I_{u'}|$ が成り立つ。制限写像は $I_{u'}$ から $I_u$ への単射なので、二つの惰性群の同型を与える。 [分岐指数の比較](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L78) · [惰性群](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L302) · [イデアルの選択](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L383)

$i=1,2$ に対して、同じ制限写像は $I_{u'}\cap\operatorname{Gal}(N'/F_i')$ と $I_u\cap\operatorname{Gal}(N/F_i)$ を同一視する。ここでは、合成体の各元を固定することと、制限が下の体の各元を固定することの同値性を使う。拡大の塔の公式により、$e_{A_2/A_1}(w)$ に $F_2$ に対応する共通部分の位数を掛けると、$F_1$ に対応する共通部分の位数になる。$K(t)$ 上でも、$w'$ と二つのプライム付きの体について同じ公式が成り立つ。共通部分の位数はそれぞれ一致し、$i=2$ に対応する共通因子は正なので、これを消去すると所定の等式が得られる。 [各元を固定する部分群との共通部分](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L315) · [拡大の塔の公式](../../../../Solutions/Source_ReferenceIutCanLiftConstantExtensionRamification.lean#L345) · [Pi1 の拡大の塔の公式](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/SubfieldGalois.lean#L226)
