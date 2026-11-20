# M2 射影作用与边界映射 · M2 projective actions and boundary maps · M2 の射影作用と境界写像

## 中文

### 射影直线上的交比

设 $k$ 为域，写 $\mathbb P^1(k)=k\cup\{\infty\}$。有限点 $t$ 的齐次代表元 $\widehat t$ 为 $(t,1)$，无穷远点的代表元为 $(1,0)$。用 $[u,v]$ 表示以两个向量为列的行列式。`wcr` 定义四点的交比

$$
w(y_1,y_2,y_3,y_4)=
\frac{[\widehat y_1,\widehat y_3][\widehat y_2,\widehat y_4]}
     {[\widehat y_1,\widehat y_4][\widehat y_2,\widehat y_3]}.
$$

分母为零时，Lean 的域除法取值为零。四点两两相异时，交比既非零也非一，在 $\mathrm{GL}_2(k)$ 的同时作用下不变，交换前两点或后两点会将其取逆。若 $k$ 非平凡赋范、闭球紧致，且采用 Borel 可测结构，则齐次代表元映射与全体四点组上的交比均可测。

`finite_of_two_refs` 给定射影点 $p,q,p',q'$，假设 $p$ 分别异于 $q,p',q'$，并给定 $c\ne0$、$c'\ne1$。满足下述条件的 $y$ 只有有限个。存在 $y'$，使得 $(y,y',p,q)$ 与 $(y,y',p',q')$ 各自四点两两相异，且交比分别为 $c$ 和 $c'$。证明用线性映射 $v\mapsto[v,\widehat p]\widehat q-c[v,\widehat q]\widehat p$ 及第二对参考点的相应映射。若同一个 $y'$ 满足两式，则这两个映射在 $\widehat y$ 处的值都与 $\widehat y'$ 的行列式为零。因此两值的行列式也为零。它关于 $\widehat y$ 是二次齐次式，在 $\widehat p$ 处非零，故射影零点集有限。

### 等变的单点映射

令 $B=\mathbb P^1(\mathbb R)$，边界测度 $\mu$ 是沿 $\mathbb R\hookrightarrow B$ 推前的 Lebesgue 测度。实矩阵通过 Möbius 变换作用于 $B$。设 $\Gamma\le\mathrm{SL}_2(\mathbb R)$，$k$ 是非平凡赋范且闭球紧致的域，$a\colon\mathrm{SL}_2(\mathbb R)\to\mathrm{GL}_2(k)$。`ActsOn` 要求对所有 $g,h\in\Gamma$ 和 $y\in\mathbb P^1(k)$，有 $a(gh)y=a(g)(a(h)y)$。`NonElem` 要求对每个有限指数子群 $\Gamma'\le\Gamma$ 和每个 $y\in\mathbb P^1(k)$，存在 $\gamma\in\Gamma'$ 使 $a(\gamma)y\ne y$。`Equivariant` 要求对每个 $\gamma\in\Gamma$，等式 $\psi(\gamma x)=a(\gamma)\psi(x)$ 对 $\mu$ 几乎处处的 $x$ 成立。

若 $\Gamma$ 可数且双遍历、`NonElem` 成立，并且 $\psi\colon B\to\mathbb P^1(k)$ 可测且满足 `Equivariant`，则 `ae_ne_of_equivariant` 给出 $\psi(x_1)\ne\psi(x_2)$ 对 $\mu\otimes\mu$ 几乎处处的 $(x_1,x_2)$ 成立。`IsDoublyErgodic` 要求在对角作用下不变的可测集为零测或余零测。可数性让这一结论适用于几乎处处不变的相等集。若它余零测，Fubini 定理给出 $\psi$ 的几乎处处常值。边界作用保持零测集，等变性便使这个值成为 $\Gamma$ 的公共不动点，与 `NonElem` 矛盾。

### 无序点对

仍令 $\Gamma$ 可数且双遍历，假设 `ActsOn` 和 `NonElem` 成立。采用上述赋范域及其 Borel 可测结构。`noPair` 断言不存在可测的 $u,v\colon B\to\mathbb P^1(k)$ 满足以下条件。对 $\mu$ 几乎处处的 $x$ 有 $u(x)\ne v(x)$。令 $S_x=\{u(x),v(x)\}$，对每个 $\gamma\in\Gamma$，$S_{\gamma x}=a(\gamma)S_x$ 对 $\mu$ 几乎处处的 $x$ 成立。双遍历性使 $S_{x_1}$ 与 $S_{x_2}$ 在 $\mu\otimes\mu$ 下或者几乎处处相交，或者几乎处处不交。

- **几乎处处相交。** `noPair_meet` 使用可数性、`ActsOn`、`NonElem`、两个分量的可测性、点对等变性和几乎处处相交这一假设。用与 $\mu$ 具有相同零测集的有限 Cauchy 测度 $\nu$，令 $w_y=\nu\{x:y\in S_x\}$。对任何有限点集，权重和至多为 $2\nu(B)$。因此权重至少为 $\nu(B)/2$ 的点只有有限个。Fubini 定理表明几乎每个 $S_x$ 都含有其中一个点。`NoPair` 直接用 `PointMaps` 的 `ae_smul` 和无序点对的等变性把这一性质传给该有限点集的每个群平移。可数性给出一个点对同时与所有这些平移相交。`ActsOn.one` 和 `ActsOn.inv` 用来构造点稳定子。这些稳定子的有限个左陪集覆盖 $\Gamma$，B. H. Neumann 引理便给出有限指数稳定子，与 `NonElem` 矛盾。
- **几乎处处不交。** `noPair_disjoint` 使用可数性、双遍历性、两个分量可测且几乎处处不同、点对等变性及几乎处处不交这一假设。`NoPair` 直接用 `CrossRatio` 的 `measurable_wcr`、`wcr_smul` 与两条交换公式。于是对两个无交点对计算的 $w+w^{-1}$ 是不依赖各点对内部次序的可测不变量，双遍历性使它几乎处处等于某个 $c+c^{-1}$，其中 $c\notin\{0,1\}$。Fubini 定理给出两个互不相交的参考点对，使得几乎每个 $S_x$ 对任一参考点对的交比都在 $\{c,c^{-1}\}$ 中。`noPair_disjoint` 对至多四种交比组合分别调用 `finite_of_two_refs`，使 $u(x)$ 几乎处处落在一个有限点集中。于是 $u$ 的一条纤维具有正测度。该纤维中任意两点所对应的点对都相交，与几乎处处不交矛盾。

### Fricke 正规形的复射影作用

设 $x,y,z\in\mathbb R$，$z>0$ 且 $x^2+y^2+z^2=xyz$。令 $A_0,B_0$ 为相应的 Fricke 正规形生成元，$\Gamma_0=\langle A_0,B_0\rangle$。交换子 $K=A_0B_0A_0^{-1}B_0^{-1}$ 属于 $\Gamma_0$，其矩阵为 $\left(\begin{smallmatrix}-1&-2\\0&-1\end{smallmatrix}\right)$。对域 $k$ 和保幺环同态 $\sigma\colon\mathbb R\to k$，`slMap` 逐项应用 $\sigma$，给出从 $\mathrm{SL}_2(\mathbb R)$ 到 $\mathrm{GL}_2(k)$ 的群同态。`slMap_commK` 在 $\mathbb P^1(k)$ 上给出 $K$ 的像的作用，即有限点平移 $2$ 而 $\infty$ 固定。$K^n$ 的像在有限点上平移 $2n$。

对每个保幺环同态 $\sigma\colon\mathbb R\to\mathbb C$，`unbounded_complex` 给出 $\Gamma_0$ 中的序列 $\gamma_n$，使得 $(0,1,\infty)$ 在 $\operatorname{slMap}(\sigma)(\gamma_n)$ 下的像收敛到坐标有重复的三元组。证明取 $\gamma_n=K^n$，相应的像为 $(2n,1+2n,\infty)$，在射影直线的乘积拓扑中趋于 $(\infty,\infty,\infty)$。`NonElementary` 另外复用 `slMap_mul` 和 `slMap_commK` 在 $x\ne0$ 时证明正规形作用的非初等性，其验收单独记录。可公度子作用的连续延拓属于后续超刚性步骤。

## English

### Cross ratio on the projective line

Let $k$ be a field, and write $\mathbb P^1(k)=k\cup\{\infty\}$. The homogeneous representative $\widehat t$ of a finite point $t$ is $(t,1)$. The representative of infinity is $(1,0)$. Write $[u,v]$ for the determinant with column vectors $u$ and $v$. The definition `wcr` gives the cross ratio

$$
w(y_1,y_2,y_3,y_4)=
\frac{[\widehat y_1,\widehat y_3][\widehat y_2,\widehat y_4]}
     {[\widehat y_1,\widehat y_4][\widehat y_2,\widehat y_3]}.
$$

Lean field division gives zero when the denominator is zero. For four pairwise distinct points, the cross ratio is different from $0$ and $1$. It is invariant under the simultaneous action of $\mathrm{GL}_2(k)$. Swapping either the first two or the last two points inverts it. Suppose $k$ has a nontrivial norm, compact closed balls, and its Borel measurable structure. Then the representative map and the cross ratio on all quadruples are measurable.

For `finite_of_two_refs`, take projective points $p,q,p',q'$ with $p\ne q$, $p\ne p'$, and $p\ne q'$. Take $c\ne0$ and $c'\ne1$. Only finitely many $y$ admit a $y'$ with the following properties. Each of $(y,y',p,q)$ and $(y,y',p',q')$ has four pairwise distinct points. Their cross ratios are $c$ and $c'$, respectively. The proof uses the linear map $v\mapsto[v,\widehat p]\widehat q-c[v,\widehat q]\widehat p$ and the corresponding map for the second reference pair. For a common $y'$, the determinant of each output at $\widehat y$ with $\widehat y'$ vanishes. The determinant between the outputs also vanishes. It is a homogeneous quadratic in $\widehat y$ that is nonzero at $\widehat p$. Its projective zero set is finite.

### Equivariant point maps

Let $B=\mathbb P^1(\mathbb R)$, with boundary measure $\mu$ given by the pushforward of Lebesgue measure along $\mathbb R\hookrightarrow B$. Real special linear matrices act on $B$ by Möbius transformations. Let $\Gamma\le\mathrm{SL}_2(\mathbb R)$, and let $k$ be a nontrivially normed field with compact closed balls. Take $a\colon\mathrm{SL}_2(\mathbb R)\to\mathrm{GL}_2(k)$. The condition `ActsOn` requires $a(gh)y=a(g)(a(h)y)$ for all $g,h\in\Gamma$ and $y\in\mathbb P^1(k)$. The condition `NonElem` concerns every finite-index subgroup $\Gamma'\le\Gamma$ and every $y\in\mathbb P^1(k)$. It requires a $\gamma\in\Gamma'$ with $a(\gamma)y\ne y$. The condition `Equivariant` requires that for each $\gamma\in\Gamma$, $\psi(\gamma x)=a(\gamma)\psi(x)$ for $\mu$-almost every $x$.

Suppose $\Gamma$ is countable and doubly ergodic, `NonElem` holds, and $\psi\colon B\to\mathbb P^1(k)$ is measurable and satisfies `Equivariant`. Then `ae_ne_of_equivariant` gives $\psi(x_1)\ne\psi(x_2)$ for $\mu\otimes\mu$-almost every $(x_1,x_2)$. The equality set is measurable and almost everywhere invariant under the diagonal action. The predicate `IsDoublyErgodic` makes invariant measurable sets null or conull. Countability extends this conclusion to the almost everywhere invariant equality set. In the conull case, Fubini's theorem gives an almost everywhere constant value of $\psi$. The boundary action preserves null sets, so equivariance makes that value a common fixed point of $\Gamma$. This contradicts `NonElem`.

### Unordered pairs

Let $\Gamma$ be countable and doubly ergodic. Assume `ActsOn` and `NonElem`, and use the same hypotheses on $k$ with its Borel measurable structure. The theorem `noPair` rules out measurable maps $u,v\colon B\to\mathbb P^1(k)$ that satisfy both conditions below. First, $u(x)\ne v(x)$ for $\mu$-almost every $x$. Second, set $S_x=\{u(x),v(x)\}$. For each $\gamma\in\Gamma$, $S_{\gamma x}=a(\gamma)S_x$ for $\mu$-almost every $x$. Under $\mu\otimes\mu$, double ergodicity makes $S_{x_1}$ and $S_{x_2}$ meet almost everywhere or be disjoint almost everywhere.

- **Almost everywhere meeting.** The theorem `noPair_meet` uses countability, `ActsOn`, `NonElem`, measurability of both components, pair equivariance, and the almost everywhere meeting hypothesis. Use the finite Cauchy measure $\nu$, which has the same null sets as $\mu$. Set $w_y=\nu\{x:y\in S_x\}$. Over any finite set of points, the sum of the weights is at most $2\nu(B)$. Thus the points with weights at least $\nu(B)/2$ form a finite set. Fubini's theorem shows that almost every $S_x$ contains a point from this set. The proof in `NoPair` calls `ae_smul` from `PointMaps`. Pair equivariance then shows that almost every $S_x$ meets each translate of this finite set. Countability gives a single pair that meets all these translates. The proof uses `ActsOn.one` and `ActsOn.inv` to form point stabilizers. Finitely many left cosets of these stabilizers cover $\Gamma$. B. H. Neumann's lemma gives a finite-index stabilizer, contrary to `NonElem`.
- **Almost everywhere disjoint.** The theorem `noPair_disjoint` uses countability, double ergodicity, measurable components distinct almost everywhere, pair equivariance, and the almost everywhere disjointness hypothesis. The proof in `NoPair` uses `measurable_wcr`, `wcr_smul`, and the two swap formulas from `CrossRatio`. Thus $w+w^{-1}$ is measurable and invariant, independent of the order inside each pair. Double ergodicity makes it almost everywhere equal to some $c+c^{-1}$ with $c\notin\{0,1\}$. Fubini's theorem gives two disjoint reference pairs for which almost every $S_x$ has both cross ratios in $\{c,c^{-1}\}$. The proof calls `finite_of_two_refs` for each combination. Hence $u(x)$ lies in a finite set almost everywhere. One fiber of $u$ then has positive measure. The pairs associated to any two points of that fiber meet, contrary to almost everywhere disjointness.

### Complex projective action of the Fricke normal form

Take $x,y,z\in\mathbb R$ with $z>0$ and $x^2+y^2+z^2=xyz$. Let $A_0,B_0$ be the associated Fricke normal form generators and let $\Gamma_0=\langle A_0,B_0\rangle$. The commutator $K=A_0B_0A_0^{-1}B_0^{-1}$ belongs to $\Gamma_0$ and has matrix $\left(\begin{smallmatrix}-1&-2\\0&-1\end{smallmatrix}\right)$. For a field $k$ and a unital ring homomorphism $\sigma\colon\mathbb R\to k$, `slMap` applies $\sigma$ entry by entry. It is a group homomorphism from $\mathrm{SL}_2(\mathbb R)$ to $\mathrm{GL}_2(k)$. The lemma `slMap_commK` says that the image of $K$ translates finite points by $2$ and fixes $\infty$. The image of $K^n$ translates finite points by $2n$.

For each unital ring homomorphism $\sigma\colon\mathbb R\to\mathbb C$, `unbounded_complex` gives a sequence $\gamma_n$ in $\Gamma_0$. The images of $(0,1,\infty)$ under $\operatorname{slMap}(\sigma)(\gamma_n)$ converge to a triple with a repeated coordinate. The proof takes $\gamma_n=K^n$. The images are $(2n,1+2n,\infty)$ and converge to $(\infty,\infty,\infty)$ in the product topology of the projective line. The module `NonElementary` uses `slMap_mul` and `slMap_commK` to prove non-elementarity of the normal form action when $x\ne0$. The acceptance record for `NonElementary` is separate. The continuous extension of the commensurator action belongs to the subsequent superrigidity step.

## 日本語

### 射影直線上の複比

体 $k$ に対し、$\mathbb P^1(k)=k\cup\{\infty\}$ と書く。有限点 $t$ の同次代表元 $\widehat t$ は $(t,1)$ で、無限遠点の代表元は $(1,0)$ である。二つのベクトルを列とする行列式を $[u,v]$ と書く。`wcr` は四点の複比

$$
w(y_1,y_2,y_3,y_4)=
\frac{[\widehat y_1,\widehat y_3][\widehat y_2,\widehat y_4]}
     {[\widehat y_1,\widehat y_4][\widehat y_2,\widehat y_3]}
$$

を定める。分母が零の場合、Lean の体の除法は零を返す。四点が互いに異なれば、複比は $0$ とも $1$ とも異なり、$\mathrm{GL}_2(k)$ を四点に同時に作用させても変わらない。最初の二点または最後の二点を入れ替えると、複比は逆数になる。$k$ が非自明なノルムをもち、閉球がコンパクトで、Borel 可測構造を入れる場合、同次代表元の写像と四点組全体での複比は可測である。

`finite_of_two_refs` では、射影点 $p,q,p',q'$ が $p\ne q$、$p\ne p'$、$p\ne q'$ を満たし、$c\ne0$、$c'\ne1$ とする。$(y,y',p,q)$ と $(y,y',p',q')$ の各四点が互いに異なり、複比がそれぞれ $c,c'$ となるような $y'$ をもつ $y$ は有限個である。証明では線形写像 $v\mapsto[v,\widehat p]\widehat q-c[v,\widehat q]\widehat p$ と、もう一方の基準点対に対応する写像を用いる。共通の $y'$ があれば、$\widehat y$ における両方の値は $\widehat y'$ との行列式が零になる。したがって値どうしの行列式も零になる。この行列式は $\widehat y$ の同次二次式で、$\widehat p$ では零でない。その射影零点集合は有限である。

### 同変な点値写像

$B=\mathbb P^1(\mathbb R)$ とし、境界測度 $\mu$ を Lebesgue 測度の $\mathbb R\hookrightarrow B$ による押し出しとする。行列式が一の実行列は Möbius 変換で $B$ に作用する。$\Gamma\le\mathrm{SL}_2(\mathbb R)$ とし、$k$ は非自明なノルムをもち閉球がコンパクトな体とする。$a\colon\mathrm{SL}_2(\mathbb R)\to\mathrm{GL}_2(k)$ を与える。`ActsOn` は、すべての $g,h\in\Gamma$ と $y\in\mathbb P^1(k)$ について $a(gh)y=a(g)(a(h)y)$ を要求する。`NonElem` は、有限指数の部分群 $\Gamma'\le\Gamma$ と点 $y\in\mathbb P^1(k)$ を任意に取ると、$a(\gamma)y\ne y$ となる $\gamma\in\Gamma'$ が存在することを要求する。`Equivariant` は、各 $\gamma\in\Gamma$ について、$\mu$ に関してほとんどすべての $x$ で $\psi(\gamma x)=a(\gamma)\psi(x)$ が成り立つことを要求する。

$\Gamma$ が可算かつ二重エルゴード的であり、`NonElem` が成り立ち、$\psi\colon B\to\mathbb P^1(k)$ が可測で `Equivariant` を満たすとする。`ae_ne_of_equivariant` により、$\mu\otimes\mu$ に関してほとんどすべての $(x_1,x_2)$ で $\psi(x_1)\ne\psi(x_2)$ が成り立つ。両方の値が等しい組の集合は可測で、対角作用の下で零集合を除いて不変である。`IsDoublyErgodic` は、対角作用の下で不変な可測集合またはその補集合が零集合であることを要求する。可算性により、この結論は零集合を除いて不変な上の集合にも適用できる。補集合が零集合なら、Fubini の定理から $\psi$ はほとんど至る所で一定となる。境界作用は零集合を保つので、同変性によりその値が $\Gamma$ の共通固定点となり、`NonElem` に反する。

### 順序を付けない点対

$\Gamma$ を可算かつ二重エルゴード的とし、`ActsOn` と `NonElem` が成り立つとする。$k$ には上と同じ仮定と Borel 可測構造を用いる。`noPair` は、次の二条件を満たす可測写像 $u,v\colon B\to\mathbb P^1(k)$ が存在しないことを示す。第一に、$\mu$ に関してほとんどすべての $x$ で $u(x)\ne v(x)$ である。第二に、$S_x=\{u(x),v(x)\}$ とすると、各 $\gamma\in\Gamma$ について、$\mu$ に関してほとんどすべての $x$ で $S_{\gamma x}=a(\gamma)S_x$ が成り立つ。二重エルゴード性により、$\mu\otimes\mu$ に関して、$S_{x_1}$ と $S_{x_2}$ はほとんど至る所で交わるか、ほとんど至る所で互いに素である。

- **ほとんど至る所で交わる場合。** `noPair_meet` は可算性、`ActsOn`、`NonElem`、両成分の可測性、点対の同変性、ほとんど至る所で交わるという仮定を用いる。$\mu$ と同じ零集合をもつ有限 Cauchy 測度 $\nu$ を用い、$w_y=\nu\{x:y\in S_x\}$ とおく。任意の有限点集合について重みの和は $2\nu(B)$ 以下である。したがって重みが $\nu(B)/2$ 以上の点は有限個である。Fubini の定理により、ほとんどすべての $S_x$ はそのうちの一点を含む。`NoPair` は `PointMaps` の `ae_smul` と点対の同変性を使い、その有限点集合を群の各元で移した集合にもほとんどすべての $S_x$ が交わることを示す。可算性により、それらすべてに交わる一つの点対が取れる。`ActsOn.one` と `ActsOn.inv` を使って点の固定部分群を作る。これらの固定部分群の有限個の左剰余類が $\Gamma$ を覆うので、B. H. Neumann の補題から有限指数の固定部分群が得られ、`NonElem` に反する。
- **ほとんど至る所で互いに素な場合。** `noPair_disjoint` は可算性、二重エルゴード性、両成分が可測かつほとんど至る所で異なること、点対の同変性、ほとんど至る所で互いに素という仮定を用いる。`NoPair` は `CrossRatio` の `measurable_wcr`、`wcr_smul` と二つの入れ替え公式を使う。したがって $w+w^{-1}$ は、各点対の内部の順序に依存しない可測な不変量となる。二重エルゴード性により、これはほとんど至る所である $c+c^{-1}$ に等しく、$c\notin\{0,1\}$ である。Fubini の定理により互いに素な二つの基準点対が取れ、ほとんどすべての $S_x$ はどちらの基準点対とも $\{c,c^{-1}\}$ に属する複比をもつ。`noPair_disjoint` は各組合せに `finite_of_two_refs` を適用する。すると $u(x)$ はほとんど至る所で有限点集合に属する。したがって $u$ のファイバーの一つは正の測度をもち、その中の任意の二点に対応する点対は交わる。これはほとんど至る所で互いに素であることに反する。

### Fricke 標準形の複素射影作用

$x,y,z\in\mathbb R$ が $z>0$ と $x^2+y^2+z^2=xyz$ を満たすとする。対応する Fricke 標準形の生成元を $A_0,B_0$ とし、$\Gamma_0=\langle A_0,B_0\rangle$ とおく。交換子 $K=A_0B_0A_0^{-1}B_0^{-1}$ は $\Gamma_0$ に属し、その行列は $\left(\begin{smallmatrix}-1&-2\\0&-1\end{smallmatrix}\right)$ である。体 $k$ と単位元を保つ環準同型 $\sigma\colon\mathbb R\to k$ に対し、`slMap` は各成分に $\sigma$ を適用する。これは $\mathrm{SL}_2(\mathbb R)$ から $\mathrm{GL}_2(k)$ への群準同型である。`slMap_commK` によると、$K$ の像は有限点を $2$ だけ平行移動し、$\infty$ を固定する。$K^n$ の像は有限点を $2n$ だけ平行移動する。

任意の単位元を保つ環準同型 $\sigma\colon\mathbb R\to\mathbb C$ に対し、`unbounded_complex` は $\Gamma_0$ 内の列 $\gamma_n$ を与える。$\operatorname{slMap}(\sigma)(\gamma_n)$ による $(0,1,\infty)$ の像は、重複する座標をもつ三点組に収束する。証明では $\gamma_n=K^n$ と取る。像は $(2n,1+2n,\infty)$ であり、射影直線の積位相で $(\infty,\infty,\infty)$ に収束する。`NonElementary` は `slMap_mul` と `slMap_commK` を $x\ne0$ のときの標準形の作用の非初等性の証明に使う。その検証結果は別途記録する。可公度化群の作用の連続延長は後続の超剛性の段階に属する。

## Sources

| Declaration or use | Pinned source | Local source |
| --- | --- | --- |
| Homogeneous coordinates and the boundary measure | [lift and br](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/ForMathlib/ProjectiveLine.lean#L72) · [bdry](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Setup.lean#L38) · [IsDoublyErgodic](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Setup.lean#L48) | [lift and br](../../../../Solutions/Source_ReferenceIutCanLiftProjectiveLine.lean#L78) · [bdry](../../../../Solutions/Source_ReferenceIutCanLiftM2Setup.lean#L46) · [IsDoublyErgodic](../../../../Solutions/Source_ReferenceIutCanLiftM2Setup.lean#L56) |
| Cross ratio, invariance, and measurability | [wcr](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/CrossRatio.lean#L31) · [wcr_smul](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/CrossRatio.lean#L95) · [measurable_wcr](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/CrossRatio.lean#L234) | [wcr](../../../../Solutions/Source_ReferenceIutCanLiftCrossRatio.lean#L37) · [wcr_smul](../../../../Solutions/Source_ReferenceIutCanLiftCrossRatio.lean#L101) · [measurable_wcr](../../../../Solutions/Source_ReferenceIutCanLiftCrossRatio.lean#L240) |
| Finiteness with two reference pairs | [finite_of_two_refs](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/CrossRatio.lean#L178) | [finite_of_two_refs](../../../../Solutions/Source_ReferenceIutCanLiftCrossRatio.lean#L184) |
| Projective action and equivariant point maps | [Equivariant, ActsOn, and NonElem](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/PointMaps.lean#L28) · [ae_ne_of_equivariant](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/PointMaps.lean#L82) | [Equivariant, ActsOn, and NonElem](../../../../Solutions/Source_ReferenceIutCanLiftPointMaps.lean#L34) · [ae_ne_of_equivariant](../../../../Solutions/Source_ReferenceIutCanLiftPointMaps.lean#L88) |
| Cross ratio results in the disjoint case | [measurability of the invariant](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/NoPair.lean#L274) · [jcr_congr](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/NoPair.lean#L235) · [finite_of_two_refs call](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/NoPair.lean#L316) | [measurability of the invariant](../../../../Solutions/Source_ReferenceIutCanLiftNoPair.lean#L281) · [jcr_congr](../../../../Solutions/Source_ReferenceIutCanLiftNoPair.lean#L242) · [finite_of_two_refs call](../../../../Solutions/Source_ReferenceIutCanLiftNoPair.lean#L323) |
| Point map results in the meeting case | [stab](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/NoPair.lean#L33) · [ae_smul call](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/NoPair.lean#L165) | [stab](../../../../Solutions/Source_ReferenceIutCanLiftNoPair.lean#L40) · [ae_smul call](../../../../Solutions/Source_ReferenceIutCanLiftNoPair.lean#L172) |
| Contradiction for unordered point pairs | [noPair_meet](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/NoPair.lean#L114) · [noPair_disjoint](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/NoPair.lean#L263) · [noPair](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/NoPair.lean#L350) | [noPair_meet](../../../../Solutions/Source_ReferenceIutCanLiftNoPair.lean#L121) · [noPair_disjoint](../../../../Solutions/Source_ReferenceIutCanLiftNoPair.lean#L270) · [noPair](../../../../Solutions/Source_ReferenceIutCanLiftNoPair.lean#L357) |
| Fricke matrix action and degeneration | [slMap](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L34) · [transl](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Unipotent.lean#L29) · [slMap_commK](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L154) · [unbounded_complex](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L199) | [slMap](../../../../Solutions/Source_ReferenceIutCanLiftFrickeComplexAction.lean#L34) · [transl](../../../../Solutions/Source_ReferenceIutCanLiftFrickeComplexAction.lean#L44) · [slMap_commK](../../../../Solutions/Source_ReferenceIutCanLiftFrickeComplexAction.lean#L88) · [unbounded_complex](../../../../Solutions/Source_ReferenceIutCanLiftFrickeComplexAction.lean#L104) |
| Reuse in non-elementarity | [actsOn_slMap](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L50) · [normal form application](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L239) | [actsOn_slMap](../../../../Solutions/Source_ReferenceIutCanLiftNonElementary.lean#L34) · [nonElem_slMap](../../../../Solutions/Source_ReferenceIutCanLiftNonElementary.lean#L102) |
