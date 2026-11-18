# Independent read-back of `prime_dvd_card_range`

## English

Let $F$ be a number field, with chosen algebraic closure $\overline F$ in the same universe. Let $E/F$ be an elliptic curve in Weierstrass form. Write $\mathcal B$ for the set of finite places of $F$ where $E$ has multiplicative reduction. The reduction conditions allow changes of Weierstrass variables over $F$ before passing to the completion. For a finite place $w$, write $p(w)$ for its residue characteristic and $f_w$ for its residue degree over the residue field of $\mathbb Q$ at $p(w)$. Put $M=\mathbb Q(j(E))\subseteq F$.

Fix a curve arithmetic record for these data. It supplies the following facts.

- The field $F$ contains a square root of $-1$.
- The curve has good or multiplicative reduction at every finite place of $F$.
- Every point of $E(\overline F)$ killed by multiplication by $6$ comes from $E(F)$.
- For every prime natural number $r\geq7$, the extension $F/M$ is Galois and $[F:M]$ is coprime to $r$.
- Every finite place of $F$ lies above a finite place of $M$. Each such pair of places has the same residue characteristic.
- Take a finite place $v$ of $M$ with residue characteristic different from $2$. Multiplicative reduction at one place above $v$ implies multiplicative reduction at every place above $v$.
- The set $\mathcal B$ is finite, and $f_w>0$ at every finite place $w$ of $F$.
- For every natural number $n$, the sum of $f_w$ over $w\in\mathcal B$ with $p(w)=n$ is at most $[F:\mathbb Q]$.

Fix Tate inputs for $E$. At each $w\in\mathcal B$, they give a parameter $q_w\in F_w^\times$ with $\lVert q_w\rVert_w<1$. The field $F_w$ is the completion of $F$ at $w$. The $j$-invariant of the Tate curve for $q_w$ equals the image of $j(E)$ in $F_w$. The Tate inputs also give a nonzero uniformizer $\pi_w$ of norm less than one. The norm of every nonzero element of $F_w$ is an integer power of $\lVert\pi_w\rVert_w$. Let $m(w)$ be the natural number with $\lVert q_w\rVert_w=\lVert\pi_w\rVert_w^{m(w)}$.

Let $\ell$ be a prime natural number with $\ell\ne2$. Fix a mod-$\ell$ representation record for $E$ and $\overline F$. The record gives an additive isomorphism $\iota$ from $E(\overline F)[\ell]$ to $(\mathbb Z/\ell\mathbb Z)^2$. This subgroup consists of the points that multiplication by $\ell$ sends to the identity. The record also gives a group homomorphism $\rho\colon\operatorname{Gal}(\overline F/F)\to\operatorname{GL}_2(\mathbb Z/\ell\mathbb Z)$ whose kernel is open in the Krull topology. For every $\sigma\in\operatorname{Gal}(\overline F/F)$ and every $P\in E(\overline F)[\ell]$, the record satisfies $\iota(\sigma P)=\rho(\sigma)\iota(P)$. Here the action on points applies $\sigma$ to the affine coordinates and fixes the point at infinity.

Assume both of the following.

- At every $w\in\mathcal B$, the prime $\ell$ does not divide $m(w)$.
- There exists a finite place $w\in\mathcal B$ with $p(w)\ne2$ and $p(w)\ne\ell$.

Then $\ell$ divides the cardinality of the image of $\rho$ in $\operatorname{GL}_2(\mathbb Z/\ell\mathbb Z)$.

## 简体中文

设 $F$ 为数域，$\overline F$ 为与 $F$ 同属一个宇宙层级的选定代数闭包，$E/F$ 为魏尔斯特拉斯形式的椭圆曲线。记 $\mathcal B$ 为 $E$ 具有乘法约化的 $F$ 的有限处构成的集合。约化条件允许在取完备化之前对魏尔斯特拉斯方程作 $F$ 上的变量变换。对 $F$ 的有限处 $w$，记其剩余特征为 $p(w)$，其相对于 $\mathbb Q$ 在 $p(w)$ 处的剩余域的剩余次数为 $f_w$。令 $M=\mathbb Q(j(E))\subseteq F$。

给定上述数据的曲线算术记录。该记录包含以下性质。

- $F$ 含有 $-1$ 的平方根。
- $E$ 在 $F$ 的每个有限处具有良好约化或乘法约化。
- $E(\overline F)$ 中每个被乘以 $6$ 消去的点都来自 $E(F)$。
- 对每个满足 $r\geq7$ 的自然数素数 $r$，扩张 $F/M$ 为伽罗瓦扩张，且 $[F:M]$ 与 $r$ 互素。
- $F$ 的每个有限处都位于 $M$ 的某个有限处之上。每对具有这种关系的有限处的剩余特征相同。
- 如果 $M$ 的有限处 $v$ 的剩余特征不等于 $2$，且 $E$ 在 $v$ 上方某个 $F$ 的有限处具有乘法约化，那么 $E$ 在 $v$ 上方 $F$ 的每个有限处都具有乘法约化。
- $\mathcal B$ 是有限集，且 $F$ 的每个有限处 $w$ 都满足 $f_w>0$。
- 对任意自然数 $n$，将满足 $p(w)=n$ 的所有 $w\in\mathcal B$ 的 $f_w$ 相加，所得总和至多为 $[F:\mathbb Q]$。

给定 $E$ 的泰特输入数据。对每个 $w\in\mathcal B$，该数据给出泰特参数 $q_w\in F_w^\times$，且 $\lVert q_w\rVert_w<1$。这里 $F_w$ 是 $F$ 在 $w$ 处的完备化。$q_w$ 的泰特曲线的 $j$ 不变量等于 $j(E)$ 在 $F_w$ 中的像。数据还给出非零的一致化元 $\pi_w$，其范数小于一。$F_w$ 中每个非零元素的范数都是 $\lVert\pi_w\rVert_w$ 的整数次幂。记 $m(w)$ 为满足 $\lVert q_w\rVert_w=\lVert\pi_w\rVert_w^{m(w)}$ 的自然数。

设 $\ell$ 为满足 $\ell\ne2$ 的自然数素数。给定关于 $E$ 与 $\overline F$ 的模 $\ell$ 表示记录。记 $E(\overline F)[\ell]$ 为 $E(\overline F)$ 中全部被乘以 $\ell$ 消去的点构成的子群。该记录给出从 $E(\overline F)[\ell]$ 到 $(\mathbb Z/\ell\mathbb Z)^2$ 的加法群同构 $\iota$，以及群同态 $\rho\colon\operatorname{Gal}(\overline F/F)\to\operatorname{GL}_2(\mathbb Z/\ell\mathbb Z)$，其核在克鲁尔拓扑中为开集。对每个 $\sigma\in\operatorname{Gal}(\overline F/F)$ 和 $P\in E(\overline F)[\ell]$，有 $\iota(\sigma P)=\rho(\sigma)\iota(P)$。这里的伽罗瓦作用将 $\sigma$ 作用于仿射坐标，并固定无穷远点。

假设以下两个条件都成立。

- 对每个 $w\in\mathcal B$，素数 $\ell$ 不整除 $m(w)$。
- 存在 $F$ 的有限处 $w\in\mathcal B$，满足 $p(w)\ne2$ 且 $p(w)\ne\ell$。

则 $\ell$ 整除 $\rho$ 在 $\operatorname{GL}_2(\mathbb Z/\ell\mathbb Z)$ 中的像的基数。

## 日本語

$F$ を数体、$\overline F$ を $F$ と同じ宇宙レベルにある選んだ代数閉包、$E/F$ をワイエルシュトラス形の楕円曲線とする。$E$ が乗法的還元を持つ $F$ の有限素点の集合を $\mathcal B$ と書く。還元の条件では、完備化に移る前に $F$ 上でワイエルシュトラス方程式の変数変換を行ってよい。$F$ の有限素点 $w$ の剰余標数を $p(w)$、有理数体の $p(w)$ における剰余体上の剰余次数を $f_w$ と書く。$M=\mathbb Q(j(E))\subseteq F$ と置く。

これらのデータに対し、以下を満たす曲線の算術データを与える。

- $F$ は $-1$ の平方根を含む。
- $E$ は $F$ の各有限素点で良い還元または乗法的還元を持つ。
- $E(\overline F)$ の $6$ 倍が零となる各点は $E(F)$ から来る。
- $r\geq7$ であるすべての自然数の素数 $r$ について、$F/M$ はガロア拡大であり、$[F:M]$ と $r$ は互いに素である。
- $F$ の各有限素点は $M$ のある有限素点の上にある。その関係にある二つの有限素点の剰余標数は等しい。
- $M$ の有限素点 $v$ の剰余標数が $2$ と異なるとき、$F$ の $v$ の上にある一つの有限素点で $E$ が乗法的還元を持てば、$F$ の $v$ の上にあるすべての有限素点で $E$ は乗法的還元を持つ。
- $\mathcal B$ は有限であり、$F$ の各有限素点 $w$ で $f_w>0$ が成り立つ。
- 任意の自然数 $n$ について、$p(w)=n$ を満たす $w\in\mathcal B$ の $f_w$ の和は $[F:\mathbb Q]$ 以下である。

$E$ のテイト入力データを与える。各 $w\in\mathcal B$ に対し、このデータは $\lVert q_w\rVert_w<1$ を満たすテイトパラメータ $q_w\in F_w^\times$ を与える。ここで $F_w$ は $F$ の $w$ における完備化である。$q_w$ のテイト曲線の $j$ 不変量は $F_w$ における $j(E)$ の像に等しい。このデータはさらにノルムが一未満の零でない一様化元 $\pi_w$ を与える。$F_w$ の各非零元のノルムは $\lVert\pi_w\rVert_w$ の整数乗である。$\lVert q_w\rVert_w=\lVert\pi_w\rVert_w^{m(w)}$ を満たす自然数を $m(w)$ とする。

$\ell\ne2$ を満たす自然数の素数 $\ell$ を取る。$E$ と $\overline F$ に関する法 $\ell$ の表現データを与える。$E(\overline F)[\ell]$ は $E(\overline F)$ のうち $\ell$ 倍が零となる点の部分群を表す。このデータは $E(\overline F)[\ell]$ から $(\mathbb Z/\ell\mathbb Z)^2$ への加法群同型 $\iota$ と群準同型 $\rho\colon\operatorname{Gal}(\overline F/F)\to\operatorname{GL}_2(\mathbb Z/\ell\mathbb Z)$ を与える。$\rho$ の核はクルル位相で開である。すべての $\sigma\in\operatorname{Gal}(\overline F/F)$ と $P\in E(\overline F)[\ell]$ について $\iota(\sigma P)=\rho(\sigma)\iota(P)$ が成り立つ。このガロア作用は各アフィン座標に $\sigma$ を適用し、無限遠点を固定する。

次の二条件を仮定する。

- 各 $w\in\mathcal B$ について、$\ell$ は $m(w)$ を割り切らない。
- $p(w)\ne2$ かつ $p(w)\ne\ell$ を満たす $F$ の有限素点 $w\in\mathcal B$ が存在する。

このとき、$\ell$ は $\operatorname{GL}_2(\mathbb Z/\ell\mathbb Z)$ における $\rho$ の像の位数を割り切る。

[Lean statement](/home/admin-wsl/Coq/abc/refer/iut/Iut/Concrete/SL2Image.lean:217) · [Curve arithmetic](/home/admin-wsl/Coq/abc/refer/iut/Iut/Concrete/Existence.lean:110) · [Tate inputs and representation](/home/admin-wsl/Coq/abc/refer/iut/Iut/Concrete/Existence.lean:143)

The Chinese read-back uses `一致化元` as a working translation for “uniformizer.” The terminology choice remains open in the project glossary. [Prove2Me adaptation status](/home/admin-wsl/Coq/abc/docs/Prove2Me适配状态.md:119)
