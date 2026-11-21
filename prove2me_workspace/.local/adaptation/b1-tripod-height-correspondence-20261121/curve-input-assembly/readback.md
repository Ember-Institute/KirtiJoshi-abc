# `AbcAdaptation.Tripod.curveInputs`

The assembly records upstream revision `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8` of `Iut/Tripod/CurveFacts.lean`. [Assembly](CheckTripodCurveInputsAssembly.lean#L48) · [Local reference copy](../../../../../refer/iut/Iut/Tripod/CurveFacts.lean#L492)

## English

### Points and parameters

The constructor returns `CurveInputs tripodTheory AG K d` for IUT IV, Corollary 2.2. Let $U$ be the set of tripod points with parameter $\lambda\in\overline{\mathbb Q}\setminus\{0,1\}$. For each $x\in U$, put $L_x=\mathbb Q(\lambda)$ and $e_x=[L_x:\mathbb Q]$.

The input `K` gives a finite set of rational primes $V$ containing $2$ and a real bound $c=K.c$. The set $S=K.\mathrm{set}$ requires both $|\log|\lambda|_v|\le c$ and $|\log|\lambda-1|_v|\le c$. These bounds apply at every infinite place of $L_x$ and every finite place of $L_x$ with residue characteristic in $V$. The natural number `d` defines $W=\{x\in S:e_x\le d\}$. The implicit inputs are the anabelian geometry `AG : AnabelianGeometry.{0}` and the real constant `TK`, written $T_K$. [Point locus](../../../../Definitions/Def_AbcTripod.lean#L175)

### `h`, `curve`, `arith`, `tate`, `modRep`, `height_eq`

The input `P : CurveProviders` supplies finiteness of the points killed by $3$ and by $5$ for every parameter $t\in\overline{\mathbb Q}$, including $0$ and $1$. The equation is $Y^2=X^3-(1+t)X^2+tX$. Let $C_n(t)$ be the set of coordinates of nonsingular affine points killed by $n$. The identity at infinity contributes no coordinates. For $x\in U$, the field $F_x$ adjoins $\lambda$, the chosen square roots of $-1,\lambda,1-\lambda$, and $C_3(\lambda)\cup C_5(\lambda)$ to $\mathbb Q$. Finiteness of the coordinate sets makes $F_x$ a number field. The curve $E_x/F_x$ uses the same equation with $t=\lambda$. Its base field has algebraic closure $\overline{\mathbb Q}$. [Provider](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviders.lean#L28)

Write $M_x=\mathbb Q(j(E_x))$, $\delta_x=[F_x:\mathbb Q]$, and $\mathcal B_x$ for the finite places of $F_x$ where $E_x$ has multiplicative reduction. At a finite place $w$, write $p(w)$ for its residue characteristic and $f(w)$ for its residue degree over $\mathbb Q$. The arithmetic data say that $-1$ is a square in $F_x$, reduction is good or multiplicative at every finite place, and the $6$-torsion is rational over $F_x$. They give that $F_x/M_x$ is Galois with degree prime to every prime $\ell\ge7$. Each finite place of $F_x$ lies over a finite place of $M_x$ with the same residue characteristic. Over a place of $M_x$ of odd residue characteristic, multiplicative reduction at one place above it implies multiplicative reduction at all places above it. The data also give finiteness of $\mathcal B_x$, positivity of $f(w)$, and $\sum_{w\in\mathcal B_x,\ p(w)=r} f(w)\le\delta_x$ for every $r\in\mathbb N$. [Curve arithmetic](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveArithmetic.lean#L50)

For each $w\in\mathcal B_x$, `P.tate x` uses classical choice for the Tate parameter $q_w$ and uniformizer $\pi_w$ in the completion of $F_x$ at $w$. The parameter has $0<\|q_w\|_w<1$, and its Tate $j$-invariant equals the image of $j(E_x)$. Its order is the positive natural number $m(w)$ with $\|q_w\|_w=\|\pi_w\|_w^{m(w)}$. The local data set $m(w)=0$ outside $\mathcal B_x$. The fields `h` and `height_eq` use the same local data as the contribution $h_2$ at $2$. [Tate data](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TateInputsSupply.lean#L196) · [Provider height](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviderHeight.lean#L17)

$$
h(x)=\frac{1}{\delta_x}\sum_{w\in\mathcal B_x}m(w)f(w)\log p(w),\qquad
h_2(x)=\frac{1}{\delta_x}\sum_{\substack{w\in\mathcal B_x\\p(w)=2}}m(w)f(w)\log p(w).
$$

The field `h` is `P.h` on all of $U$. For each $x\in W$ and each witness of membership, the fields `curve`, `arith`, `tate`, and `modRep` use the corresponding data from $P$. For each prime $\ell$ with primality witness `hℓ`, `P.modRep x ℓ hℓ` identifies $E_x[\ell]$ additively with $\mathbb F_\ell^2$. It gives a homomorphism $\rho_{x,\ell}\colon\operatorname{Gal}(\overline{\mathbb Q}/F_x)\to\mathrm{GL}_2(\mathbb F_\ell)$ with open kernel. Its matrices express the Galois action in that identification. The equality of the local height with $h(x)$ holds by definition in `height_eq`. [Representation data](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveData.lean#L54)

### `deg_le`, `dmod_le`

The inputs `hdeg3` and `hdeg5` give the following degree bound for $n=3$ and $n=5$, respectively. It applies to every $x\in U$ and every finite intermediate field $\mathbb Q\subseteq L\subseteq\overline{\mathbb Q}$ containing $\lambda$.

$$
[L(C_n(\lambda)):\mathbb Q]\le(n^2-1)(n^2-n)[L:\mathbb Q].
$$

Here $L(C_n(\lambda))$ adjoins the indicated coordinates to $L$. On $W$, `deg_le` uses these bounds to give $[F_x:\mathbb Q]\le 552960d$, and `dmod_le` gives $[M_x:\mathbb Q]\le d$. [Torsion degree bound](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveDegreeBound.lean#L33)

### `htCan_equiv`, `northcott`, `B`, `B_nonneg`, `heightEq_two_le`

The canonical point height $h_{\mathrm{can}}(x)$ is the logarithmic height of $\lambda$ relative to $L_x$, divided by $e_x$. The input `hh` supplies real constants $a_1,a_2$ such that on $S$,

$$
\frac{h(x)}6\le h_{\mathrm{can}}(x)+a_1,\qquad
h_{\mathrm{can}}(x)\le\frac{h(x)}6+a_2.
$$

The record stores this comparison in `htCan_equiv`. The input `hN` gives finiteness of $\{x\in U:e_x\le b,\ h_{\mathrm{can}}(x)\le H\}$ for every $b\in\mathbb N$ and $H\in\mathbb R$. The field `northcott` uses `hN` and `hh` to give finiteness of $\{x\in W:h(x)\le H\}$ for every real $H$. [Northcott comparison](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_NorthcottComparison.lean#L21)

The field `B` is $\max(4c,0)$, with $0\le B$ in `B_nonneg`. The input `hB` gives $h_2(x)\le B$ for every $x\in S$. The field `heightEq_two_le` applies it on $W$. [Bound at 2](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_TwoAdicBoundHyp.lean#L21)

### `HasCyclicSubgroup`, `TK`, `cyclic_bound`, `sl2_of`

The field `HasCyclicSubgroup` is the predicate $G(x,\ell)$ for $x\in U$ and $\ell\in\mathbb N$. It asserts that some additive subgroup of $E_x(\overline{\mathbb Q})$ has natural number cardinality $\ell$ and is stable under $\operatorname{Gal}(\overline{\mathbb Q}/F_x)$. Lean's `Nat.card` assigns zero to infinite sets. The field `TK` stores $T_K$. The only field of the input `CF` gives `cyclic_bound` for every $x\in W$ and prime $\ell\ge7$. If $\ell\nmid m(w)$ for every $w\in\mathcal B_x$ and $G(x,\ell)$ holds, then

$$
\frac{\ell-2}{24}\bigl(h(x)-h_2(x)\bigr)\le 2\log\ell+T_K.
$$

The private theorem `sl2Image` proves an implication from $P$ for every $x\in U$ and prime $\ell\ge5$. The Tate orders and residue characteristics come from the same local data as $h$ and $h_2$.

- (P2) $\ell\nmid m(w)$ for every $w\in\mathcal B_x$.
- (P4) $\neg G(x,\ell)$. The curve has no Galois-stable subgroup of order $\ell$.
- (P5) Some $w\in\mathcal B_x$ has $p(w)\ne2$ and $p(w)\ne\ell$.

Under these premises, every determinant-one matrix in $\mathrm{SL}_2(\mathbb F_\ell)$ belongs to the image of the supplied $\rho_{x,\ell}$ as an element of $\mathrm{GL}_2(\mathbb F_\ell)$. The field `sl2_of` applies this implication on $W$. [Cyclic and image conditions](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts.lean#L23) · [Image proof](/tmp/mcp-ci/01a1f575-a867-75d1-9ba5-04ce946763c8/assembly/Source_TripodCurveInputsAssembly.lean#L25)

### `logDiff_eq`, `excCore_finite`, `logCond_ge`, `logCond_le`

The tripodal field $F_x^\ast\subseteq F_x$ is generated over $\mathbb Q$ by $j(E_x)$ and the first coordinates of nonsingular affine $2$-torsion points over $F_x$. Write $\mathfrak D_{F_x^\ast/\mathbb Q}$ for the different ideal and $\mathrm N_{\mathrm{abs}}$ for the absolute ideal norm. The field `logDiff_eq` gives, on $W$,

$$
\frac{\log|\operatorname{disc}(L_x)|}{e_x}
=\frac{\log\mathrm N_{\mathrm{abs}}(\mathfrak D_{F_x^\ast/\mathbb Q})}{[F_x^\ast:\mathbb Q]}.
$$

The input `hcore` gives `excCore_finite`. A point in $W$ is exceptional if the core condition fails after some base change. In `AG`, form the once-punctured orbicurve of $E_x$ and its sign quotient. The core condition requires the base-changed quotient to be a core of the base-changed orbicurve along every unital field map from $F_x$ to a characteristic-zero field in universe $0$. The exceptional set is finite. [Core condition](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean#L32)

The point conductor $\gamma(x)$ sums log absolute norms of the maximal ideals at the finite places of $L_x$ where $|\lambda|_v\ne1$ or $|\lambda-1|_v\ne1$, divided by $e_x$. For $\gamma_\ell(x)$, select finite places $v$ of $M_x$ with residue characteristic different from both $2$ and $\ell$. Require at least one place of $F_x$ above $v$, and require all such places to belong to $\mathcal B_x$. Sum log absolute norms of the maximal ideals at the finite places of $F_x^\ast$ with a place of $F_x$ above both them and some selected $v$. Divide by $[F_x^\ast:\mathbb Q]$. The inputs `hge` and `hle` give the respective lower and upper bounds for all $x\in U$ and all primes $\ell\ge7$.

$$
\gamma_\ell(x)\le\gamma(x)\le\gamma_\ell(x)+\log(2\ell).
$$

The fields `logCond_ge` and `logCond_le` apply the bounds on $W$. All logarithms are natural. [Conductor of the tripodal field](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean#L33)

`CurveInputs.toCorollary22Inputs` computes `localData` from `curve`, `arith`, and `tate`. It defines `SL2Image` with `modRep` and supplies its image implication with `sl2_of`. [Corollary 2.2 consumer](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean#L142)

## 简体中文

### 点与参数

构造函数返回 IUT IV 推论 2.2 的 `CurveInputs tripodTheory AG K d`。令 $U$ 为参数 $\lambda\in\overline{\mathbb Q}\setminus\{0,1\}$ 的三足曲线点集。对每个 $x\in U$，记 $L_x=\mathbb Q(\lambda)$、$e_x=[L_x:\mathbb Q]$。

输入 `K` 给出含 $2$ 的有理素数有限集 $V$ 和实数界 $c=K.c$。集合 $S=K.\mathrm{set}$ 要求 $|\log|\lambda|_v|\le c$ 与 $|\log|\lambda-1|_v|\le c$ 同时成立。这些界适用于 $L_x$ 的所有无穷位和剩余特征在 $V$ 中的所有有限位。自然数 `d` 定义 $W=\{x\in S:e_x\le d\}$。隐式输入为远阿贝尔几何 `AG : AnabelianGeometry.{0}` 与实常数 `TK`，后者记为 $T_K$。 [点集](../../../../Definitions/Def_AbcTripod.lean#L175)

### `h`、`curve`、`arith`、`tate`、`modRep`、`height_eq`

输入 `P : CurveProviders` 给出对每个参数 $t\in\overline{\mathbb Q}$，被 $3$ 倍和被 $5$ 倍消去的点各自构成有限集，其中也包括参数 $0$ 和 $1$。所用方程为 $Y^2=X^3-(1+t)X^2+tX$。令 $C_n(t)$ 为被 $n$ 倍消去的非奇异仿射点的坐标集。无穷远处的单位元不贡献坐标。对 $x\in U$，在 $\mathbb Q$ 上添入 $\lambda$、$-1,\lambda,1-\lambda$ 的选定平方根及 $C_3(\lambda)\cup C_5(\lambda)$，得到 $F_x$。坐标集的有限性保证 $F_x$ 是数域。在同一方程中取 $t=\lambda$，得到 $E_x/F_x$，并取 $\overline{\mathbb Q}$ 为 $F_x$ 的代数闭包。 [曲线数据提供者](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviders.lean#L28)

记 $M_x=\mathbb Q(j(E_x))$、$\delta_x=[F_x:\mathbb Q]$，并记 $\mathcal B_x$ 为 $E_x$ 在 $F_x$ 上具有乘法约化的有限位集合。对有限位 $w$，记 $p(w)$ 为其剩余特征，$f(w)$ 为其相对于 $\mathbb Q$ 的剩余次数。算术数据给出 $-1$ 是 $F_x$ 中的平方元、每个有限位处为良好约化或乘法约化，以及被 $6$ 倍消去的点均在 $F_x$ 上有理。扩张 $F_x/M_x$ 是伽罗瓦扩张，其次数与每个素数 $\ell\ge7$ 互素。$F_x$ 的每个有限位都位于 $M_x$ 的一个剩余特征相同的有限位之上。在 $M_x$ 的奇剩余特征位之上，一个位上有乘法约化就推出其上所有位上有乘法约化。数据还给出 $\mathcal B_x$ 有限、$f(w)>0$，以及对每个 $r\in\mathbb N$ 有 $\sum_{w\in\mathcal B_x,\ p(w)=r} f(w)\le\delta_x$。 [曲线算术](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveArithmetic.lean#L50)

对每个 $w\in\mathcal B_x$，`P.tate x` 用经典选择在 $F_x$ 于 $w$ 的完备化中取 Tate 参数 $q_w$ 和一致化参数 $\pi_w$。该 Tate 参数满足 $0<\|q_w\|_w<1$，其 Tate $j$-不变量等于 $j(E_x)$ 的像。它的阶数 $m(w)$ 是正整数，满足 $\|q_w\|_w=\|\pi_w\|_w^{m(w)}$。在 $\mathcal B_x$ 之外，局部数据取 $m(w)=0$。字段 `h` 和 `height_eq` 与 $2$ 处的贡献 $h_2$ 使用同一份局部数据。 [Tate 数据](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TateInputsSupply.lean#L196) · [曲线高度](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviderHeight.lean#L17)

$$
h(x)=\frac{1}{\delta_x}\sum_{w\in\mathcal B_x}m(w)f(w)\log p(w),\qquad
h_2(x)=\frac{1}{\delta_x}\sum_{\substack{w\in\mathcal B_x\\p(w)=2}}m(w)f(w)\log p(w).
$$

字段 `h` 是整个 $U$ 上的 `P.h`。对每个 $x\in W$ 及每个所属证明，字段 `curve`、`arith`、`tate` 和 `modRep` 采用 $P$ 的相应数据。对每个素数 $\ell$ 及其素性证明 `hℓ`，`P.modRep x ℓ hℓ` 给出 $E_x[\ell]$ 与 $\mathbb F_\ell^2$ 的加法群同构。它给出开核同态 $\rho_{x,\ell}\colon\operatorname{Gal}(\overline{\mathbb Q}/F_x)\to\mathrm{GL}_2(\mathbb F_\ell)$。该同态的矩阵在此同构下表示伽罗瓦作用。`height_eq` 中局部高度等于 $h(x)$，由定义成立。 [表示数据](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveData.lean#L54)

### `deg_le`、`dmod_le`

输入 `hdeg3` 和 `hdeg5` 分别给出 $n=3$ 和 $n=5$ 时的下列次数界。它适用于每个 $x\in U$ 和每个包含 $\lambda$ 的有限次中间域 $\mathbb Q\subseteq L\subseteq\overline{\mathbb Q}$。

$$
[L(C_n(\lambda)):\mathbb Q]\le(n^2-1)(n^2-n)[L:\mathbb Q].
$$

这里 $L(C_n(\lambda))$ 由在 $L$ 上添入相应坐标得到。在 $W$ 上，`deg_le` 用这些界给出 $[F_x:\mathbb Q]\le 552960d$，`dmod_le` 给出 $[M_x:\mathbb Q]\le d$。 [挠点次数界](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveDegreeBound.lean#L33)

### `htCan_equiv`、`northcott`、`B`、`B_nonneg`、`heightEq_two_le`

点的典范高度 $h_{\mathrm{can}}(x)$ 为 $\lambda$ 相对于 $L_x$ 的对数高度除以 $e_x$。输入 `hh` 给出实常数 $a_1,a_2$，使下列不等式在 $S$ 上成立。

$$
\frac{h(x)}6\le h_{\mathrm{can}}(x)+a_1,\qquad
h_{\mathrm{can}}(x)\le\frac{h(x)}6+a_2.
$$

字段 `htCan_equiv` 保存这一比较。输入 `hN` 给出对每个 $b\in\mathbb N$ 和 $H\in\mathbb R$，集合 $\{x\in U:e_x\le b,\ h_{\mathrm{can}}(x)\le H\}$ 有限。字段 `northcott` 使用 `hN` 和 `hh`，得到对每个实数 $H$，集合 $\{x\in W:h(x)\le H\}$ 有限。 [Northcott 比较](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_NorthcottComparison.lean#L21)

字段 `B` 取 $\max(4c,0)$，字段 `B_nonneg` 给出 $0\le B$。输入 `hB` 给出对每个 $x\in S$ 均有 $h_2(x)\le B$。字段 `heightEq_two_le` 在 $W$ 上使用此界。 [2 处贡献的界](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_TwoAdicBoundHyp.lean#L21)

### `HasCyclicSubgroup`、`TK`、`cyclic_bound`、`sl2_of`

字段 `HasCyclicSubgroup` 给出 $x\in U$、$\ell\in\mathbb N$ 上的谓词 $G(x,\ell)$。它断言 $E_x(\overline{\mathbb Q})$ 存在自然数基数为 $\ell$ 的加法子群，且该子群在 $\operatorname{Gal}(\overline{\mathbb Q}/F_x)$ 的作用下稳定。Lean 的 `Nat.card` 对无限集取零。字段 `TK` 保存 $T_K$。输入 `CF` 的唯一字段为每个 $x\in W$ 和每个素数 $\ell\ge7$ 给出 `cyclic_bound`。若对所有 $w\in\mathcal B_x$ 都有 $\ell\nmid m(w)$ 且 $G(x,\ell)$ 成立，则

$$
\frac{\ell-2}{24}\bigl(h(x)-h_2(x)\bigr)\le 2\log\ell+T_K.
$$

私有定理 `sl2Image` 从 $P$ 出发，对每个 $x\in U$ 和每个素数 $\ell\ge5$ 证明以下蕴含。Tate 阶数和剩余特征均取自 $h$ 和 $h_2$ 使用的同一份局部数据。

- (P2) 对每个 $w\in\mathcal B_x$，均有 $\ell\nmid m(w)$。
- (P4) $\neg G(x,\ell)$。曲线没有阶为 $\ell$ 的伽罗瓦稳定子群。
- (P5) 存在 $w\in\mathcal B_x$ 同时满足 $p(w)\ne2$ 和 $p(w)\ne\ell$。

在这些前提下，$\mathrm{SL}_2(\mathbb F_\ell)$ 中每个行列式为 $1$ 的矩阵作为 $\mathrm{GL}_2(\mathbb F_\ell)$ 的元素，都属于所给 $\rho_{x,\ell}$ 的像。字段 `sl2_of` 在 $W$ 上使用这一蕴含。 [循环子群与像条件](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts.lean#L23) · [像的证明](/tmp/mcp-ci/01a1f575-a867-75d1-9ba5-04ce946763c8/assembly/Source_TripodCurveInputsAssembly.lean#L25)

### `logDiff_eq`、`excCore_finite`、`logCond_ge`、`logCond_le`

三足域 $F_x^\ast\subseteq F_x$ 由 $j(E_x)$ 和 $F_x$ 上非奇异仿射 $2$ 阶挠点的第一坐标在 $\mathbb Q$ 上生成。记 $\mathfrak D_{F_x^\ast/\mathbb Q}$ 为不同理想，$\mathrm N_{\mathrm{abs}}$ 为理想的绝对范数。字段 `logDiff_eq` 在 $W$ 上给出

$$
\frac{\log|\operatorname{disc}(L_x)|}{e_x}
=\frac{\log\mathrm N_{\mathrm{abs}}(\mathfrak D_{F_x^\ast/\mathbb Q})}{[F_x^\ast:\mathbb Q]}.
$$

输入 `hcore` 给出 `excCore_finite`。若核心条件在某次基变换后失败，则 $W$ 中的该点是例外点。用 `AG` 取 $E_x$ 去一点所得的轨形曲线及其符号作用之商。核心条件要求，沿从 $F_x$ 到类型宇宙 $0$ 中任一特征零域的每个保单位元的域同态做基变换后，所得商是基变换后轨形曲线的核心。例外点集有限。 [核心条件](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean#L32)

点导子 $\gamma(x)$ 对 $L_x$ 中满足 $|\lambda|_v\ne1$ 或 $|\lambda-1|_v\ne1$ 的有限位求对应极大理想的绝对范数的对数之和，再除以 $e_x$。计算 $\gamma_\ell(x)$ 时，选取 $M_x$ 中剩余特征异于 $2$ 和 $\ell$ 的有限位 $v$。要求 $v$ 上方至少有一个 $F_x$ 的有限位，且所有这样的位均属于 $\mathcal B_x$。对 $F_x^\ast$ 中的有限位求对应极大理想的绝对范数的对数之和，计入的位须有一个 $F_x$ 的位同时位于其上方和某个选定的 $v$ 上方。将和除以 $[F_x^\ast:\mathbb Q]$。输入 `hge` 和 `hle` 分别对所有 $x\in U$ 和所有素数 $\ell\ge7$ 给出下界与上界。

$$
\gamma_\ell(x)\le\gamma(x)\le\gamma_\ell(x)+\log(2\ell).
$$

字段 `logCond_ge` 和 `logCond_le` 在 $W$ 上使用这些界。所有对数均为自然对数。 [三足域的导子](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean#L33)

`CurveInputs.toCorollary22Inputs` 从 `curve`、`arith` 和 `tate` 计算 `localData`。它用 `modRep` 定义 `SL2Image`，用 `sl2_of` 提供相应的像蕴含。 [推论 2.2 的消费者](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean#L142)

## 日本語

### 点とパラメータ

構成子は IUT IV 系 2.2 の `CurveInputs tripodTheory AG K d` を返す。$U$ を、パラメータ $\lambda\in\overline{\mathbb Q}\setminus\{0,1\}$ を持つ三脚曲線の点の集合とする。各 $x\in U$ に対し $L_x=\mathbb Q(\lambda)$、$e_x=[L_x:\mathbb Q]$ と置く。

入力 `K` は、$2$ を含む有理素数の有限集合 $V$ と実数の上界 $c=K.c$ を与える。集合 $S=K.\mathrm{set}$ では、$|\log|\lambda|_v|\le c$ と $|\log|\lambda-1|_v|\le c$ の両方が成り立つ。これらの上界は、$L_x$ のすべての無限素点と剰余標数が $V$ に属するすべての有限素点で課される。自然数 `d` により $W=\{x\in S:e_x\le d\}$ を定める。暗黙の入力は遠アーベル幾何 `AG : AnabelianGeometry.{0}` と実定数 `TK` であり、後者を $T_K$ と書く。 [点の集合](../../../../Definitions/Def_AbcTripod.lean#L175)

### `h`、`curve`、`arith`、`tate`、`modRep`、`height_eq`

入力 `P : CurveProviders` は、$0$ と $1$ を含む各パラメータ $t\in\overline{\mathbb Q}$ について、$3$ 倍で零になる点の集合と $5$ 倍で零になる点の集合がそれぞれ有限であることを与える。用いる方程式は $Y^2=X^3-(1+t)X^2+tX$ である。$C_n(t)$ を、$n$ 倍で零になる非特異なアフィン点の座標集合とする。無限遠の単位元は座標を寄与しない。各 $x\in U$ について、$\lambda$、$-1,\lambda,1-\lambda$ の選んだ平方根、および $C_3(\lambda)\cup C_5(\lambda)$ を $\mathbb Q$ に添加して $F_x$ を得る。座標集合の有限性から $F_x$ は数体である。同じ方程式に $t=\lambda$ を代入して $E_x/F_x$ を得る。$F_x$ の代数閉包には $\overline{\mathbb Q}$ を用いる。 [曲線データの供給元](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviders.lean#L28)

$M_x=\mathbb Q(j(E_x))$、$\delta_x=[F_x:\mathbb Q]$ とし、$\mathcal B_x$ を $E_x$ が $F_x$ 上で乗法的還元を持つ有限素点の集合とする。有限素点 $w$ の剰余標数を $p(w)$、$\mathbb Q$ 上の剰余次数を $f(w)$ と書く。算術データは、$-1$ が $F_x$ の平方元であること、各有限素点で良還元または乗法的還元を持つこと、$6$-ねじれ点がすべて $F_x$ 上有理であることを与える。$F_x/M_x$ は拡大次数が各素数 $\ell\ge7$ と互いに素なガロア拡大である。$F_x$ の各有限素点は、剰余標数が等しい $M_x$ の有限素点の上にある。$M_x$ の奇剰余標数の素点の上で、一つの素点で乗法的還元を持てば、その上のすべての素点で乗法的還元を持つ。さらに、$\mathcal B_x$ が有限で、$f(w)>0$ であり、すべての $r\in\mathbb N$ について $\sum_{w\in\mathcal B_x,\ p(w)=r} f(w)\le\delta_x$ が成り立つ。 [曲線の算術](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveArithmetic.lean#L50)

各 $w\in\mathcal B_x$ について、`P.tate x` は古典的選択により $F_x$ の $w$ での完備化のテイトパラメータ $q_w$ と素元 $\pi_w$ を取る。テイトパラメータは $0<\|q_w\|_w<1$ を満たし、そのテイト $j$-不変量は $j(E_x)$ の像に等しい。位数 $m(w)$ は正の自然数であり、 $\|q_w\|_w=\|\pi_w\|_w^{m(w)}$ を満たす。局所データは $\mathcal B_x$ の外で $m(w)=0$ とする。フィールド `h` と `height_eq` は、$2$ での寄与 $h_2$ と同じ局所データを使う。 [テイトデータ](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TateInputsSupply.lean#L196) · [曲線の高さ](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviderHeight.lean#L17)

$$
h(x)=\frac{1}{\delta_x}\sum_{w\in\mathcal B_x}m(w)f(w)\log p(w),\qquad
h_2(x)=\frac{1}{\delta_x}\sum_{\substack{w\in\mathcal B_x\\p(w)=2}}m(w)f(w)\log p(w).
$$

フィールド `h` は $U$ 全体での `P.h` である。各 $x\in W$ とその所属の各証拠に対し、`curve`、`arith`、`tate`、`modRep` は $P$ の対応するデータを使う。各素数 $\ell$ とその素数性の証明 `hℓ` に対し、`P.modRep x ℓ hℓ` は $E_x[\ell]$ と $\mathbb F_\ell^2$ の加法群同型を与える。さらに開核を持つ準同型 $\rho_{x,\ell}\colon\operatorname{Gal}(\overline{\mathbb Q}/F_x)\to\mathrm{GL}_2(\mathbb F_\ell)$ を与える。その行列は、この同型を通じたガロア作用を表す。`height_eq` における局所的な高さと $h(x)$ の等式は定義により成り立つ。 [表現のデータ](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveData.lean#L54)

### `deg_le`、`dmod_le`

入力 `hdeg3` と `hdeg5` は、$n=3$ と $n=5$ のそれぞれについて以下の次数の上界を与える。各 $x\in U$ と、$\lambda$ を含む各有限次中間体 $\mathbb Q\subseteq L\subseteq\overline{\mathbb Q}$ に適用できる。

$$
[L(C_n(\lambda)):\mathbb Q]\le(n^2-1)(n^2-n)[L:\mathbb Q].
$$

ここで $L(C_n(\lambda))$ は、該当する座標を $L$ に添加した体である。$W$ 上で、`deg_le` はこれらの上界を使って $[F_x:\mathbb Q]\le 552960d$ を与え、`dmod_le` は $[M_x:\mathbb Q]\le d$ を与える。 [ねじれ点の次数の上界](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveDegreeBound.lean#L33)

### `htCan_equiv`、`northcott`、`B`、`B_nonneg`、`heightEq_two_le`

点の標準高さ $h_{\mathrm{can}}(x)$ は、$\lambda$ の $L_x$ に関する相対対数高さを $e_x$ で割った値である。入力 `hh` は、$S$ 上で次の二つの不等式を満たす実定数 $a_1,a_2$ を与える。

$$
\frac{h(x)}6\le h_{\mathrm{can}}(x)+a_1,\qquad
h_{\mathrm{can}}(x)\le\frac{h(x)}6+a_2.
$$

フィールド `htCan_equiv` はこの比較を格納する。入力 `hN` は、各 $b\in\mathbb N$ と $H\in\mathbb R$ に対し、$\{x\in U:e_x\le b,\ h_{\mathrm{can}}(x)\le H\}$ が有限であることを与える。フィールド `northcott` は `hN` と `hh` を使い、各実数 $H$ に対し $\{x\in W:h(x)\le H\}$ が有限であることを与える。 [Northcott の比較](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_NorthcottComparison.lean#L21)

フィールド `B` は $\max(4c,0)$ であり、`B_nonneg` は $0\le B$ を与える。入力 `hB` はすべての $x\in S$ で $h_2(x)\le B$ を与える。フィールド `heightEq_two_le` はこの上界を $W$ 上で使う。 [2 での寄与の上界](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_TwoAdicBoundHyp.lean#L21)

### `HasCyclicSubgroup`、`TK`、`cyclic_bound`、`sl2_of`

フィールド `HasCyclicSubgroup` は、$x\in U$ と $\ell\in\mathbb N$ に対する述語 $G(x,\ell)$ である。これは、$E_x(\overline{\mathbb Q})$ の加法部分群で、自然数値の濃度が $\ell$ であり、$\operatorname{Gal}(\overline{\mathbb Q}/F_x)$ の作用で安定なものが存在することを表す。Lean の `Nat.card` は無限集合に零を割り当てる。フィールド `TK` は $T_K$ を格納する。入力 `CF` の唯一のフィールドは、各 $x\in W$ と各素数 $\ell\ge7$ に対して `cyclic_bound` を与える。すべての $w\in\mathcal B_x$ で $\ell\nmid m(w)$ が成り立ち、$G(x,\ell)$ が成り立つなら、

$$
\frac{\ell-2}{24}\bigl(h(x)-h_2(x)\bigr)\le 2\log\ell+T_K.
$$

非公開の定理 `sl2Image` は、各 $x\in U$ と各素数 $\ell\ge5$ について、次の含意を $P$ から証明する。テイトパラメータの位数と剰余標数は、$h$ と $h_2$ に使う局所データから取る。

- (P2) すべての $w\in\mathcal B_x$ について $\ell\nmid m(w)$ が成り立つ。
- (P4) $\neg G(x,\ell)$。曲線には位数 $\ell$ のガロア安定な部分群が存在しない。
- (P5) $p(w)\ne2$ と $p(w)\ne\ell$ をともに満たす $w\in\mathcal B_x$ が存在する。

これらの前提の下で、$\mathrm{SL}_2(\mathbb F_\ell)$ の行列式 $1$ の各行列は、$\mathrm{GL}_2(\mathbb F_\ell)$ の元として与えられた $\rho_{x,\ell}$ の像に属する。フィールド `sl2_of` はこの含意を $W$ 上で使う。 [巡回部分群と像の条件](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts.lean#L23) · [像の証明](/tmp/mcp-ci/01a1f575-a867-75d1-9ba5-04ce946763c8/assembly/Source_TripodCurveInputsAssembly.lean#L25)

### `logDiff_eq`、`excCore_finite`、`logCond_ge`、`logCond_le`

三脚体 $F_x^\ast\subseteq F_x$ は、$j(E_x)$ と $F_x$ 上の非特異なアフィン $2$-ねじれ点の第一座標が $\mathbb Q$ 上生成する体である。$\mathfrak D_{F_x^\ast/\mathbb Q}$ を相対差積イデアルとし、$\mathrm N_{\mathrm{abs}}$ をイデアルの絶対ノルムとする。フィールド `logDiff_eq` は $W$ 上で次の等式を与える。

$$
\frac{\log|\operatorname{disc}(L_x)|}{e_x}
=\frac{\log\mathrm N_{\mathrm{abs}}(\mathfrak D_{F_x^\ast/\mathbb Q})}{[F_x^\ast:\mathbb Q]}.
$$

入力 `hcore` は `excCore_finite` を与える。ある基底変換の後でコア条件が成り立たないとき、$W$ のその点は例外点である。`AG` で $E_x$ を一点穿孔したオービ曲線と、符号作用によるその商を取る。コア条件は、$F_x$ から型宇宙 $0$ に属する標数零の体への任意の単位元を保つ体準同型に沿う基底変換の後で、商がオービ曲線のコアであることを要求する。例外点の集合は有限である。 [コア条件](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean#L32)

点の導手 $\gamma(x)$ は、$L_x$ の有限素点のうち $|\lambda|_v\ne1$ または $|\lambda-1|_v\ne1$ を満たすものについて、対応する極大イデアルの絶対ノルムの対数を足して $e_x$ で割った値である。$\gamma_\ell(x)$ を求めるには、剰余標数が $2$ とも $\ell$ とも異なる $M_x$ の有限素点 $v$ を選ぶ。$v$ の上に $F_x$ の素点が少なくとも一つあり、その上のすべての素点が $\mathcal B_x$ に属することを要求する。$F_x^\ast$ の有限素点のうち、その素点と選んだ $v$ の両方の上にある $F_x$ の素点が存在するものについて、対応する極大イデアルの絶対ノルムの対数を足す。その和を $[F_x^\ast:\mathbb Q]$ で割る。入力 `hge` と `hle` は、すべての $x\in U$ とすべての素数 $\ell\ge7$ に対し、それぞれ下界と上界を与える。

$$
\gamma_\ell(x)\le\gamma(x)\le\gamma_\ell(x)+\log(2\ell).
$$

フィールド `logCond_ge` と `logCond_le` はこれらの界を $W$ 上で使う。対数はすべて自然対数である。 [三脚体の導手](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean#L33)

`CurveInputs.toCorollary22Inputs` は `curve`、`arith`、`tate` から `localData` を計算する。`modRep` で `SL2Image` を定め、`sl2_of` から像に関する含意を与える。 [系 2.2 の利用箇所](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean#L142)
