# Tripod curve inputs

## English

### Constructor and local consumer

The platform declaration is `AbcAdaptation.Tripod.curveInputs`. The local P7 code calls `AbcAdaptation.Tripod.curveInputs_from_source`. Both take `P`, `K`, `d`, implicit `AG : AnabelianGeometry.{0}` and `TK : ℝ`, and proofs `CF`, `hcore`, `hN`, `hh`, and `hB`. Both return `CurveInputs tripodTheory AG K d`, with the 21 fields described below. [Platform constructor](platform/Def_AbcAdaptation_Reference_Iut_Tripod_CurveInputsAssembly.lean#L186) · [Local entry](../../../../Solutions/Source_TripodCurveInputsFromSource.lean#L40) · [P7 use](../../../../Solutions/Source_TripodP7.lean#L47)

The platform constructor takes four more proofs as arguments. The local entry supplies them when it calls `curveInputsOfSL2Image`. It supplies `torsionDegreeBound_three'` and `torsionDegreeBound_five'` for `hdeg3` and `hdeg5`. It supplies `logCondGe P` and `logCondLe P` for `hge` and `hle`. [Local assembly](../../../../Solutions/Source_TripodCurveInputs.lean#L26) · [Degree proofs](../../../../Solutions/Source_TripodTorsionBasis.lean#L43) · [Conductor proofs](../../../../Solutions/Source_TripodLogCond.lean#L188)

The platform `sl2_of` calls the imported `sl2Image`. The copy of that imported theorem in this workspace has a `sorry` body. The local entry fills the assembler's `hSL2` argument with the proof `sl2Image_from_source P`. The local assembler also uses the helper lemmas `curveInputs_deg_le`, `curveInputs_dmod_le`, and `curveInputs_logDiff_eq` for the corresponding fields. The platform constructor applies `deg_le`, `dmod_le`, and `logDiff_eq` in its field assignments. [Platform image declaration](../../../../Theorems/Thm_AbcAdaptation_Tripod_sl2Image.lean#L16) · [Local image proof](../../../../Solutions/Source_TripodCurveInputsFromSource.lean#L23) · [Local field proofs](../../../../Solutions/Source_TripodCurveInputsFieldArithmetic.lean#L21) · [Local moduli bound](../../../../Solutions/Source_TripodCurveInputsDmodField.lean#L20)

`CurveInputs.toCorollary22Inputs` builds `localData` from `curve`, `arith`, and `tate`. It fills `localData_height` and `localData_deg_le` from `height_eq` and `deg_le`. It builds `SL2Image` from `modRep` and uses `sl2_of` to establish it. The pointwise construction `pointThetaData` reads `dmod_le`, `logDiff_eq`, `logCond_ge`, and `logCond_le` directly from the curve bundle. [Corollary 2.2 conversion](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean#L142) · [Pointwise Θ-data](../../../../Solutions/Source_ReferenceIutPointThetaData.lean#L62)

### Points and curves

Let $U$ be the set of tripod points. Each $x\in U$ has a parameter $\lambda\in\overline{\mathbb Q}\setminus\{0,1\}$. Write $L_x=\mathbb Q(\lambda)$ and $e_x=[L_x:\mathbb Q]$. The input $K$ gives a finite set $V$ of rational primes containing $2$ and a real constant $c=K.c$. The set $S=K.\mathrm{set}$ requires both $|\log|\lambda|_v|\le c$ and $|\log|\lambda-1|_v|\le c$. The bounds apply at every infinite place of $L_x$ and every finite place with residue characteristic in $V$. The output uses $W=\{x\in S\mid e_x\le d\}$. [Compactly bounded set](../../../../Definitions/Def_AbcTripod.lean#L168)

The provider `P : CurveProviders` gives finiteness of the $3$- and $5$-torsion point sets for every parameter in $\overline{\mathbb Q}$. It also gives curve arithmetic and mod-$\ell$ representations at every $x\in U$. Let $C_n(\lambda)$ be the coordinates of nonsingular affine points on the Legendre equation $Y^2=X(X-1)(X-\lambda)$ killed by $n$. The identity contributes the empty set. The curve field $F_x$ adjoins $\lambda$, chosen square roots of $-1,\lambda,1-\lambda$, and $C_3(\lambda)\cup C_5(\lambda)$ to $\mathbb Q$. Finiteness of the coordinate sets makes $F_x$ a number field. Write $E_x/F_x$ for this Legendre curve and $M_x=\mathbb Q(j(E_x))$ for its moduli field. The curve data use $\overline{\mathbb Q}$ as the algebraic closure of $F_x$. [Provider](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviders.lean#L28) · [Field generators](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveOfFieldsData.lean#L35)

### `h`, `curve`, `arith`, `tate`, `modRep`, `height_eq`

For $x\in W$, `curve`, `arith`, and `tate` give `P.curve x`, `P.arith x`, and `P.tate x`. The arithmetic gives that $-1$ is a square in $F_x$. Each finite place has good or multiplicative reduction. All points killed by $6$ are rational over $F_x$. The extension $F_x/M_x$ is Galois with degree prime to each prime $\ell\ge7$. Finite places of $F_x$ lie above finite places of $M_x$ with the same residue characteristic. Over each odd-residue-characteristic place of $M_x$, multiplicative reduction at one place above it implies multiplicative reduction at all places above it. The arithmetic proves that the multiplicative places $\mathcal B_x$ form a finite set. It gives positive residue degrees $f(w)$ over $\mathbb Q$ and $\sum_{w\in\mathcal B_x,\ p(w)=r}f(w)\le[F_x:\mathbb Q]$ for every natural $r$, with $p(w)$ the residue characteristic. [Curve arithmetic](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveArithmetic.lean#L50)

For $w\in\mathcal B_x$, `P.tate x` uses classical choice for a Tate parameter $q_w$ and a uniformizer $\pi_w$ in the completion at $w$. The parameter satisfies $0<\|q_w\|_w<1$. Its Tate $j$-invariant equals the image of $j(E_x)$. The order $m(w)>0$ is the natural number with $\|q_w\|_w=\|\pi_w\|_w^{m(w)}$. The local data set $m(w)=0$ elsewhere. The field `h` is `P.h` on all of $U$, with

$$
h(x)=\frac{\sum_{w\in\mathcal B_x}m(w)f(w)\log p(w)}{[F_x:\mathbb Q]},
\qquad
h_2(x)=\frac{\sum_{w\in\mathcal B_x,\ p(w)=2}m(w)f(w)\log p(w)}{[F_x:\mathbb Q]}.
$$

The field `height_eq` identifies the local height with $h(x)$ by reflexivity. The term $h_2(x)$ is the contribution at $2$ from these same data. [Tate choices](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TateInputsSupply.lean#L196) · [Local height data](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalHeightDataAssembly.lean#L39)

For each $x\in W$ and each prime $\ell$, `modRep` uses `P.modRep x ℓ hℓ` with the primality proof `hℓ`. It supplies an additive identification $E_x[\ell]\simeq\mathbb F_\ell^2$. It gives $\rho_{x,\ell}\colon\operatorname{Gal}(\overline{\mathbb Q}/F_x)\to\mathrm{GL}_2(\mathbb F_\ell)$ with open kernel. The matrix action through this identification is the Galois action on the torsion. [Representation data](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveData.lean#L54)

### `deg_le`, `dmod_le`

Each torsion-degree proof for $n=3,5$ applies to every $x\in U$ and every finite intermediate field $L\subseteq\overline{\mathbb Q}$ containing $\lambda$. It gives

$$
[L(C_n(\lambda)):\mathbb Q]\le(n^2-1)(n^2-n)[L:\mathbb Q].
$$

The field `deg_le` gives $[F_x:\mathbb Q]\le552960d$ on $W$. The platform proof uses factors $8$, $48$, and $480$ for the three square roots, $3$-torsion, and $5$-torsion, respectively. Their product is $184320$. The declaration states the weaker bound with $552960$. The field `dmod_le` uses $M_x\subseteq L_x$ inside $F_x$ to give $[M_x:\mathbb Q]\le d$. [Torsion-degree property](platform/Def_AbcAdaptation_Reference_Iut_Tripod_CurveInputsAssembly.lean#L41) · [Curve-field degree](platform/Def_AbcAdaptation_Reference_Iut_Tripod_CurveInputsAssembly.lean#L95) · [Moduli-field degree](../../../../Solutions/Source_TripodCurveInputsDmodField.lean#L20)

### `htCan_equiv`, `northcott`, `B`, `B_nonneg`, `heightEq_two_le`

The height $h_{\mathrm{can}}$ is the relative logarithmic height of $\lambda$ in $L_x$ divided by $e_x$. The input `hh` gives two uniform additive bounds on $S$. There exist real constants $a_1,a_2$ with

$$
h(x)/6\le h_{\mathrm{can}}(x)+a_1,\qquad
h_{\mathrm{can}}(x)\le h(x)/6+a_2 .
$$

The field `htCan_equiv` stores these bounds. The input `hN` gives finiteness of $\{x\in U\mid e_x\le b,\ h_{\mathrm{can}}(x)\le H\}$ for every natural $b$ and real $H$. The second bound from `hh` gives the cutoff $H/6+a_2$ for $h_{\mathrm{can}}$. This proves `northcott`, the finiteness of $\{x\in W\mid h(x)\le H\}$ for each real $H$. [Platform Northcott comparison](platform/Def_AbcAdaptation_Reference_Iut_Tripod_CurveInputsAssembly.lean#L153) · [Local Northcott comparison](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_NorthcottComparison.lean#L21)

The field `B` is $\max(4c,0)$, and `B_nonneg` proves $0\le B$. The input `hB` gives $h_2(x)\le B$ on $S$. The field `heightEq_two_le` uses this on $W$. [Field assignments](platform/Def_AbcAdaptation_Reference_Iut_Tripod_CurveInputsAssembly.lean#L204)

### `HasCyclicSubgroup`, `TK`, `cyclic_bound`, `sl2_of`

The field `HasCyclicSubgroup` is the predicate $G(x,\ell)$ on $U\times\mathbb N$. It asserts that $E_x(\overline{\mathbb Q})$ has an additive subgroup of natural cardinality $\ell$ stable under $\operatorname{Gal}(\overline{\mathbb Q}/F_x)$. The field `TK` stores the real $T_K$. The input `CF` supplies `cyclic_bound` on $W$ for each prime $\ell\ge7$. When $\ell\nmid m(w)$ at every $w\in\mathcal B_x$ and $G(x,\ell)$ holds, it gives

$$
\frac{\ell-2}{24}\bigl(h(x)-h_2(x)\bigr)\le 2\log\ell+T_K.
$$

The image theorem used by `sl2_of` applies on $U$, and the field uses it on $W$. It requires a prime $\ell\ge5$ and these three conditions.

- (P2) $\ell\nmid m(w)$ for every $w\in\mathcal B_x$.
- (P4) $\neg G(x,\ell)$, so there is no Galois-stable subgroup of order $\ell$.
- (P5) Some $w\in\mathcal B_x$ has $p(w)\ne2$ and $p(w)\ne\ell$.

The conclusion is that every determinant-one matrix over $\mathbb F_\ell$, viewed in $\mathrm{GL}_2(\mathbb F_\ell)$, belongs to the image of $\rho_{x,\ell}$. In the local proof, $m(w)$ is the order of the Tate parameter from `P.tate x`, and the representation is the one from `P.modRep x ℓ hℓ`. [Cyclic and image hypotheses](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts.lean#L24) · [Local proof](../../../../Solutions/Source_TripodCurveInputsFromSource.lean#L23)

### `logDiff_eq`, `excCore_finite`, `logCond_ge`, `logCond_le`

The tripodal field $F_{\mathrm{tpd},x}$ is generated by $j(E_x)$ and the first coordinates of the rational affine $2$-torsion points over $F_x$. These coordinates are $0,1,\lambda$. The tripodal field identifies with $L_x$ over $\mathbb Q$. The field `logDiff_eq` identifies the point's normalized log absolute discriminant with the normalized log norm of the different ideal of $F_{\mathrm{tpd},x}$ on $W$.

$$
\frac{\log|\operatorname{disc}(L_x)|}{e_x}
=\frac{\log\mathrm N_{\mathrm{abs}}\bigl(\mathfrak D_{F_{\mathrm{tpd},x}/\mathbb Q}\bigr)}
{[F_{\mathrm{tpd},x}:\mathbb Q]}.
$$

The input `hcore` gives `excCore_finite`. It requires only finitely many points of $W$ where the core property fails after some characteristic-zero base change. The property asks that the sign quotient of the once-punctured orbicurve be a core of that orbicurve after base change. It quantifies over every unital field map from $F_x$ to a characteristic-zero field in universe $0$. [Tripodal field](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FieldIdentification.lean#L81) · [Core predicate](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean#L32)

The point conductor $\gamma(x)$ is the sum of log absolute norms of the maximal ideals at finite places of $L_x$ where $\lambda$ or $\lambda-1$ is not a local unit, divided by $e_x$. For $\gamma_\ell(x)$, select the finite places of $M_x$ of residue characteristic different from $2,\ell$ with a nonempty fiber of finite places of $F_x$. Every place in the fiber must have multiplicative reduction. Sum the log absolute norms of the maximal ideals at the qualifying finite places of $F_{\mathrm{tpd},x}$. Each must have an $F_x$ place above it and one of the selected moduli places. Divide by $[F_{\mathrm{tpd},x}:\mathbb Q]$. The inputs `hge` and `hle` give the respective inequalities for every $x\in U$ and each prime $\ell\ge7$.

$$
\gamma_\ell(x)\le\gamma(x)\le\gamma_\ell(x)+\log(2\ell).
$$

The fields `logCond_ge` and `logCond_le` use those inequalities on $W$. [Conductor definitions](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean#L33) · [Hypotheses and fields](platform/Def_AbcAdaptation_Reference_Iut_Tripod_CurveInputsAssembly.lean#L186)

## 简体中文

### 构造器与本地消费入口

平台声明是 `AbcAdaptation.Tripod.curveInputs`。本地 P7 代码调用 `AbcAdaptation.Tripod.curveInputs_from_source`。两者都接收 `P`、`K`、`d`、隐式参数 `AG : AnabelianGeometry.{0}` 和 `TK : ℝ`，以及证明 `CF`、`hcore`、`hN`、`hh` 和 `hB`。两者均返回 `CurveInputs tripodTheory AG K d`，含下述 21 个字段。 [平台构造器](platform/Def_AbcAdaptation_Reference_Iut_Tripod_CurveInputsAssembly.lean#L186) · [本地入口](../../../../Solutions/Source_TripodCurveInputsFromSource.lean#L40) · [P7 调用](../../../../Solutions/Source_TripodP7.lean#L47)

平台构造器另行接收四项证明。本地入口在调用 `curveInputsOfSL2Image` 时填入这四项。对 `hdeg3` 和 `hdeg5` 分别传入 `torsionDegreeBound_three'` 和 `torsionDegreeBound_five'`，对 `hge` 和 `hle` 分别传入 `logCondGe P` 和 `logCondLe P`。 [本地装配](../../../../Solutions/Source_TripodCurveInputs.lean#L26) · [次数界证明](../../../../Solutions/Source_TripodTorsionBasis.lean#L43) · [导子界证明](../../../../Solutions/Source_TripodLogCond.lean#L188)

平台的 `sl2_of` 调用导入的 `sl2Image`。当前工作区中，这个被导入定理的正文是 `sorry`。本地入口把证明 `sl2Image_from_source P` 传给装配函数的 `hSL2` 参数。本地装配还以辅助引理 `curveInputs_deg_le`、`curveInputs_dmod_le` 和 `curveInputs_logDiff_eq` 填写相应字段。平台构造器在字段赋值中直接调用 `deg_le`、`dmod_le` 和 `logDiff_eq`。 [平台像定理声明](../../../../Theorems/Thm_AbcAdaptation_Tripod_sl2Image.lean#L16) · [本地像证明](../../../../Solutions/Source_TripodCurveInputsFromSource.lean#L23) · [本地字段证明](../../../../Solutions/Source_TripodCurveInputsFieldArithmetic.lean#L21) · [本地模域次数界](../../../../Solutions/Source_TripodCurveInputsDmodField.lean#L20)

`CurveInputs.toCorollary22Inputs` 从 `curve`、`arith` 和 `tate` 构造 `localData`，用 `height_eq` 和 `deg_le` 填入 `localData_height` 和 `localData_deg_le`，并从 `modRep` 定义 `SL2Image`、用 `sl2_of` 证明它。逐点构造 `pointThetaData` 直接从曲线输入读取 `dmod_le`、`logDiff_eq`、`logCond_ge` 和 `logCond_le`。 [推论 2.2 转换](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean#L142) · [逐点 Θ 数据](../../../../Solutions/Source_ReferenceIutPointThetaData.lean#L62)

### 点与曲线

令 $U$ 为三足曲线点集。点 $x\in U$ 的参数为 $\lambda\in\overline{\mathbb Q}\setminus\{0,1\}$。记 $L_x=\mathbb Q(\lambda)$、$e_x=[L_x:\mathbb Q]$。输入 $K$ 给出含 $2$ 的有理素数有限集 $V$ 与实数常数 $c=K.c$。集合 $S=K.\mathrm{set}$ 要求 $|\log|\lambda|_v|\le c$ 和 $|\log|\lambda-1|_v|\le c$ 同时成立。检验范围为 $L_x$ 的每个无穷位和剩余特征在 $V$ 中的每个有限位。输出使用 $W=\{x\in S\mid e_x\le d\}$。 [紧有界集合](../../../../Definitions/Def_AbcTripod.lean#L168)

`P : CurveProviders` 给出对 $\overline{\mathbb Q}$ 中每个参数均成立的 $3$-挠点集和 $5$-挠点集有限性，并给出每个 $x\in U$ 的曲线算术和模 $\ell$ 表示。令 $C_n(\lambda)$ 为 Legendre 方程 $Y^2=X(X-1)(X-\lambda)$ 上被 $n$ 倍消去的非奇异仿射点的坐标集。单位元对应空集。在 $\mathbb Q$ 上添入 $\lambda$、$-1,\lambda,1-\lambda$ 的选定平方根和 $C_3(\lambda)\cup C_5(\lambda)$，得到曲线域 $F_x$。坐标集的有限性保证 $F_x$ 是数域。记 $E_x/F_x$ 为此 Legendre 曲线，$M_x=\mathbb Q(j(E_x))$ 为其模域。曲线数据以 $\overline{\mathbb Q}$ 为 $F_x$ 的代数闭包。 [曲线数据提供者](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviders.lean#L28) · [域生成元](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveOfFieldsData.lean#L35)

### `h`、`curve`、`arith`、`tate`、`modRep`、`height_eq`

对 $x\in W$，`curve`、`arith` 和 `tate` 分别给出 `P.curve x`、`P.arith x` 和 `P.tate x`。曲线算术给出 $-1$ 在 $F_x$ 中为平方。各有限位处为良好约化或乘法约化。被 $6$ 倍消去的点均在 $F_x$ 上有理。扩张 $F_x/M_x$ 是伽罗瓦扩张，其次数与每个素数 $\ell\ge7$ 互素。$F_x$ 的有限位位于 $M_x$ 中剩余特征相同的有限位之上。对 $M_x$ 中每个奇剩余特征位，其上一个位有乘法约化就推出其上所有位都有乘法约化。算术数据证明乘法约化位集 $\mathcal B_x$ 有限，相对于 $\mathbb Q$ 的剩余次数 $f(w)$ 为正，且对每个自然数 $r$ 均有 $\sum_{w\in\mathcal B_x,\ p(w)=r}f(w)\le[F_x:\mathbb Q]$，其中 $p(w)$ 是剩余特征。 [曲线算术](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveArithmetic.lean#L50)

对 $w\in\mathcal B_x$，`P.tate x` 用经典选择在 $w$ 处的完备化中取 Tate 参数 $q_w$ 与一致化参数 $\pi_w$。该参数满足 $0<\|q_w\|_w<1$，其 Tate $j$-不变量等于 $j(E_x)$ 的像。阶数 $m(w)>0$ 是满足 $\|q_w\|_w=\|\pi_w\|_w^{m(w)}$ 的自然数。局部数据在其他位上取 $m(w)=0$。字段 `h` 采用整个 $U$ 上的 `P.h`，其公式为

$$
h(x)=\frac{\sum_{w\in\mathcal B_x}m(w)f(w)\log p(w)}{[F_x:\mathbb Q]},
\qquad
h_2(x)=\frac{\sum_{w\in\mathcal B_x,\ p(w)=2}m(w)f(w)\log p(w)}{[F_x:\mathbb Q]}.
$$

字段 `height_eq` 以自反性证明局部高度等于 $h(x)$。$h_2(x)$ 是同一份数据在 $2$ 处的贡献。 [Tate 数据的选择](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TateInputsSupply.lean#L196) · [局部高度数据](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalHeightDataAssembly.lean#L39)

对每个 $x\in W$ 和每个素数 $\ell$，字段 `modRep` 用素性证明 `hℓ` 调用 `P.modRep x ℓ hℓ`。所得数据给出加法群同构 $E_x[\ell]\simeq\mathbb F_\ell^2$，以及开核同态 $\rho_{x,\ell}\colon\operatorname{Gal}(\overline{\mathbb Q}/F_x)\to\mathrm{GL}_2(\mathbb F_\ell)$。该同构下的矩阵作用给出挠点上的伽罗瓦作用。 [表示数据](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveData.lean#L54)

### `deg_le`、`dmod_le`

$n=3,5$ 时的两项挠点次数界均适用于每个 $x\in U$ 和每个包含 $\lambda$ 的有限次中间域 $L\subseteq\overline{\mathbb Q}$。不等式为

$$
[L(C_n(\lambda)):\mathbb Q]\le(n^2-1)(n^2-n)[L:\mathbb Q].
$$

字段 `deg_le` 在 $W$ 上给出 $[F_x:\mathbb Q]\le552960d$。平台证明对三个平方根、$3$-挠点和 $5$-挠点分别使用因子 $8$、$48$ 和 $480$。它们的乘积是 $184320$。Lean 声明用 $552960$ 给出较宽的上界。字段 `dmod_le` 用 $F_x$ 内部的包含关系 $M_x\subseteq L_x$ 得到 $[M_x:\mathbb Q]\le d$。 [挠点次数条件](platform/Def_AbcAdaptation_Reference_Iut_Tripod_CurveInputsAssembly.lean#L41) · [曲线域次数](platform/Def_AbcAdaptation_Reference_Iut_Tripod_CurveInputsAssembly.lean#L95) · [模域次数](../../../../Solutions/Source_TripodCurveInputsDmodField.lean#L20)

### `htCan_equiv`、`northcott`、`B`、`B_nonneg`、`heightEq_two_le`

高度 $h_{\mathrm{can}}$ 是 $\lambda$ 在 $L_x$ 中的相对对数高度除以 $e_x$。输入 `hh` 给出 $S$ 上两个一致的加法误差界，即存在实数 $a_1,a_2$ 使

$$
h(x)/6\le h_{\mathrm{can}}(x)+a_1,\qquad
h_{\mathrm{can}}(x)\le h(x)/6+a_2 .
$$

字段 `htCan_equiv` 保存这两个界。输入 `hN` 给出对每个自然数 $b$ 和每个实数 $H$，$\{x\in U\mid e_x\le b,\ h_{\mathrm{can}}(x)\le H\}$ 有限。`hh` 的第二个界给出 $h_{\mathrm{can}}$ 的阈值 $H/6+a_2$，从而得到 `northcott`，即对每个实数 $H$，$\{x\in W\mid h(x)\le H\}$ 有限。 [平台 Northcott 比较](platform/Def_AbcAdaptation_Reference_Iut_Tripod_CurveInputsAssembly.lean#L153) · [本地 Northcott 比较](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_NorthcottComparison.lean#L21)

字段 `B` 取 $\max(4c,0)$，`B_nonneg` 证明 $0\le B$。输入 `hB` 在 $S$ 上给出 $h_2(x)\le B$。`heightEq_two_le` 在 $W$ 上使用此界。 [字段赋值](platform/Def_AbcAdaptation_Reference_Iut_Tripod_CurveInputsAssembly.lean#L204)

### `HasCyclicSubgroup`、`TK`、`cyclic_bound`、`sl2_of`

字段 `HasCyclicSubgroup` 是 $U\times\mathbb N$ 上的谓词 $G(x,\ell)$。它断言 $E_x(\overline{\mathbb Q})$ 有一个自然数基数为 $\ell$ 的加法子群，且该子群在 $\operatorname{Gal}(\overline{\mathbb Q}/F_x)$ 的作用下稳定。字段 `TK` 保存实数 $T_K$。输入 `CF` 给出 $W$ 上对每个素数 $\ell\ge7$ 成立的 `cyclic_bound`。若对每个 $w\in\mathcal B_x$ 都有 $\ell\nmid m(w)$ 且 $G(x,\ell)$ 成立，则

$$
\frac{\ell-2}{24}\bigl(h(x)-h_2(x)\bigr)\le 2\log\ell+T_K.
$$

`sl2_of` 使用的像定理在 $U$ 上成立，字段将它用于 $W$。定理要求素数 $\ell\ge5$ 及以下三个条件。

- (P2) 对每个 $w\in\mathcal B_x$，有 $\ell\nmid m(w)$。
- (P4) $\neg G(x,\ell)$，即不存在阶为 $\ell$ 的伽罗瓦稳定子群。
- (P5) 存在 $w\in\mathcal B_x$，同时满足 $p(w)\ne2$ 和 $p(w)\ne\ell$。

结论为 $\mathbb F_\ell$ 上每个行列式为 $1$ 的矩阵作为 $\mathrm{GL}_2(\mathbb F_\ell)$ 的元素，都属于 $\rho_{x,\ell}$ 的像。本地证明中的 $m(w)$ 取自 `P.tate x`，表示取自 `P.modRep x ℓ hℓ`。 [循环子群与像条件](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts.lean#L24) · [本地证明](../../../../Solutions/Source_TripodCurveInputsFromSource.lean#L23)

### `logDiff_eq`、`excCore_finite`、`logCond_ge`、`logCond_le`

三足域 $F_{\mathrm{tpd},x}$ 由 $j(E_x)$ 和 $F_x$ 上有理的仿射 $2$-挠点的第一坐标生成。这些坐标为 $0,1,\lambda$，所以该域在 $\mathbb Q$ 上与 $L_x$ 等同。字段 `logDiff_eq` 在 $W$ 上将点的归一化绝对判别式对数与 $F_{\mathrm{tpd},x}$ 的归一化不同理想范数对数等同。

$$
\frac{\log|\operatorname{disc}(L_x)|}{e_x}
=\frac{\log\mathrm N_{\mathrm{abs}}\bigl(\mathfrak D_{F_{\mathrm{tpd},x}/\mathbb Q}\bigr)}
{[F_{\mathrm{tpd},x}:\mathbb Q]}.
$$

输入 `hcore` 给出 `excCore_finite`。它要求 $W$ 中只有有限多个点的核心条件在某次特征零基变换后失败。核心条件断言去一点所得轨形曲线经符号作用取商后，该商在基变换后是原轨形曲线基变换后的核心。所用映射遍历从 $F_x$ 到类型宇宙 $0$ 中特征零域的每个保单位元的域同态。 [三足域](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FieldIdentification.lean#L81) · [核心谓词](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean#L32)

点导子 $\gamma(x)$ 对 $L_x$ 中 $\lambda$ 或 $\lambda-1$ 不是局部单位的有限位求和。每项为相应极大理想绝对范数的对数，和除以 $e_x$。计算 $\gamma_\ell(x)$ 时，在 $M_x$ 中选取剩余特征异于 $2,\ell$ 的有限位，要求其上存在 $F_x$ 的有限位且所有这些位都为乘法约化。在 $F_{\mathrm{tpd},x}$ 的有限位中，计入与某个选定模域位同在一个 $F_x$ 有限位之下的位。取这些位的极大理想绝对范数的对数之和，除以 $[F_{\mathrm{tpd},x}:\mathbb Q]$。输入 `hge` 和 `hle` 分别对所有 $x\in U$ 和每个素数 $\ell\ge7$ 给出下列两边的不等式。

$$
\gamma_\ell(x)\le\gamma(x)\le\gamma_\ell(x)+\log(2\ell).
$$

字段 `logCond_ge` 和 `logCond_le` 在 $W$ 上使用上述不等式。 [导子的定义](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean#L33) · [假设与字段](platform/Def_AbcAdaptation_Reference_Iut_Tripod_CurveInputsAssembly.lean#L186)

## 日本語

### 構成子とローカルの利用箇所

プラットフォームの宣言は `AbcAdaptation.Tripod.curveInputs` である。ローカルの P7 のコードは `AbcAdaptation.Tripod.curveInputs_from_source` を呼ぶ。どちらも `P`、`K`、`d`、暗黙の引数 `AG : AnabelianGeometry.{0}` と `TK : ℝ`、および証明 `CF`、`hcore`、`hN`、`hh`、`hB` を受け取る。戻り値は以下の 21 フィールドを持つ `CurveInputs tripodTheory AG K d` である。 [プラットフォームの構成子](platform/Def_AbcAdaptation_Reference_Iut_Tripod_CurveInputsAssembly.lean#L186) · [ローカルの入口](../../../../Solutions/Source_TripodCurveInputsFromSource.lean#L40) · [P7 の利用箇所](../../../../Solutions/Source_TripodP7.lean#L47)

プラットフォームの構成子はさらに四つの証明を受け取る。ローカルの入口は `curveInputsOfSL2Image` を呼ぶ際にその四つを与える。`hdeg3` と `hdeg5` にはそれぞれ `torsionDegreeBound_three'` と `torsionDegreeBound_five'` を渡す。`hge` と `hle` にはそれぞれ `logCondGe P` と `logCondLe P` を渡す。 [ローカルの構成](../../../../Solutions/Source_TripodCurveInputs.lean#L26) · [次数の証明](../../../../Solutions/Source_TripodTorsionBasis.lean#L43) · [導手の証明](../../../../Solutions/Source_TripodLogCond.lean#L188)

プラットフォームの `sl2_of` はインポートした `sl2Image` を呼ぶ。このワークスペースにあるインポート先の定理の本体は `sorry` である。ローカルの入口は構成関数の `hSL2` 引数に証明 `sl2Image_from_source P` を渡す。ローカルの構成関数は、対応するフィールドに補題 `curveInputs_deg_le`、`curveInputs_dmod_le`、`curveInputs_logDiff_eq` を使う。プラットフォームの構成子は、フィールドの代入で `deg_le`、`dmod_le`、`logDiff_eq` を直接使う。 [プラットフォームの像定理](../../../../Theorems/Thm_AbcAdaptation_Tripod_sl2Image.lean#L16) · [ローカルの像の証明](../../../../Solutions/Source_TripodCurveInputsFromSource.lean#L23) · [ローカルのフィールドの証明](../../../../Solutions/Source_TripodCurveInputsFieldArithmetic.lean#L21) · [モジュライ体の次数の証明](../../../../Solutions/Source_TripodCurveInputsDmodField.lean#L20)

`CurveInputs.toCorollary22Inputs` は `curve`、`arith`、`tate` から `localData` を作る。`height_eq` と `deg_le` から `localData_height` と `localData_deg_le` を得る。`modRep` から `SL2Image` を定め、`sl2_of` でその成立を示す。点ごとの構成 `pointThetaData` は `dmod_le`、`logDiff_eq`、`logCond_ge`、`logCond_le` を曲線のデータから直接読む。 [系 2.2 への変換](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean#L142) · [点ごとの Θ データ](../../../../Solutions/Source_ReferenceIutPointThetaData.lean#L62)

### 点と曲線

$U$ を三脚曲線の点の集合とする。点 $x\in U$ のパラメータは $\lambda\in\overline{\mathbb Q}\setminus\{0,1\}$ である。$L_x=\mathbb Q(\lambda)$、$e_x=[L_x:\mathbb Q]$ と書く。入力 $K$ は、$2$ を含む有理素数の有限集合 $V$ と実定数 $c=K.c$ を与える。集合 $S=K.\mathrm{set}$ では $|\log|\lambda|_v|\le c$ と $|\log|\lambda-1|_v|\le c$ の両方を要求する。$L_x$ の各無限素点と、剰余標数が $V$ に属する各有限素点でこれらを調べる。出力は $W=\{x\in S\mid e_x\le d\}$ を使う。 [コンパクト有界集合](../../../../Definitions/Def_AbcTripod.lean#L168)

`P : CurveProviders` は、$\overline{\mathbb Q}$ の各パラメータで $3$-ねじれ点の集合と $5$-ねじれ点の集合が有限であることを与える。また、各 $x\in U$ の曲線の算術と mod $\ell$ 表現を与える。Legendre 方程式 $Y^2=X(X-1)(X-\lambda)$ 上で、$n$ 倍が零となる非特異なアフィン点の座標集合を $C_n(\lambda)$ とする。単位元に対応する座標集合は空である。$\mathbb Q$ に $\lambda$、$-1,\lambda,1-\lambda$ の選んだ平方根と $C_3(\lambda)\cup C_5(\lambda)$ を添加して曲線の体 $F_x$ を得る。座標集合の有限性により $F_x$ は数体である。この Legendre 曲線を $E_x/F_x$ とし、そのモジュライ体を $M_x=\mathbb Q(j(E_x))$ とする。曲線のデータでは $\overline{\mathbb Q}$ を $F_x$ の代数閉包とする。 [供給元](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveProviders.lean#L28) · [体の生成元](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveOfFieldsData.lean#L35)

### `h`、`curve`、`arith`、`tate`、`modRep`、`height_eq`

$x\in W$ に対し、`curve`、`arith`、`tate` はそれぞれ `P.curve x`、`P.arith x`、`P.tate x` を与える。算術データは $-1$ が $F_x$ の平方元であることを与える。各有限素点で良還元または乗法的還元を持つ。$6$ 倍が零となる点はすべて $F_x$ 上有理である。$F_x/M_x$ は、拡大次数が各素数 $\ell\ge7$ と互いに素なガロア拡大である。$F_x$ の各有限素点は剰余標数が等しい $M_x$ の有限素点の上にある。$M_x$ の各奇剰余標数の素点について、その上の一つの素点で乗法的還元を持てば、その上のすべての素点で乗法的還元を持つ。乗法的還元を持つ素点の集合 $\mathcal B_x$ は有限である。$\mathbb Q$ 上の剰余次数 $f(w)$ は正であり、剰余標数を $p(w)$ とすると各自然数 $r$ で $\sum_{w\in\mathcal B_x,\ p(w)=r}f(w)\le[F_x:\mathbb Q]$ が成り立つ。 [曲線の算術](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveArithmetic.lean#L50)

$w\in\mathcal B_x$ に対して、`P.tate x` は古典的選択により $w$ での完備化のテイトパラメータ $q_w$ と素元 $\pi_w$ を選ぶ。このパラメータは $0<\|q_w\|_w<1$ を満たし、テイト $j$-不変量は $j(E_x)$ の像に等しい。位数 $m(w)>0$ は $\|q_w\|_w=\|\pi_w\|_w^{m(w)}$ を満たす自然数である。局所データでは他の素点で $m(w)=0$ とする。`h` は $U$ 全体での `P.h` であり、式は次のとおりである。

$$
h(x)=\frac{\sum_{w\in\mathcal B_x}m(w)f(w)\log p(w)}{[F_x:\mathbb Q]},
\qquad
h_2(x)=\frac{\sum_{w\in\mathcal B_x,\ p(w)=2}m(w)f(w)\log p(w)}{[F_x:\mathbb Q]}.
$$

`height_eq` は局所高さと $h(x)$ の等式を反射性で示す。$h_2(x)$ は同じデータにおける $2$ での寄与である。 [テイトデータの選択](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TateInputsSupply.lean#L196) · [局所高さデータ](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalHeightDataAssembly.lean#L39)

各 $x\in W$ と各素数 $\ell$ に対し、`modRep` は素数性の証明 `hℓ` を用いて `P.modRep x ℓ hℓ` を使う。これは加法群同型 $E_x[\ell]\simeq\mathbb F_\ell^2$ と、開核を持つ準同型 $\rho_{x,\ell}\colon\operatorname{Gal}(\overline{\mathbb Q}/F_x)\to\mathrm{GL}_2(\mathbb F_\ell)$ を与える。この同型を通じた行列作用はねじれ点へのガロア作用を表す。 [表現のデータ](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveData.lean#L54)

### `deg_le`、`dmod_le`

$n=3,5$ それぞれのねじれ点の次数の証明は、各 $x\in U$ と、$\lambda$ を含む各有限次中間体 $L\subseteq\overline{\mathbb Q}$ に適用する。得られる不等式は次である。

$$
[L(C_n(\lambda)):\mathbb Q]\le(n^2-1)(n^2-n)[L:\mathbb Q].
$$

`deg_le` は $W$ 上で $[F_x:\mathbb Q]\le552960d$ を与える。プラットフォームの証明は、三つの平方根、$3$-ねじれ点、$5$-ねじれ点についてそれぞれ係数 $8$、$48$、$480$ を使う。積は $184320$ である。Lean の宣言では $552960$ による緩い上界を使う。`dmod_le` は $F_x$ の中での包含関係 $M_x\subseteq L_x$ から $[M_x:\mathbb Q]\le d$ を得る。 [ねじれ点の次数の条件](platform/Def_AbcAdaptation_Reference_Iut_Tripod_CurveInputsAssembly.lean#L41) · [曲線の体の次数](platform/Def_AbcAdaptation_Reference_Iut_Tripod_CurveInputsAssembly.lean#L95) · [モジュライ体の次数](../../../../Solutions/Source_TripodCurveInputsDmodField.lean#L20)

### `htCan_equiv`、`northcott`、`B`、`B_nonneg`、`heightEq_two_le`

高さ $h_{\mathrm{can}}$ は、$L_x$ における $\lambda$ の相対対数高さを $e_x$ で割った値である。入力 `hh` は $S$ 上の一様な加法誤差の上界を二つ与える。実定数 $a_1,a_2$ が存在し、次が成り立つ。

$$
h(x)/6\le h_{\mathrm{can}}(x)+a_1,\qquad
h_{\mathrm{can}}(x)\le h(x)/6+a_2 .
$$

`htCan_equiv` はこれらの上界を記録する。入力 `hN` は、各自然数 $b$ と各実数 $H$ について $\{x\in U\mid e_x\le b,\ h_{\mathrm{can}}(x)\le H\}$ が有限であることを与える。`hh` の二番目の上界から $h_{\mathrm{can}}$ の上界に $H/6+a_2$ を使う。これにより、各実数 $H$ で $\{x\in W\mid h(x)\le H\}$ が有限であることを示す `northcott` が得られる。 [プラットフォームの Northcott 比較](platform/Def_AbcAdaptation_Reference_Iut_Tripod_CurveInputsAssembly.lean#L153) · [ローカルの Northcott 比較](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_NorthcottComparison.lean#L21)

`B` は $\max(4c,0)$ であり、`B_nonneg` は $0\le B$ を示す。入力 `hB` は $S$ 上で $h_2(x)\le B$ を与える。`heightEq_two_le` はこの上界を $W$ 上で使う。 [フィールドの代入](platform/Def_AbcAdaptation_Reference_Iut_Tripod_CurveInputsAssembly.lean#L204)

### `HasCyclicSubgroup`、`TK`、`cyclic_bound`、`sl2_of`

`HasCyclicSubgroup` は $U\times\mathbb N$ 上の述語 $G(x,\ell)$ である。$E_x(\overline{\mathbb Q})$ の加法部分群で、自然数値の濃度が $\ell$ であり、$\operatorname{Gal}(\overline{\mathbb Q}/F_x)$ の作用で安定なものが存在することをいう。`TK` は実数 $T_K$ を記録する。入力 `CF` は $W$ 上で各素数 $\ell\ge7$ について `cyclic_bound` を与える。各 $w\in\mathcal B_x$ で $\ell\nmid m(w)$ が成り立ち、$G(x,\ell)$ が成り立つなら、次を得る。

$$
\frac{\ell-2}{24}\bigl(h(x)-h_2(x)\bigr)\le 2\log\ell+T_K.
$$

`sl2_of` が使う像定理は $U$ 上で成り立ち、このフィールドはそれを $W$ 上で使う。定理は素数 $\ell\ge5$ と以下の三条件を要求する。

- (P2) 各 $w\in\mathcal B_x$ で $\ell\nmid m(w)$ が成り立つ。
- (P4) $\neg G(x,\ell)$。位数 $\ell$ のガロア安定な部分群は存在しない。
- (P5) $p(w)\ne2$ と $p(w)\ne\ell$ をともに満たす $w\in\mathcal B_x$ が存在する。

結論は、$\mathbb F_\ell$ 上の行列式 $1$ の各行列が、$\mathrm{GL}_2(\mathbb F_\ell)$ の元として $\rho_{x,\ell}$ の像に属することである。ローカルの証明では、$m(w)$ は `P.tate x` から取り、表現は `P.modRep x ℓ hℓ` から取る。 [巡回部分群と像の条件](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts.lean#L24) · [ローカルの証明](../../../../Solutions/Source_TripodCurveInputsFromSource.lean#L23)

### `logDiff_eq`、`excCore_finite`、`logCond_ge`、`logCond_le`

三脚体 $F_{\mathrm{tpd},x}$ は、$j(E_x)$ と $F_x$ 上有理なアフィン $2$-ねじれ点の第一座標で生成する。これらの座標は $0,1,\lambda$ なので、三脚体は $\mathbb Q$ 上で $L_x$ と同一視できる。`logDiff_eq` は、点の正規化した絶対判別式の対数が $F_{\mathrm{tpd},x}$ の相対差積イデアルの絶対ノルムの正規化対数に等しいことを $W$ 上で与える。

$$
\frac{\log|\operatorname{disc}(L_x)|}{e_x}
=\frac{\log\mathrm N_{\mathrm{abs}}\bigl(\mathfrak D_{F_{\mathrm{tpd},x}/\mathbb Q}\bigr)}
{[F_{\mathrm{tpd},x}:\mathbb Q]}.
$$

入力 `hcore` は `excCore_finite` を与える。これは、ある標数零の基底変換の後でコア条件が成り立たない $W$ の点が有限個であることを要求する。コア条件は、一点穿孔したオービ曲線を符号作用で割った商が、基底変換の後に元のオービ曲線の基底変換のコアであるという条件である。$F_x$ から型宇宙 $0$ の標数零の体へのすべての単位元を保つ体準同型を考える。 [三脚体](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FieldIdentification.lean#L81) · [コア述語](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean#L32)

点の導手 $\gamma(x)$ は、$\lambda$ または $\lambda-1$ が局所単元でない $L_x$ の有限素点で、対応する極大イデアルの絶対ノルムの対数を足し、$e_x$ で割った値である。$\gamma_\ell(x)$ では、剰余標数が $2,\ell$ と異なる $M_x$ の有限素点を選ぶ。その上に $F_x$ の有限素点が存在し、そのすべてで乗法的還元を持つことを要求する。$F_{\mathrm{tpd},x}$ の有限素点のうち、その素点と選んだモジュライ体の素点の両方の上に $F_x$ の有限素点が存在するものを数える。対応する極大イデアルの絶対ノルムの対数を足し、$[F_{\mathrm{tpd},x}:\mathbb Q]$ で割る。入力 `hge` と `hle` は、全ての $x\in U$ と各素数 $\ell\ge7$ についてそれぞれ次の不等式を与える。

$$
\gamma_\ell(x)\le\gamma(x)\le\gamma_\ell(x)+\log(2\ell).
$$

`logCond_ge` と `logCond_le` はその不等式を $W$ 上で使う。 [導手の定義](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean#L33) · [仮定とフィールド](platform/Def_AbcAdaptation_Reference_Iut_Tripod_CurveInputsAssembly.lean#L186)
