# CanLift · 有理函数的局部形式与极点

$$
f,N,D,H,K,R\in\mathbb C[X],\qquad c\in\mathbb C,\qquad
U=\{x\in\mathbb C\mid f(x)\ne 0\},\qquad G(x)=\frac{N(x)}{D(x)}.
$$

| `RatCert` 字段 / Fields / フィールド | 条件 / Conditions / 条件 |
| --- | --- |
| `c_ne`, `D_ne`, `deg` | $c\ne0$, $D\ne0$, $\deg D<\deg N$ |
| `hN`, `hK`, `hcrit` | $N=C(c)H^3$, $N-1728D=C(c)K^2$, $N'D-ND'=RH^2K$ |
| `f_dvd_D`, `D_dvd_f`, `R_dvd_f` | $D=fq_f$, $C(d_D)f^6=Dq_D$, $C(d_R)f^6=Rq_R$ |
| `H_cop`, `K_cop` | $a_H H+b_H f=C(d_H)$, $a_K K+b_K f=C(d_K)$ |
| `H_sqf`, `K_sqf` | $a_{H'} H'+b_{H'}H=C(d_{H'})$, $a_{K'} K'+b_{K'}K=C(d_{K'})$ |

## 中文

### 多项式证书

表中的 $C(d)$ 表示常数多项式，撇号表示多项式导数，次数对应 Lean 的 `natDegree`。后三行中的 $q$、$a$、$b$ 是存在的多项式见证，各个 $d$ 是存在的非零复数。给定这份 `RatCert`，对每个 $x\in\mathbb C$，`D_eval_eq_zero_iff` 给出 $D(x)=0$ 当且仅当 $f(x)=0$。在 $f$ 的根上，对 $H$ 与 $f$ 的 Bézout 等式求值可得 $H(x)\ne0$，故 `N_eval_ne` 给出 $N(x)\ne0$。Lean 的除法在这些点给出 $G(x)=0$。

### 有限值及其纤维

$G$ 在 $U$ 上复可微，并且在 $U$ 的每个点解析。对任意 $x\in U$，$G(x)=0$ 等价于 $H(x)=0$，而 $G(x)=1728$ 等价于 $K(x)=0$。`hasLocalForm` 给出一条在 $x$ 处解析的局部坐标 $g$，满足 $g(x)=0$、$g'(x)\ne0$，且在 $x$ 的某个邻域内有 $G(y)=G(x)+g(y)^n$。这里 $n=\operatorname{sig}(G(x))$，在 $G(x)=0$ 时为 $3$，在 $G(x)=1728$ 时为 $2$，其余情形为 $1$。

在前两种情形，导数的 Bézout 等式保证 $H$ 或 $K$ 在 $x$ 处有单根。把 $c/D$ 的局部解析 $n$ 次根乘进该多项式就得到 $g$。$R$ 的根都是 $f$ 的根。其余情形中 $R(x)H(x)^2 K(x)\ne0$，因此商的导数非零，可取 $g(y)=G(y)-G(x)$。

对每个 $w\in\mathbb C$，多项式 $N-C(w)D$ 与 $N$ 的次数相同，且次数为正。纤维 $\{x\in U\mid G(x)=w\}$ 包含在该多项式的有限根集中，故 `finite_fiber` 给出其有限性。复数域上的根存在性给出至少一个根。由于 $f$ 的根处 $D=0$ 且 $N\ne0$，它属于 $U$，故 `surj` 给出 $G$ 在 $U$ 上取遍 $\mathbb C$。

### 极点极限

对每个满足 $f(z)=0$ 的 $z\in\mathbb C$，`tendsto_nhdsNE` 给出 $x\to z$ 且 $x\ne z$ 时 $|G(x)|\to+\infty$。$D$ 的根是孤立的，故穿孔邻域内 $D(x)$ 非零且趋于零，同时 $N(x)$ 趋于非零的 $N(z)$。

`tendsto_cobounded` 给出 $|x|\to+\infty$ 时 $|G(x)|\to+\infty$。令 $k=\deg N-\deg D>0$。分子与分母的首项之商是 $(\operatorname{lc}N/\operatorname{lc}D)x^k$，其中 $\operatorname{lc}$ 表示首项系数。将 $G(x)$ 除以这个首项之商所得的因子趋于 $1$，而首项之商的模趋于无穷大。

## English

### Polynomial certificate

In the table, $C(d)$ is the constant polynomial with value $d$. Primes denote polynomial derivatives, and degrees use Lean's `natDegree`. The last three rows require polynomial witnesses $q$, $a$, and $b$ and nonzero complex scalars $d$. Given `RatCert`, `D_eval_eq_zero_iff` gives $D(x)=0$ if and only if $f(x)=0$ for every $x\in\mathbb C$. At each root of $f$, the Bézout identity for $H$ and $f$ gives $H(x)\ne0$. Thus `N_eval_ne` gives $N(x)\ne0$. Lean division gives $G(x)=0$ at these points.

### Finite values and their fibers

The function $G$ is complex differentiable on $U$ and analytic at each point of $U$. For $x\in U$, $G(x)=0$ if and only if $H(x)=0$. Also, $G(x)=1728$ if and only if $K(x)=0$. The theorem `hasLocalForm` gives a coordinate $g$ analytic at $x$, with $g(x)=0$ and $g'(x)\ne0$. Near $x$ it satisfies $G(y)=G(x)+g(y)^n$. Here $n=\operatorname{sig}(G(x))$ is $3$ over $0$, $2$ over $1728$, and $1$ at all other values.

In the first two cases, a Bézout identity with the derivative makes $x$ a simple root of $H$ or $K$. Multiplying that polynomial by a local analytic $n$th root of $c/D$ gives $g$. Every root of $R$ is a root of $f$. In the last case, $R(x)H(x)^2K(x)\ne0$. The quotient rule gives a nonzero derivative, so $g(y)=G(y)-G(x)$ is a coordinate.

For every $w\in\mathbb C$, the polynomial $N-C(w)D$ has the same positive degree as $N$. The fiber $\{x\in U\mid G(x)=w\}$ lies in the finite root set of this polynomial. Thus `finite_fiber` gives its finiteness. Over $\mathbb C$, the polynomial has a root. Since $D=0$ and $N\ne0$ at every root of $f$, this root belongs to $U$. Thus `surj` says that $G$ attains every complex value on $U$.

### Limits at the poles

For every $z\in\mathbb C$ with $f(z)=0$, `tendsto_nhdsNE` gives $|G(x)|\to+\infty$ as $x\to z$ with $x\ne z$. The roots of $D$ are isolated. Thus $D(x)$ approaches zero through nonzero values while $N(x)$ approaches the nonzero value $N(z)$.

The theorem `tendsto_cobounded` gives $|G(x)|\to+\infty$ as $|x|\to+\infty$. Let $k=\deg N-\deg D>0$. The quotient of the leading monomials is $(\operatorname{lc}N/\operatorname{lc}D)x^k$, where $\operatorname{lc}$ denotes the leading coefficient. The ratio of $G(x)$ to this leading term tends to $1$. The absolute value of the leading term tends to infinity.

## 日本語

### 多項式証明書

表の $C(d)$ は値 $d$ の定数多項式を表し、プライムは多項式の導関数を表す。次数は Lean の `natDegree` に対応する。下三行の $q$、$a$、$b$ は存在を要求される多項式であり、各 $d$ は存在を要求される非零複素数である。`RatCert` が与えられると、任意の $x\in\mathbb C$ に対し、`D_eval_eq_zero_iff` により $D(x)=0$ と $f(x)=0$ は同値である。$f$ の根では $H$ と $f$ の Bézout 恒等式より $H(x)\ne0$ が成り立つ。したがって `N_eval_ne` により $N(x)\ne0$ である。これらの点では Lean の除法により $G(x)=0$ となる。

### 有限値とそのファイバー

$G$ は $U$ 上で複素微分可能であり、$U$ の各点で解析的である。任意の $x\in U$ に対し、$G(x)=0$ と $H(x)=0$ は同値であり、$G(x)=1728$ と $K(x)=0$ は同値である。`hasLocalForm` は $x$ で解析的な局所座標 $g$ を与える。$g(x)=0$、$g'(x)\ne0$ であり、$x$ のある近傍で $G(y)=G(x)+g(y)^n$ が成り立つ。ここで $n=\operatorname{sig}(G(x))$ は、$G(x)=0$ のとき $3$、$G(x)=1728$ のとき $2$、それ以外のとき $1$ である。

最初の二つの場合には、導関数との Bézout 恒等式から $x$ が $H$ または $K$ の単根であることが分かる。その多項式に $c/D$ の局所的な解析的 $n$ 乗根を掛けると $g$ が得られる。$R$ の根はいずれも $f$ の根である。それ以外の場合は $R(x)H(x)^2K(x)\ne0$ なので、商の微分公式から導関数は非零となり、$g(y)=G(y)-G(x)$ が局所座標となる。

任意の $w\in\mathbb C$ に対して、多項式 $N-C(w)D$ の次数は $N$ の次数と等しく、正である。`finite_fiber` によると、$\{x\in U\mid G(x)=w\}$ はこの多項式の有限な根集合に含まれる。この多項式は複素数体上で根をもつ。$f$ の根では $D=0$ かつ $N\ne0$ なので、その根は $U$ に属する。したがって `surj` により、$G$ は $U$ 上で任意の複素数値をとる。

### 極における極限

$f(z)=0$ を満たす任意の $z\in\mathbb C$ に対し、`tendsto_nhdsNE` により $x\ne z$ として $x\to z$ のとき $|G(x)|\to+\infty$ となる。$D$ の根は孤立している。したがって、$z$ の穴あき近傍で $D(x)$ は非零の値をとりながら零に収束し、$N(x)$ は非零の値 $N(z)$ に収束する。

`tendsto_cobounded` により、$|x|\to+\infty$ のとき $|G(x)|\to+\infty$ となる。$k=\deg N-\deg D>0$ とおく。最高次の項の商は $(\operatorname{lc}N/\operatorname{lc}D)x^k$ であり、$\operatorname{lc}$ は最高次係数を表す。$G(x)$ とこの項との比は $1$ に収束し、この項の絶対値は無限大に発散する。

## Sources

| Declaration | Pinned source | Local declaration |
| --- | --- | --- |
| Polynomial certificate | [RatCert](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Rational.lean#L29) | [RatCert](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRatCert.lean#L22) |
| Rational map and pole set | [D_eval_eq_zero_iff](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Rational.lean#L67) · [N_eval_ne](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Rational.lean#L74) · [G](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Rational.lean#L81) | [D_eval_eq_zero_iff](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRational.lean#L50) · [N_eval_ne](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRational.lean#L55) · [G](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRational.lean#L63) |
| Analyticity and distinguished fibers | [differentiableAt](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Rational.lean#L85) · [analyticAt](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Rational.lean#L91) · [G_eq_zero_iff](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Rational.lean#L98) · [G_eq_1728_iff](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Rational.lean#L110) | [differentiableAt](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRational.lean#L67) · [analyticAt](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRational.lean#L73) · [G_eq_zero_iff](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRational.lean#L76) · [G_eq_1728_iff](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRational.lean#L86) |
| Local form | [sig](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Defs.lean#L33) · [HasLocalForm](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Defs.lean#L40) · [hasLocalForm_of_eq_pow_mul](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/LocalForm.lean#L59) · [hasLocalForm](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Rational.lean#L120) | [sig](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiOrbifoldLocalForm.lean#L23) · [HasLocalForm](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiOrbifoldLocalForm.lean#L30) · [hasLocalForm_of_eq_pow_mul](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiOrbifoldLocalForm.lean#L65) · [hasLocalForm](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRational.lean#L96) |
| Finite fibers and surjectivity | [finite_fiber](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Rational.lean#L162) · [surj](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Rational.lean#L170) | [finite_fiber](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRational.lean#L140) · [surj](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRational.lean#L147) |
| Poles and infinity | [tendsto_nhdsNE](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Rational.lean#L187) · [tendsto_cobounded](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Rational.lean#L211) | [tendsto_nhdsNE](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRationalPoles.lean#L25) · [tendsto_cobounded](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRationalPoles.lean#L48) |
