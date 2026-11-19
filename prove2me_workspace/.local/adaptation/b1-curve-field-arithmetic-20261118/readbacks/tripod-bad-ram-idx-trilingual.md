# Legendre torsion-field ramification at finite places

## English

### Chord slopes and inertia on torsion

Let $L$ be a field. Let $\nu$ be a multiplicative valuation on $L$ with values in a linearly ordered commutative group with zero. Use an affine model with Weierstrass coefficients $(0,-(1+\mu),0,\mu,0)$. Its equation is $Y^2=X(X-1)(X-\mu)$. Assume $\nu(\mu)<1$ and $\nu(2)=1$.

Let $\sigma\colon L\to L$ be a ring homomorphism that preserves $\nu$. Assume $\nu(\sigma z-z)<1$ for each $z$ with $\nu(z)\le1$. For a point $(X,Y)$ on the model with $\sigma X\ne X$, put $s=(\sigma Y+Y)/(\sigma X-X)$. The slope estimates give

$$
\begin{aligned}
\nu(\mu)<\nu(X)<1
&\quad\Longrightarrow\quad
1<\nu(s)\ \lor\ \bigl(\nu(s)\le1\ \land\ \nu(s^2+1)=1\bigr),\\
\nu(X)\le\nu(\mu),\ \nu(X)<1,\ \sigma\mu=\mu
&\quad\Longrightarrow\quad 1<\nu(s).
\end{aligned}
$$

In the first range, $Y/X$ is a unit of the valuation ring and $\nu((Y/X)^2+1)<1$. In the second range, the coordinates $X/\mu$ and $Y/\mu$ belong to the valuation ring. [First slope estimate](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodMultiplicativeSlopes.lean:115) · [Second slope estimate](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodMultiplicativeSlopes.lean:202)

Assume $\sigma\mu=\mu$ and $\nu(X)<1$. Let $Q=(X,Y)$ and $\sigma Q=(\sigma X,\sigma Y)$ be nonsingular affine points. The difference $\sigma Q-Q$ is the group identity or a nonsingular affine point with first coordinate of valuation at least $1$. If $\sigma X\ne X$, the first coordinate is $(s^2+1)+(\mu-\sigma X-X)$. The second summand has valuation below $1$, so the slope estimates give the bound. If $\sigma X=X$, the proof uses equality of points or the tangent formula. [Difference of points](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodMultiplicativeDifference.lean:42)

Let $n$ be an odd natural number with $\nu(n)=1$, and assume $\sigma\mu=\mu$. Let $\phi$ be an additive endomorphism of the point group that acts by $\sigma$ on nonsingular affine coordinates. If $Q=(X,Y)$ is killed by $n$ and $1\le\nu(X)$, the fixed-point lemma gives $\phi Q=Q$. The proof obtains $\nu(X)=1$ and uses rigidity at nonsingular reduction.

If $\nu(X)<1$ and $\phi Q-Q$ is affine, the difference lemma gives the coordinate condition for the fixed-point lemma. The difference is killed by $n$ because $\phi$ is additive. For every point $Q$ killed by $n$ and every natural number $m$, the lemmas give the following identities. Here $[m]$ denotes multiplication by $m$ in the point group.

$$
\phi(\phi Q-Q)=\phi Q-Q,\qquad
\phi^{\circ m}(Q)=Q+[m](\phi Q-Q),\qquad
\phi^{\circ n}(Q)=Q.
$$

[Fixed points above the nonsingular locus](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodMultiplicativeUnipotence.lean:48) · [Unipotence](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodMultiplicativeUnipotence.lean:104) · [Iteration formula](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodMultiplicativeUnipotence.lean:126)

### Applying inertia at a finite place

Take number fields $k,L$ with $L$ a $k$-algebra. Let $\mu_0\in k$ and let $\mu$ be its image in $L$. Take a finite place $v$ of $L$ of residue characteristic different from $2$. Let $\nu$ be its multiplicative valuation. Assume $\nu(\mu)\ne1$ or $\nu(\mu-1)\ne1$. Choose an odd natural number $n$ with $\nu(n)=1$.

Let $\sigma\in\operatorname{Aut}_k(L)$ belong to the inertia group at $v$. Assume $\sigma$ fixes $i,a\in L$ with $i^2=-1$ and $a^2=\mu$. Inertia preserves $\nu$ and acts trivially modulo the maximal ideal on elements integral at $v$. Let $\phi$ be the induced point map on the base change of $\operatorname{legendre}(\mu_0)$ to $L$. For every $n$-torsion point $Q$, `iterate_map_eq_self_of_inertia` gives $\phi^{\circ n}(Q)=Q$. [Inertia preserves valuation](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodInertiaTransport.lean:24) · [Inertia congruence](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerInertia.lean:29) · [Iteration at a finite place](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodInertiaUnipotent.lean:63)

If $\nu(\mu)<1$, the proof uses the original model. If $\nu(\mu)=1$, it uses $i$ to change the parameter to $1-\mu$. If $1<\nu(\mu)$, it uses $a$ to change the parameter to $\mu^{-1}$. In each case the parameter has valuation below $1$. The isomorphisms from the changes of variables transport the iteration identity to the original model. [Model for the complement](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodInertiaTransport.lean:110) · [Model for the inverse](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodInertiaTransport.lean:131) · [Three model cases](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodInertiaUnipotent.lean:63)

### The ramification bound for the given curve

Fix `P : CurveProviders`, `x : Pt`, and an odd prime $\ell$. Let $E/F$ be the Legendre curve `P.curve x` with parameter $\lambda$. Let $K$ be the torsion field of any `R : (P.curve x).ModEllRepData ℓ`. Set $F_{\mathrm{tpd}}=\mathbb Q(\lambda)\subseteq F$. For a finite place $v$ of $K$, write $w$ and $u$ for the places of $F$ and $F_{\mathrm{tpd}}$ below it.

The set `badT P x` consists of the finite places $u$ with $u(\lambda)\ne1$ or $u(\lambda-1)\ne1$. Here $u$ denotes the absolute value. The lemma `valuation_genT_ne_one_of_mem_badT` gives the same disjunction for the multiplicative valuation at each finite place above $u$. [Tripodal field](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FieldTransport.lean:22) · [Bad places](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodLogCond.lean:89) · [Valuation transport](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodBadRamIdx.lean:79)

Suppose $u\in\texttt{badT}$ and $p=\operatorname{residueChar}(v)\notin\{2,\ell\}$. For each $\sigma$ in the inertia group $I_v$ of $K/F$ at $v$, `inertia_pow_eq_one_of_badT` gives $\sigma^\ell=1$. The chosen square roots of $-1$ and $\lambda$ belong to $F$, so $\sigma$ fixes them. Since $p\ne\ell$, the valuation at $v$ satisfies $\nu(\ell)=1$. Apply the finite-place theorem with $n=\ell$ to see that $\sigma^\ell$ fixes all $\ell$-torsion points. This action is faithful, so $\sigma^\ell$ is the identity of $K$. [Inertia exponent](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodBadRamIdx.lean:108) · [Faithfulness on torsion](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTorsionFaithful.lean:45) · [Reference bad-place proof](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/BadRamIdx.lean:76)

For any datum `R : C.ModEllRepData ℓ` with $\ell$ prime, `finrank_torsionField_dvd` shows that the extension degree divides the order of $\mathrm{GL}_2(\mathbb F_\ell)$. For the selected curve this gives

$$
[K:F]\mid(\ell^2-1)(\ell^2-\ell)
=\ell(\ell^2-1)(\ell-1),\qquad
\ell\nmid(\ell^2-1)(\ell-1).
$$

Let $q$ be a prime and $H$ a subgroup of a finite group $G$. Suppose $|G|\mid q m$, $q\nmid m$, and every $\sigma\in H$ satisfies $\sigma^q=1$. The lemma `card_le_of_forall_pow_eq_one` proves that $|H|$ is a power of $q$ and gives $|H|\le q$.

Apply the bound to $G=\operatorname{Gal}(K/F)$, $H=I_v$, and $q=\ell$, using $|G|=[K:F]$. At a bad tripodal place the relative ramification index satisfies $e(v/w)=|I_v|\le\ell$. At $u$ outside `badT`, good reduction gives $e(v/w)=1$ for $p\notin\{2,\ell\}$. Thus `relRamIdx_torsionField_le` gives the following bound at every such $v$.

$$
e(v/w)\le\ell\qquad\bigl(\operatorname{residueChar}(v)\notin\{2,\ell\}\bigr).
$$

[Degree divisibility](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodBadRamIdx.lean:24) · [Finite subgroup bound](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodBadRamIdx.lean:41) · [Inertia and ramification index](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerInertia.lean:71) · [Good-place proof](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodUnramified.lean:22) · [Ramification theorem](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodBadRamIdx.lean:131)

For $F/F_{\mathrm{tpd}}$, the downstream draft gives $e(w/u)\le30$ at bad tripodal places of residue characteristic outside $\{2,3,5\}$. At the other tripodal places in that characteristic range it uses $e(w/u)=1$. Multiplicativity gives $e(v/u)\le30\ell$ when $\operatorname{residueChar}(v)\notin\{2,3,5,\ell\}$. The Step (iii) draft applies the bound and assumes $\operatorname{ord}_p(e(v/u))\le\operatorname{wildConst}(\ell,p)$ at every finite $v$, with $p=\operatorname{residueChar}(v)$. [Bad-place bound for $F/F_{\mathrm{tpd}}$](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/TowerFacts.lean:46) · [Tower bound](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/TowerFacts.lean:46) · [Step (iii) draft](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/TowerFacts.lean:112)

The inertia iteration and the two ramification theorems passed MCP-CI review. [Review](../receipts/round-ci-022183-c7d6f502-result.json)

## 中文

### 弦斜率与挠点上的惯性作用

设域 $L$ 带有取值于带零的线序交换群的乘法赋值 $\nu$。取 Weierstrass 系数为 $(0,-(1+\mu),0,\mu,0)$ 的仿射模型，其方程为 $Y^2=X(X-1)(X-\mu)$。假设 $\nu(\mu)<1$、$\nu(2)=1$。设环同态 $\sigma\colon L\to L$ 保持 $\nu$，并且每个满足 $\nu(z)\le1$ 的 $z$ 都满足 $\nu(\sigma z-z)<1$。对于方程上的点 $(X,Y)$，若 $\sigma X\ne X$，令 $s=(\sigma Y+Y)/(\sigma X-X)$。两条斜率估计给出

$$
\begin{aligned}
\nu(\mu)<\nu(X)<1
&\quad\Longrightarrow\quad
1<\nu(s)\ \lor\ \bigl(\nu(s)\le1\ \land\ \nu(s^2+1)=1\bigr),\\
\nu(X)\le\nu(\mu),\ \nu(X)<1,\ \sigma\mu=\mu
&\quad\Longrightarrow\quad 1<\nu(s).
\end{aligned}
$$

第一种情形中，$Y/X$ 是赋值环的单位，且 $\nu((Y/X)^2+1)<1$。第二种情形使用属于赋值环的坐标 $X/\mu$、$Y/\mu$。 [第一条斜率估计](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodMultiplicativeSlopes.lean:115) · [第二条斜率估计](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodMultiplicativeSlopes.lean:202)

设 $\sigma\mu=\mu$、$\nu(X)<1$，且 $Q=(X,Y)$ 与 $\sigma Q=(\sigma X,\sigma Y)$ 均为非奇异仿射点。则 $\sigma Q-Q$ 为点群的零元，或为横坐标赋值至少为 $1$ 的非奇异仿射点。当 $\sigma X\ne X$ 时，差点的横坐标为 $(s^2+1)+(\mu-\sigma X-X)$，第二项的赋值小于 $1$，故可由斜率估计推出这一界。当 $\sigma X=X$ 时，证明使用点相等的情形或切线公式。 [差点引理](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodMultiplicativeDifference.lean:42)

取奇自然数 $n$，设 $\nu(n)=1$、$\sigma\mu=\mu$。设点群的加法自同态 $\phi$ 在非奇异仿射点的坐标上作用为 $\sigma$。若 $Q=(X,Y)$ 是 $n$ 挠点，且 $1\le\nu(X)$，固定点引理给出 $\phi Q=Q$。证明先得到 $\nu(X)=1$，再使用非奇异约化处的刚性。

若 $\nu(X)<1$，差点引理说明，当 $\phi Q-Q$ 是仿射点时，它满足固定点引理的横坐标条件。由 $\phi$ 的加法性，$\phi Q-Q$ 也是 $n$ 挠点。因此对每个 $n$ 挠点 $Q$ 和自然数 $m$，得到以下恒等式，其中 $[m]$ 表示在点群中乘以 $m$。

$$
\phi(\phi Q-Q)=\phi Q-Q,\qquad
\phi^{\circ m}(Q)=Q+[m](\phi Q-Q),\qquad
\phi^{\circ n}(Q)=Q.
$$

[非奇异约化处的固定点](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodMultiplicativeUnipotence.lean:48) · [幺幂性](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodMultiplicativeUnipotence.lean:104) · [迭代公式](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodMultiplicativeUnipotence.lean:126)

### 有限位上的惯性作用

取数域 $k,L$，其中 $L$ 是 $k$-代数。取 $\mu_0\in k$ 和 $L$ 中剩余特征不为 $2$ 的有限位 $v$。记 $\nu$ 为其乘法赋值，$\mu$ 为 $\mu_0$ 在 $L$ 中的像。假设 $\nu(\mu)\ne1$ 或 $\nu(\mu-1)\ne1$。取奇自然数 $n$ 且 $\nu(n)=1$。设 $\sigma\in\operatorname{Aut}_k(L)$ 属于 $v$ 的惯性群，并固定所选的 $i,a\in L$，其中 $i^2=-1$、$a^2=\mu$。惯性作用保持 $\nu$，且在 $v$ 处整元素模极大理想的剩余类上作用平凡。定理 `iterate_map_eq_self_of_inertia` 给出 $\phi^{\circ n}(Q)=Q$，适用于 $\operatorname{legendre}(\mu_0)$ 基变换到 $L$ 后的每个 $n$ 挠点 $Q$，其中 $\phi$ 是 $\sigma$ 诱导的点映射。 [惯性保持赋值](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodInertiaTransport.lean:24) · [惯性同余](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerInertia.lean:29) · [有限位处的迭代](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodInertiaUnipotent.lean:63)

证明分别在 $\nu(\mu)<1$、$\nu(\mu)=1$、$1<\nu(\mu)$ 三种情形使用参数 $\mu$、$1-\mu$、$\mu^{-1}$ 的模型。所选参数的赋值小于 $1$。后两种情形分别用固定的平方根 $i$ 和 $a$ 作变量代换，再通过所得同构将迭代恒等式移回原模型。 [互补参数模型](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodInertiaTransport.lean:110) · [倒数参数模型](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodInertiaTransport.lean:131) · [三种模型](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodInertiaUnipotent.lean:63)

### 给定曲线的分歧界

固定 `P : CurveProviders`、`x : Pt` 和奇素数 $\ell$。设 $E/F$ 为 `P.curve x` 对应的 Legendre 曲线，参数为 $\lambda$。取任意 `R : (P.curve x).ModEllRepData ℓ`，记 $K$ 为 $R$ 的挠点域，令 $F_{\mathrm{tpd}}=\mathbb Q(\lambda)\subseteq F$。对 $K$ 中的有限位 $v$，记其下方在 $F$ 和 $F_{\mathrm{tpd}}$ 上的位为 $w$ 和 $u$。`badT P x` 由满足 $u(\lambda)\ne1$ 或 $u(\lambda-1)\ne1$ 的有限位 $u$ 组成，这里 $u$ 表示该位的绝对值。引理 `valuation_genT_ne_one_of_mem_badT` 将这个析取搬到 $F_{\mathrm{tpd}}$ 上任意数域中位于 $u$ 上方的位的乘法赋值。 [三脚架域](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FieldTransport.lean:22) · [坏位集](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodLogCond.lean:89) · [赋值搬运](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodBadRamIdx.lean:79)

设 $u\in\texttt{badT}$，且 $p=\operatorname{residueChar}(v)\notin\{2,\ell\}$。对 $K/F$ 在 $v$ 处的惯性群 $I_v$ 中每个 $\sigma$，`inertia_pow_eq_one_of_badT` 给出 $\sigma^\ell=1$。$-1$ 与 $\lambda$ 的所选平方根属于 $F$，故 $\sigma$ 固定它们。由 $p\ne\ell$ 得 $v$ 处的赋值满足 $\nu(\ell)=1$。取 $n=\ell$ 应用有限位定理，得到 $\sigma^\ell$ 固定全部 $\ell$ 挠点。挠点上的作用忠实，故 $\sigma^\ell$ 是 $K$ 的恒等自同构。 [惯性群元素的幂](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodBadRamIdx.lean:108) · [挠点作用的忠实性](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTorsionFaithful.lean:45) · [参考坏位证明](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/BadRamIdx.lean:76)

对于任意 `R : C.ModEllRepData ℓ` 及素数 $\ell$，`finrank_torsionField_dvd` 给出扩张次数整除 $\mathrm{GL}_2(\mathbb F_\ell)$ 的阶。对所选曲线得到

$$
[K:F]\mid(\ell^2-1)(\ell^2-\ell)
=\ell(\ell^2-1)(\ell-1),\qquad
\ell\nmid(\ell^2-1)(\ell-1).
$$

设 $q$ 为素数，$H$ 为有限群 $G$ 的子群。若 $|G|\mid q m$、$q\nmid m$，且 $H$ 的每个元素 $\sigma$ 都满足 $\sigma^q=1$，则 `card_le_of_forall_pow_eq_one` 先证明 $|H|$ 是 $q$ 的幂，继而得出 $|H|\le q$。

将其用于 $G=\operatorname{Gal}(K/F)$、$H=I_v$、$q=\ell$，并用 $|G|=[K:F]$。在坏三脚架域位上方，相对分歧指数满足 $e(v/w)=|I_v|\le\ell$。若 $u$ 在 `badT` 之外且 $p\notin\{2,\ell\}$，好约化给出 $e(v/w)=1$。因此 `relRamIdx_torsionField_le` 对每个这样的 $v$ 给出

$$
e(v/w)\le\ell\qquad\bigl(\operatorname{residueChar}(v)\notin\{2,\ell\}\bigr).
$$

[扩张次数的整除性](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodBadRamIdx.lean:24) · [有限子群阶的上界](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodBadRamIdx.lean:41) · [惯性群与分歧指数](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerInertia.lean:71) · [好位证明](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodUnramified.lean:22) · [分歧定理](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodBadRamIdx.lean:131)

后续草稿在剩余特征避开 $\{2,3,5\}$ 的坏三脚架域位上使用 $e(w/u)\le30$，在该特征范围内的其余三脚架域位上使用 $e(w/u)=1$，并与上述 $K/F$ 界相乘。在剩余特征避开 $\{2,3,5,\ell\}$ 时得到 $e(v/u)\le30\ell$。步骤 (iii) 的组合草稿提供这一界，并对每个有限位 $v$ 显式假设 $\operatorname{ord}_p(e(v/u))\le\operatorname{wildConst}(\ell,p)$，其中 $p=\operatorname{residueChar}(v)$。 [坏位上的 $F/F_{\mathrm{tpd}}$ 分歧界](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/TowerFacts.lean:46) · [域塔分歧界](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/TowerFacts.lean:46) · [步骤 (iii) 草稿](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/TowerFacts.lean:112)



惯性迭代及两项分歧声明通过 MCP-CI 审查。 [MCP-CI](../receipts/round-ci-022183-c7d6f502-result.json)

## 日本語

### 弦の傾きとねじれ点への惰性作用

$L$ を体とし、零付きの全順序可換群に値を取る乗法的付値を $\nu$ とする。Weierstrass 係数が $(0,-(1+\mu),0,\mu,0)$ のアフィンモデルを取る。その方程式は $Y^2=X(X-1)(X-\mu)$ である。$\nu(\mu)<1$ と $\nu(2)=1$ を仮定する。環準同型 $\sigma\colon L\to L$ は $\nu$ を保つとし、$\nu(z)\le1$ を満たす各 $z$ について $\nu(\sigma z-z)<1$ を仮定する。方程式上の点 $(X,Y)$ が $\sigma X\ne X$ を満たすとき、$s=(\sigma Y+Y)/(\sigma X-X)$ とおく。二つの傾きの評価は次のとおりである。

$$
\begin{aligned}
\nu(\mu)<\nu(X)<1
&\quad\Longrightarrow\quad
1<\nu(s)\ \lor\ \bigl(\nu(s)\le1\ \land\ \nu(s^2+1)=1\bigr),\\
\nu(X)\le\nu(\mu),\ \nu(X)<1,\ \sigma\mu=\mu
&\quad\Longrightarrow\quad 1<\nu(s).
\end{aligned}
$$

第一の場合には、$Y/X$ は付値環の単元であり、$\nu((Y/X)^2+1)<1$ を満たす。第二の場合には、付値環に属する座標 $X/\mu$ と $Y/\mu$ を用いる。 [第一の傾きの評価](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodMultiplicativeSlopes.lean:115) · [第二の傾きの評価](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodMultiplicativeSlopes.lean:202)

$\sigma\mu=\mu$ と $\nu(X)<1$ を仮定し、$Q=(X,Y)$ と $\sigma Q=(\sigma X,\sigma Y)$ はともに非特異アフィン点とする。このとき $\sigma Q-Q$ は点の加法群の零元、または第一座標の付値が $1$ 以上の非特異アフィン点である。$\sigma X\ne X$ ならば、差の第一座標は $(s^2+1)+(\mu-\sigma X-X)$ となる。第二項の付値が $1$ 未満なので、傾きの評価から第一座標の評価が従う。$\sigma X=X$ のときは、点の一致または接線の公式を用いる。 [点の差の補題](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodMultiplicativeDifference.lean:42)

$n$ を奇数の自然数とし、$\nu(n)=1$ と $\sigma\mu=\mu$ を仮定する。点の加法群の自己準同型 $\phi$ は非特異アフィン点の座標に $\sigma$ として作用するとする。$Q=(X,Y)$ が $n$ ねじれ点で $1\le\nu(X)$ ならば、固定点の補題から $\phi Q=Q$ となる。証明は $\nu(X)=1$ を導き、非特異な還元における剛性を用いる。

$\nu(X)<1$ かつ $\phi Q-Q$ がアフィン点ならば、差の補題から固定点の補題の第一座標の条件を満たす。$\phi$ は加法的なので、$\phi Q-Q$ も $n$ ねじれ点である。従って、すべての $n$ ねじれ点 $Q$ と自然数 $m$ について次の等式を得る。ここで $[m]$ は点の加法群での $m$ 倍を表す。

$$
\phi(\phi Q-Q)=\phi Q-Q,\qquad
\phi^{\circ m}(Q)=Q+[m](\phi Q-Q),\qquad
\phi^{\circ n}(Q)=Q.
$$

[非特異な還元を持つ固定点](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodMultiplicativeUnipotence.lean:48) · [ユニポテント性](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodMultiplicativeUnipotence.lean:104) · [反復の等式](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodMultiplicativeUnipotence.lean:126)

### 有限素点での惰性作用

$k,L$ を数体とし、$L$ は $k$-代数とする。$\mu_0\in k$ と、剰余標数が $2$ と異なる $L$ の有限素点 $v$ を取る。$\nu$ をその乗法的付値、$\mu$ を $\mu_0$ の $L$ での像とする。$\nu(\mu)\ne1$ または $\nu(\mu-1)\ne1$ を仮定する。$\nu(n)=1$ を満たす奇数の自然数 $n$ を取る。$\sigma\in\operatorname{Aut}_k(L)$ は $v$ の惰性群に属し、$i^2=-1$ と $a^2=\mu$ を満たす選ばれた $i,a\in L$ を固定するとする。惰性作用は $\nu$ を保ち、$v$ で整な元の極大イデアルによる剰余類に自明に作用する。`iterate_map_eq_self_of_inertia` は、$\operatorname{legendre}(\mu_0)$ を $L$ に基底変換した曲線上のすべての $n$ ねじれ点 $Q$ に対し、$\phi^{\circ n}(Q)=Q$ を与える。ここで $\phi$ は $\sigma$ が誘導する点の写像である。 [惰性作用による付値の保存](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodInertiaTransport.lean:24) · [惰性作用の合同条件](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerInertia.lean:29) · [有限素点での反復](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodInertiaUnipotent.lean:63)

証明は $\nu(\mu)<1$、$\nu(\mu)=1$、$1<\nu(\mu)$ の三つの場合に、それぞれパラメータ $\mu$、$1-\mu$、$\mu^{-1}$ のモデルを用いる。選んだパラメータの付値は $1$ 未満である。後の二つの場合は、固定された平方根 $i$ と $a$ をそれぞれ用いて変数変換を行う。その同型で反復の等式を元のモデルに移す。 [補パラメータのモデル](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodInertiaTransport.lean:110) · [逆数パラメータのモデル](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodInertiaTransport.lean:131) · [三つのモデル](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodInertiaUnipotent.lean:63)

### 与えられた曲線の分岐指数の評価

`P : CurveProviders`、`x : Pt`、奇素数 $\ell$ を固定する。$E/F$ は `P.curve x` で与えられるパラメータ $\lambda$ の Legendre 曲線とする。任意の `R : (P.curve x).ModEllRepData ℓ` のねじれ点体を $K$ とし、$F_{\mathrm{tpd}}=\mathbb Q(\lambda)\subseteq F$ とおく。$K$ の有限素点 $v$ に対し、その下にある $F$ および $F_{\mathrm{tpd}}$ の素点をそれぞれ $w,u$ とする。`badT P x` は $u(\lambda)\ne1$ または $u(\lambda-1)\ne1$ を満たす有限素点 $u$ の集合である。ここで $u$ は素点の絶対値を表す。`valuation_genT_ne_one_of_mem_badT` はこの選言を、$F_{\mathrm{tpd}}$ 上の数体で $u$ の上にある各素点の乗法的付値に移す。 [三脚体](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FieldTransport.lean:22) · [悪い素点の集合](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodLogCond.lean:89) · [付値への移行](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodBadRamIdx.lean:79)

$u\in\texttt{badT}$ と $p=\operatorname{residueChar}(v)\notin\{2,\ell\}$ を仮定する。$K/F$ の $v$ における惰性群 $I_v$ の各 $\sigma$ に対し、`inertia_pow_eq_one_of_badT` は $\sigma^\ell=1$ を与える。$-1$ と $\lambda$ の選ばれた平方根は $F$ に属するため、$\sigma$ はそれらを固定する。$p\ne\ell$ から $v$ での付値は $\nu(\ell)=1$ を満たす。有限素点での定理を $n=\ell$ で適用すると、$\sigma^\ell$ はすべての $\ell$ ねじれ点を固定する。この作用は忠実なので、$\sigma^\ell$ は $K$ の恒等自己同型である。 [惰性群の元のべき](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodBadRamIdx.lean:108) · [ねじれ点への忠実な作用](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTorsionFaithful.lean:45) · [参照元の悪い素点での証明](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/BadRamIdx.lean:76)

任意の `R : C.ModEllRepData ℓ` と素数 $\ell$ に対し、`finrank_torsionField_dvd` は拡大次数が $\mathrm{GL}_2(\mathbb F_\ell)$ の位数を割ることを示す。選んだ曲線に対しては次を得る。

$$
[K:F]\mid(\ell^2-1)(\ell^2-\ell)
=\ell(\ell^2-1)(\ell-1),\qquad
\ell\nmid(\ell^2-1)(\ell-1).
$$

$q$ を素数とし、$H$ を有限群 $G$ の部分群とする。$|G|\mid q m$、$q\nmid m$、かつ $H$ の各元 $\sigma$ が $\sigma^q=1$ を満たすと仮定する。`card_le_of_forall_pow_eq_one` はまず $|H|$ が $q$ のべきであることを示し、$|H|\le q$ を導く。

$|G|=[K:F]$ を用いて $G=\operatorname{Gal}(K/F)$、$H=I_v$、$q=\ell$ に適用すると、三脚体の悪い素点の上で相対分岐指数は $e(v/w)=|I_v|\le\ell$ を満たす。$u$ が `badT` の外にあり、$p\notin\{2,\ell\}$ ならば、良い還元から $e(v/w)=1$ となる。従って `relRamIdx_torsionField_le` は、この剰余標数の条件を満たすすべての $v$ に対して次を与える。

$$
e(v/w)\le\ell\qquad\bigl(\operatorname{residueChar}(v)\notin\{2,\ell\}\bigr).
$$

[拡大次数の整除性](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodBadRamIdx.lean:24) · [有限部分群の位数の評価](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodBadRamIdx.lean:41) · [惰性群と分岐指数](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerInertia.lean:71) · [良い素点での証明](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodUnramified.lean:22) · [分岐指数の定理](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodBadRamIdx.lean:131)

後続の草稿は、剰余標数が $\{2,3,5\}$ の外にあるとき、三脚体の悪い素点では $e(w/u)\le30$ を用い、それ以外の三脚体の素点では $e(w/u)=1$ を用いる。これを $K/F$ の評価と掛け合わせ、剰余標数が $\{2,3,5,\ell\}$ の外にあれば $e(v/u)\le30\ell$ を得る。ステップ (iii) の組み立ての草稿はこの上界を与え、すべての有限素点 $v$ に対して $\operatorname{ord}_p(e(v/u))\le\operatorname{wildConst}(\ell,p)$ を明示的に仮定する。ここで $p=\operatorname{residueChar}(v)$ である。 [悪い素点での $F/F_{\mathrm{tpd}}$ の分岐指数](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/TowerFacts.lean:46) · [体の塔での評価](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/TowerFacts.lean:46) · [ステップ (iii) の草稿](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/TowerFacts.lean:112)

惰性群の反復作用と分岐に関する二つの命題は MCP-CI の審査に合格した。 [MCP-CI](../receipts/round-ci-022183-c7d6f502-result.json)
