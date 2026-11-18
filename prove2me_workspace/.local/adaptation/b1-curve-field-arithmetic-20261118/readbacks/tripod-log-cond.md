# Tripodal conductor bounds

Source revision `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`, Apache-2.0. [Iut/Tripod/LogCond.lean](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/LogCond.lean:193)

## English

Take any `CurveProviders` $P$, any tripod point $x$ with coordinate $\lambda\in\overline{\mathbb Q}\setminus\{0,1\}$, and any prime $\ell\ge 7$. Let $E=(P.\mathrm{curve}\,x).E$ be the Legendre curve over $F=(P.\mathrm{curve}\,x).F$. Let $T$ be the tripodal subfield of $F$ for $E$. The isomorphism `tpdEquiv` identifies $T$ with $\mathbb Q(\lambda)$ and sends the generator of $T$ to $\lambda$. The degree $d=[T:\mathbb Q]=\deg(x.1)$ is positive. It equals the degree of the minimal polynomial of $\lambda$ over $\mathbb Q$.

Let $S$ consist of the finite places $\mathfrak p$ of $T$ where $|\lambda|_{\mathfrak p}\ne 1$ or $|\lambda-1|_{\mathfrak p}\ne 1$. In these expressions, $\lambda$ is the generator in $T$. Each of these two nonzero elements has absolute value different from one at only finitely many places. Thus $S$ is finite.

Let $B_\ell$ consist of the finite places $\mathfrak p$ of $T$ that satisfy `IsBadTpdOf`. This predicate requires a finite place $w$ of $F$ above $\mathfrak p$. The place $w$ must also lie above a place $v$ in `VBadOf ℓ`. Here $v$ is a finite place of the field of moduli $\mathbb Q(j(E))$. Membership in `VBadOf ℓ` requires residue characteristic different from $2$ and $\ell$. It requires at least one place of $F$ above $v$ and multiplicative reduction of $E$ at every such place. [TripodalInvariants.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean:30)

Write $N\mathfrak p$ for the cardinality of the residue field at $\mathfrak p$. Transport along `tpdEquiv` preserves absolute values at corresponding places and the residue field cardinalities. The two sums on $T$ are

$$
\operatorname{logCond}(x)=\frac{1}{d}\sum_{\mathfrak p\in S}\log N\mathfrak p,\qquad
C_\ell=\operatorname{logConductorDegOf}(F,E,\mathrm{VBadOf}(\ell))
=\frac{1}{d}\sum_{\mathfrak p\in B_\ell}\log N\mathfrak p.
$$

If $\mathfrak p\in B_\ell$, the witness $w$ has multiplicative reduction. Its multiplicative valuation satisfies $v_w(j(E))>1$. The formula $j(E)=256(\lambda^2-\lambda+1)^3/(\lambda^2(\lambda-1)^2)$ then puts $\mathfrak p$ in $S$. The inclusion $B_\ell\subseteq S$ makes the second sum finite. Each summand is nonnegative, which gives `LogCondGeHyp P`, the inequality $C_\ell\le\operatorname{logCond}(x)$.

Take a place of $S$ of residue characteristic different from $2$ and $\ell$. At a place $w$ above it, $v_w(256)=1$, so the same formula gives $v_w(j(E))>1$. Stable reduction implies multiplicative reduction at $w$. The arithmetic of the given curve supplies a place $v$ below $w$ in the field of moduli. The residue characteristic stays the same. The curve arithmetic gives multiplicative reduction at every place above $v$, so $v$ belongs to `VBadOf ℓ`. Thus each place in $S\setminus B_\ell$ has residue characteristic $2$ or $\ell$.

For a fixed residue characteristic $q$, the identity $N\mathfrak p=q^{f_{\mathfrak p}}$ uses the residue degree $f_{\mathfrak p}$. The residue degrees over $q$ sum to at most $d$. After division by $d$, the places in the difference over $q$ contribute at most $\log q$. The two contributions give `LogCondLeHyp P`, the inequality $\operatorname{logCond}(x)\le C_\ell+\log(2\ell)$.

## 简体中文

取任意 `CurveProviders` $P$、任意坐标为 $\lambda\in\overline{\mathbb Q}\setminus\{0,1\}$ 的三足曲线点 $x$，以及任意素数 $\ell\ge 7$。取 $F=(P.\mathrm{curve}\,x).F$ 上的勒让德曲线 $E=(P.\mathrm{curve}\,x).E$。设 $T$ 是该曲线在 $F$ 内的三足域。域同构 `tpdEquiv` 将 $T$ 识别为 $\mathbb Q(\lambda)$，并把 $T$ 的生成元送到 $\lambda$。正整数 $d=[T:\mathbb Q]=\deg(x.1)$ 等于 $\lambda$ 在 $\mathbb Q$ 上的最小多项式的次数。

设 $S$ 由 $T$ 上满足 $|\lambda|_{\mathfrak p}\ne 1$ 或 $|\lambda-1|_{\mathfrak p}\ne 1$ 的有限处 $\mathfrak p$ 组成。式中 $\lambda$ 指 $T$ 内的生成元。这两个元素均非零，各自的绝对值异于 $1$ 的处都只有有限多个，故 $S$ 有限。

设 $B_\ell$ 是 $T$ 上满足 `IsBadTpdOf` 的有限处集合。该谓词要求 $F$ 有一个位于 $\mathfrak p$ 上方的有限处 $w$，且 $w$ 也位于 `VBadOf ℓ` 中某个有限处 $v$ 的上方。这里 $v$ 是模域 $\mathbb Q(j(E))$ 上的有限处。属于 `VBadOf ℓ` 的 $v$ 的剩余特征须异于 $2$ 和 $\ell$。在 $F$ 中，$v$ 上方至少有一个有限处，且 $E$ 在每个这样的处都具有乘法约化。 [TripodalInvariants.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean:30)

记 $N\mathfrak p$ 为 $\mathfrak p$ 的剩余域基数。沿 `tpdEquiv` 输运保持对应处的绝对值和剩余域基数。因此在 $T$ 上的两个和为

$$
\operatorname{logCond}(x)=\frac{1}{d}\sum_{\mathfrak p\in S}\log N\mathfrak p,\qquad
C_\ell=\operatorname{logConductorDegOf}(F,E,\mathrm{VBadOf}(\ell))
=\frac{1}{d}\sum_{\mathfrak p\in B_\ell}\log N\mathfrak p.
$$

若 $\mathfrak p\in B_\ell$，见证处 $w$ 有乘法约化，所以乘法记法下的赋值满足 $v_w(j(E))>1$。由公式 $j(E)=256(\lambda^2-\lambda+1)^3/(\lambda^2(\lambda-1)^2)$ 可得 $\mathfrak p\in S$。由 $B_\ell\subseteq S$ 可知，第二个和是有限和。各项均非负，由此得到 `LogCondGeHyp P` 的不等式 $C_\ell\le\operatorname{logCond}(x)$。

若 $S$ 中某处的剩余特征异于 $2$ 和 $\ell$，取其上方一个处 $w$，则 $v_w(256)=1$，由同一公式得到 $v_w(j(E))>1$。由稳定约化可知 $E$ 在 $w$ 处具有乘法约化。给定曲线的算术数据给出 $w$ 下方的模域处 $v$。剩余特征保持不变，且算术数据将乘法约化传到 $v$ 上方的每一个处，从而得到 $v\in\mathrm{VBadOf}(\ell)$。因此 $S\setminus B_\ell$ 中的处的剩余特征只能是 $2$ 或 $\ell$。

固定剩余特征 $q$ 时，$N\mathfrak p=q^{f_{\mathfrak p}}$，其中 $f_{\mathfrak p}$ 是剩余次数。$q$ 上方各处的剩余次数之和至多为 $d$。除以 $d$ 后，差集中剩余特征为 $q$ 的处的总贡献至多为 $\log q$。两项相加得到 `LogCondLeHyp P` 的不等式 $\operatorname{logCond}(x)\le C_\ell+\log(2\ell)$。

## 日本語

任意の `CurveProviders` $P$、座標が $\lambda\in\overline{\mathbb Q}\setminus\{0,1\}$ である任意の三点除去直線の点 $x$、任意の素数 $\ell\ge 7$ を取る。$F=(P.\mathrm{curve}\,x).F$ 上のルジャンドル曲線 $E=(P.\mathrm{curve}\,x).E$ を用いる。$T$ を $F$ の中にある $E$ の三脚体とする。体の同型 `tpdEquiv` は $T$ を $\mathbb Q(\lambda)$ と同一視し、$T$ の生成元を $\lambda$ に写す。正整数 $d=[T:\mathbb Q]=\deg(x.1)$ は、$\lambda$ の $\mathbb Q$ 上の最小多項式の次数に等しい。

$S$ を、$|\lambda|_{\mathfrak p}\ne 1$ または $|\lambda-1|_{\mathfrak p}\ne 1$ を満たす $T$ の有限素点 $\mathfrak p$ の集合とする。これらの式の $\lambda$ は $T$ の生成元を表す。これら二つの元はいずれも非零であり、それぞれの絶対値が $1$ と異なる素点は有限個である。従って $S$ は有限集合である。

$B_\ell$ を `IsBadTpdOf` を満たす $T$ の有限素点の集合とする。この述語は、$\mathfrak p$ の上にある $F$ の有限素点 $w$ で、さらに `VBadOf ℓ` に属する有限素点 $v$ の上にあるものの存在を要求する。ここで $v$ はモジュライ体 $\mathbb Q(j(E))$ の有限素点である。`VBadOf ℓ` に属する $v$ の剰余標数は $2$ と $\ell$ のいずれとも異なる。$F$ には $v$ の上の素点が少なくとも一つ存在し、そのすべてで $E$ は乗法的還元を持つ。 [TripodalInvariants.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean:30)

$N\mathfrak p$ を $\mathfrak p$ の剰余体の位数とする。`tpdEquiv` による移送は、対応する素点での絶対値と剰余体の位数を保つ。従って $T$ 上での二つの和は次の式で与えられる。

$$
\operatorname{logCond}(x)=\frac{1}{d}\sum_{\mathfrak p\in S}\log N\mathfrak p,\qquad
C_\ell=\operatorname{logConductorDegOf}(F,E,\mathrm{VBadOf}(\ell))
=\frac{1}{d}\sum_{\mathfrak p\in B_\ell}\log N\mathfrak p.
$$

$\mathfrak p\in B_\ell$ の存在条件を満たす $w$ では $E$ が乗法的還元を持つため、乗法的に表した付値は $v_w(j(E))>1$ を満たす。公式 $j(E)=256(\lambda^2-\lambda+1)^3/(\lambda^2(\lambda-1)^2)$ から $\mathfrak p\in S$ が従う。よって $B_\ell\subseteq S$ となり、二番目の和も有限和である。各項が非負なので、`LogCondGeHyp P` の不等式 $C_\ell\le\operatorname{logCond}(x)$ を得る。

$S$ の素点の剰余標数が $2$ と $\ell$ のいずれとも異なるとき、その上にある素点 $w$ では $v_w(256)=1$ であり、同じ公式から $v_w(j(E))>1$ を得る。安定還元性により $w$ では乗法的還元が成り立つ。与えられた曲線の算術データから、$w$ の下にあるモジュライ体の素点 $v$ が得られる。剰余標数は保たれ、$v$ の上にあるすべての素点で乗法的還元が成り立つため、$v\in\mathrm{VBadOf}(\ell)$ となる。従って $S\setminus B_\ell$ の素点の剰余標数は $2$ または $\ell$ である。

剰余標数 $q$ を固定すると、$N\mathfrak p=q^{f_{\mathfrak p}}$ であり、$f_{\mathfrak p}$ は剰余次数である。$q$ の上の素点の剰余次数の和は高々 $d$ である。$d$ で割ると、剰余標数が $q$ である差集合中の素点の寄与は高々 $\log q$ となる。二つの寄与を加えると、`LogCondLeHyp P` の不等式 $\operatorname{logCond}(x)\le C_\ell+\log(2\ell)$ を得る。
