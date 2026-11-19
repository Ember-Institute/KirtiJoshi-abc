# CanLift

## exists_coset_polynomial

### English

Let $\mathbb H$ be the upper half-plane with the fractional linear action of $\operatorname{SL}_2(\mathbb R)$. Let $\Gamma\le N\le\operatorname{SL}_2(\mathbb R)$ with finite index $[N:\Gamma]$ and let $F:\mathbb H\to\mathbb C$ be invariant under $\Gamma$. Assume that whenever $F(\tau)=F(\tau')$, some $\gamma\in\Gamma$ sends $\tau$ to $\tau'$. There exist a finite index set $I$ and matrices $g_i\in N$ for which $P_\tau(T)=\prod_{i\in I}(T-F(g_i\cdot\tau))$ is monic, has root $F(\tau)$ for all $\tau$, and satisfies $P_{u\cdot\tau}=P_\tau$ for all $u\in N$ and $\tau\in\mathbb H$. For every pair $\tau,\tau'\in\mathbb H$, all coefficients of $P_\tau$ and $P_{\tau'}$ agree if and only if some $u\in N$ sends $\tau$ to $\tau'$.

### 中文

设 $\mathbb H$ 为上半平面，$\operatorname{SL}_2(\mathbb R)$ 在其上作分式线性作用。设 $\Gamma\le N$ 为其中的子群，且 $[N:\Gamma]$ 有限。设 $F:\mathbb H\to\mathbb C$ 在 $\Gamma$ 作用下不变，并且 $F(\tau)=F(\tau')$ 时存在 $\gamma\in\Gamma$ 使 $\gamma\cdot\tau=\tau'$。则存在有限指标集 $I$ 和矩阵 $g_i\in N$，使每个 $P_\tau(T)=\prod_{i\in I}(T-F(g_i\cdot\tau))$ 都为首一多项式，以 $F(\tau)$ 为根，且对所有 $u\in N$ 和 $\tau\in\mathbb H$ 满足 $P_{u\cdot\tau}=P_\tau$。对任意 $\tau,\tau'\in\mathbb H$，$P_\tau$ 与 $P_{\tau'}$ 的所有系数分别相等，当且仅当存在 $u\in N$ 使 $u\cdot\tau=\tau'$。

### 日本語

$\mathbb H$ を上半平面とし、$\operatorname{SL}_2(\mathbb R)$ は分数線形変換で作用する。$\Gamma\le N$ をその部分群とし、指数 $[N:\Gamma]$ は有限とする。写像 $F:\mathbb H\to\mathbb C$ は $\Gamma$ の作用で不変であり、$F(\tau)=F(\tau')$ ならば $\gamma\cdot\tau=\tau'$ となる $\gamma\in\Gamma$ が存在すると仮定する。有限添字集合 $I$ と行列 $g_i\in N$ が存在し、各 $P_\tau(T)=\prod_{i\in I}(T-F(g_i\cdot\tau))$ はモニックで $F(\tau)$ を根に持ち、すべての $u\in N$ と $\tau\in\mathbb H$ に対して $P_{u\cdot\tau}=P_\tau$ を満たす。任意の $\tau,\tau'\in\mathbb H$ に対して、$P_\tau$ と $P_{\tau'}$ の全係数がそれぞれ一致することと、$u\cdot\tau=\tau'$ となる $u\in N$ が存在することは同値である。

[Lean coset polynomial theorem](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftCosetPolynomial.lean:24)

## RatFuncPoly.exists_poly_generator

### English

Let $K$ be an algebraically closed field and $R$ a $K$-subalgebra of $K[T]$ containing a polynomial of positive degree. There exists $s\in K[T]$ of positive degree for which some $r,q\in R$ satisfy $q\ne0$ and $sq=r$. Every polynomial $p\in R$ admits a polynomial $a\in K[T]$ with $p(T)=a(s(T))$ as a polynomial identity.

### 中文

设 $K$ 为代数闭域，$R$ 为 $K[T]$ 的 $K$-子代数，且 $R$ 含有正次数多项式。则存在正次数的 $s\in K[T]$，使得有 $r,q\in R$ 满足 $q\ne0$ 且 $sq=r$。对每个 $p\in R$，存在 $a\in K[T]$ 使多项式恒等式 $p(T)=a(s(T))$ 成立。

### 日本語

$K$ を代数閉体とし、$R$ を正次数の多項式を含む $K[T]$ の $K$ 部分代数とする。正次数の $s\in K[T]$ が存在し、ある $r,q\in R$ に対して $q\ne0$ かつ $sq=r$ が成り立つ。任意の $p\in R$ に対して $a\in K[T]$ が存在し、多項式の恒等式 $p(T)=a(s(T))$ が成り立つ。

[Lean polynomial generator theorem](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftRatFuncPoly.lean:182)
