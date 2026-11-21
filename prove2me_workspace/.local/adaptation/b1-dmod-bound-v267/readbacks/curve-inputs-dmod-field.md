# English

Let $P$ supply the $3$-torsion and $5$-torsion finiteness proofs for all algebraic parameters, the arithmetic of the resulting Legendre curves and their representations modulo each prime. Let $K$ specify a finite set of primes containing $2$ and a real bound $c$. Fix a natural number $d$ and a point $x$ on the projective line with $0,1,\infty$ removed. Write $\lambda$ for its coordinate. Assume that the degree of the minimal polynomial of $\lambda$ over $\mathbb Q$ is at most $d$. Assume also that at every infinite place of $\mathbb Q(\lambda)$ and every finite place with residue characteristic in the specified set, the absolute values of the logarithms of the local absolute values of $\lambda$ and $\lambda-1$ are at most $c$.

For the curve $P.\mathrm{curve}(x)$ over its supplied number field, `curveInputs_dmod_le` gives $[\mathbb Q(j(P.\mathrm{curve}(x))):\mathbb Q]\leq d$. Its proof applies `dmod_le` to the curve selected by the same $P$ and uses the point degree bound.

# 简体中文

设 $P$ 为每个代数参数提供 $3$-挠点集和 $5$-挠点集的有限性证明，并提供由此得到的 Legendre 曲线的算术数据及模各素数的表示。令 $K$ 指定一个含有 $2$ 的有限素数集和实数界 $c$。固定自然数 $d$ 和射影直线去掉 $0,1,\infty$ 后的一个点 $x$，记其坐标为 $\lambda$。假设 $\lambda$ 在 $\mathbb Q$ 上的极小多项式次数至多为 $d$。参考代码以如下处上的有界条件表示紧致有界子集的约束：在 $\mathbb Q(\lambda)$ 的每个无穷处，以及剩余特征属于所指定素数集的每个有限处，$\lambda$ 和 $\lambda-1$ 的局部绝对值取对数后的绝对值均至多为 $c$。

对 $P$ 在数域上给出的曲线 $P.\mathrm{curve}(x)$，`curveInputs_dmod_le` 给出 $[\mathbb Q(j(P.\mathrm{curve}(x))):\mathbb Q]\leq d$。证明将 `dmod_le` 用于同一 $P$ 选定的曲线，再使用点的次数界。

# 日本語

$P$ が、すべての代数的なパラメータに対する $3$ 等分点集合と $5$ 等分点集合の有限性の証明、およびこれらから定まる Legendre 曲線の数論的データと各素数を法とする表現を与えるとする。$K$ は $2$ を含む有限な素数集合と実数の上限 $c$ を指定するものとする。自然数 $d$ と、射影直線から $0,1,\infty$ を除いた曲線上の点 $x$ を固定し、その座標を $\lambda$ とする。$\lambda$ の $\mathbb Q$ 上の最小多項式の次数は $d$ 以下とする。また、$\mathbb Q(\lambda)$ のすべての無限素点と、指定された素数集合に剰余標数が属するすべての有限素点で、$\lambda$ と $\lambda-1$ の局所絶対値の対数の絶対値はともに $c$ 以下とする。

$P$ が数体上に与える曲線 $P.\mathrm{curve}(x)$ に対して、`curveInputs_dmod_le` は $[\mathbb Q(j(P.\mathrm{curve}(x))):\mathbb Q]\leq d$ を与える。証明では、同じ $P$ が定める曲線に `dmod_le` を適用し、点の次数の上限を用いる。

[Local degree field](../../../../Solutions/Source_TripodCurveInputsDmodField.lean#L20) · [Source degree field](../../../../../refer/iut/Iut/Tripod/CurveFacts.lean#L507) · [Source field of moduli bound](../../../../../refer/iut/Iut/Tripod/CurveFacts.lean#L207)
