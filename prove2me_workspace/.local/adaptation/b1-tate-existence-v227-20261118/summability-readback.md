# English

Let $K$ be an ultrametric normed field, and let $q$ be the value of a Tate parameter over $K$, so that $q\ne0$ and $\lVert q\rVert<1$. For every natural number $n$, `norm_one_sub_qpow` gives $\lVert 1-q^{n+1}\rVert=1$. The norm of $q^{n+1}$ is strictly smaller than the norm of $1$, so the ultrametric equality for summands of unequal norm applies. `one_sub_qpow_ne_zero` then gives $1-q^{n+1}\ne0$.

If $K$ is also complete, `eisenstein_summand_summable` gives, for each natural number $k$, summability of the family with terms $((n+1):K)^k q^{n+1}/(1-q^{n+1})$. Each term has norm at most $\lVert q\rVert^{n+1}$: the denominator has norm $1$, and the norm of the natural-number cast is at most $1$. The comparison series is geometric. These estimates are used to bound the discriminant and to compare series evaluated at two parameters.

# 简体中文

设 $K$ 是超度量赋范域，$q$ 是 $K$ 上一个 Tate 参数的取值，满足 $q\ne0$ 及 $\lVert q\rVert<1$。对每个自然数 $n$，`norm_one_sub_qpow` 给出 $\lVert 1-q^{n+1}\rVert=1$。这是因为 $q^{n+1}$ 的范数严格小于 $1$ 的范数，而超度量下范数不等的两项相加，其和的范数等于较大的范数。`one_sub_qpow_ne_zero` 由此得到 $1-q^{n+1}\ne0$。

若 $K$ 还完备，则 `eisenstein_summand_summable` 表明：对每个自然数 $k$，以 $((n+1):K)^k q^{n+1}/(1-q^{n+1})$ 为通项的族可求和。分母的范数为 $1$，自然数在域中对应元素的范数至多为 $1$，所以每项的范数至多为 $\lVert q\rVert^{n+1}$，可与收敛的几何级数比较。这些估计用于控制判别式，也用于比较两个参数对应的级数。

# 日本語

$K$ を超距離をもつノルム体とし、$q$ を $K$ 上の Tate パラメータの値とする。このとき $q\ne0$ かつ $\lVert q\rVert<1$ である。`norm_one_sub_qpow` によれば、任意の自然数 $n$ に対して $\lVert 1-q^{n+1}\rVert=1$ となる。$q^{n+1}$ のノルムが $1$ のノルムより真に小さいため、和のノルムは二項のうち大きい方のノルムに等しい。したがって `one_sub_qpow_ne_zero` により $1-q^{n+1}\ne0$ となる。

さらに $K$ が完備ならば、`eisenstein_summand_summable` により、任意の自然数 $k$ に対して一般項が $((n+1):K)^k q^{n+1}/(1-q^{n+1})$ である族は総和可能である。分母のノルムは $1$ であり、自然数を $K$ に移した元のノルムは $1$ 以下である。したがって各項のノルムは $\lVert q\rVert^{n+1}$ 以下であり、収束する等比級数と比較できる。これらの評価は判別式の評価と、二つのパラメータにおける級数の比較に用いられる。
