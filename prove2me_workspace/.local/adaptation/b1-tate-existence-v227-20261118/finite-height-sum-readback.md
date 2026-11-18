# English

Let $E/F$ be the curve selected by the provider at $x$. Multiplying the provider's height $h(x)$ by $[F:\mathbb Q]$ gives the sum of the local Tate contributions over the finite places of multiplicative reduction. At each such place this summand is the positive logarithm of the local absolute value of $j(E)$. At the other finite places that logarithm vanishes. Hence $[F:\mathbb Q]h(x)$ equals the finite height of $j(E)$ computed over $F$.

The proof follows `Iut/Tripod/Height.lean:582` and `Iut/Implication/PrimeSelection.lean:187`. Definition 3.3 of Mochizuki's *Arithmetic Elliptic Curves in General Position* provides the context of the arithmetic degree of the $q$ object.

# 简体中文

设 $E/F$ 是供应数据为点 $x$ 选定的曲线。将高度 $h(x)$ 乘以数域次数 $[F:\mathbb Q]$，得到所有乘法约化有限处的 Tate 局部贡献之和。每项恰是该处 $j(E)$ 的绝对值的正部对数；其余有限处的正部对数为零。因此 $[F:\mathbb Q]h(x)$ 等于在 $F$ 上计算的 $j(E)$ 的有限高度。望月新一《处于一般位置的算术椭圆曲线》定义 3.3 给出了 $q$ 对象算术次数的背景。

# 日本語

点 $x$ に対して供給データが選ぶ曲線を $E/F$ とする。高さ $h(x)$ に体の拡大次数 $[F:\mathbb Q]$ を掛けると、乗法的還元をもつ有限素点における Tate の局所寄与の和が得られる。各項は対応する素点での $j(E)$ の絶対値の対数の正部分に等しい。それ以外の有限素点ではこの正部分が零である。したがって、$[F:\mathbb Q]h(x)$ は $F$ 上で計算した $j(E)$ の有限部分の高さに等しい。$q$ 対象の算術次数については、望月新一の *Arithmetic Elliptic Curves in General Position* 定義 3.3 を参照。
