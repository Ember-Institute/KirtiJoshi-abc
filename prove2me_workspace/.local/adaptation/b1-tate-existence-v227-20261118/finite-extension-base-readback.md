# English

For an extension of number fields $K/k$, a finite place $w$ of $K$ determines a unique finite place $v$ of $k$ below it. Contract the prime ideal of $w$ along the map of rings of integers. The contraction is prime and nonzero because the integer ring extension is integral. The relation that $w$ lies over $v$ identifies the prime ideal of $v$ with this contraction, which gives uniqueness.

For a pair $w$ over $v$, the relative ramification index $e(w/v)$ is nonzero. The multiplicative valuation of the image of $x\in k$ in $K$ is the valuation of $x$ at $v$ raised to $e(w/v)$. The relative residue degree records the degree of the extension of the corresponding residue fields. These two integers will enter the absolute value comparison in the finite height proof. The formal sources are `PlaceUnder.lean:30`, `ValuationTransfer.lean:65` and `Height.lean:141`. Mochizuki's *Arithmetic Elliptic Curves in General Position*, §3, gives the local field context.

# 简体中文

设 $K/k$ 是数域扩张。$K$ 的有限处 $w$ 下方有唯一的 $k$ 的有限处 $v$。沿整数环之间的映射收缩 $w$ 对应的素理想。由于整数环扩张是整扩张，收缩所得理想仍为非零素理想。若 $w$ 位于 $v$ 上方，则 $v$ 对应的素理想就是这个收缩理想，所以 $v$ 唯一。

设 $w$ 位于 $v$ 上方。相对分歧指数 $e(w/v)$ 非零。对 $x\in k$，它在 $K$ 中的像在 $w$ 处的乘法赋值，等于 $x$ 在 $v$ 处的乘法赋值的 $e(w/v)$ 次幂。相对剩余次数记录相应剩余域的扩张次数。这两个整数用于后续有限高度证明中的绝对值换算。

# 日本語

$K/k$ を数体の拡大とする。$K$ の有限素点 $w$ の下には $k$ の有限素点 $v$ がただ一つ存在する。整数環の写像に沿って $w$ に対応する素イデアルを縮約する。整数環の拡大は整拡大なので、縮約は非零素イデアルである。$w$ が $v$ の上にあるならば、$v$ の素イデアルはこの縮約に等しく、従って $v$ は一意に定まる。

$w$ が $v$ の上にあるとき、相対分岐指数 $e(w/v)$ は零でない。$x\in k$ の像の $w$ における乗法的付値は、$x$ の $v$ における乗法的付値の $e(w/v)$ 乗である。相対剰余次数は、対応する剰余体の拡大次数を表す。これら二つの整数は、有限部分の高さを比較する際の絶対値の換算に用いられる。
