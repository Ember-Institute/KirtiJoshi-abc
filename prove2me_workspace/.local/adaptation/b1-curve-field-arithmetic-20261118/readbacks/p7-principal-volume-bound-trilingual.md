# Principal volume bound

## logQ_le_of_globalVolume_bound

### English

Let $n,H$ be real numbers. If $n\ge3$ and $(n-1)(2n+5)H\le6(2n+1)(n+3)\log\pi$, where $\log$ is the natural logarithm, then $H\le(126/11)\log\pi$.

### 中文

设 $n,H$ 为实数，其中 $\log$ 表示自然对数。若 $n\ge3$ 且 $(n-1)(2n+5)H\le6(2n+1)(n+3)\log\pi$，则 $H\le(126/11)\log\pi$。

### 日本語

$n,H$ を実数とし、$\log$ を自然対数とする。$n\ge3$ かつ $(n-1)(2n+5)H\le6(2n+1)(n+3)\log\pi$ ならば、$H\le(126/11)\log\pi$ が成り立つ。

[Lean scalar theorem](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCor312PrincipalVolumeBound.lean:10)

## Universal source P7 premise in the high-height theorem

### English

Fix the curve provider, its cyclic bounds and core finiteness hypotheses, and the anabelian existence data for the fixed anabelian and tempered geometries. The high-height theorem takes the following premise for every compactly bounded set $K$, every natural-number degree bound $d$, and every variant bundle $X$ over those geometries. Take a point of the three-punctured projective line that lies in $K$, has degree at most $d$, and lies outside the core exception set. Let $\ell\ge7$ be a prime satisfying the P7 local and image conditions, and assume the curve has at least four rational points killed by multiplication by $2$. For the concrete bundle $X$ of this point and prime, the premise says that its signed q-pilot log-volume is at most its theta-hull log-volume. The prime conditions are that $\ell$ divides none of the valuation orders of the Tate parameters at bad places, the orders at residue characteristic $\ell$ are strictly less than the square root of the point’s height, some bad place has residue characteristic different from both $2$ and $\ell$, and the mod-$\ell$ image contains $\operatorname{SL}_2(\mathbb F_\ell)$. The signed term is the normalized bad-place q-degree multiplied by $-1/(2\ell)$. The hull term averages, over the capsules, the sums of packet log-volumes over all rational places.

### 中文

固定曲线提供器、其循环子群界和核心例外集有限性假设，以及固定的远阿贝尔几何与缓和几何的远阿贝尔存在性数据。高高度定理以如下全称命题为前提。对任一紧致有界子集 $K$、自然数次数上界 $d$ 以及上述几何上的变体数据 $X$，若 $X$ 来自 $K$ 中次数至多为 $d$ 且不在核心例外集内的三穿孔直线点、满足 P7 局部与像条件的素数 $\ell\ge7$，且相应曲线上乘以 $2$ 得到零元的有理点至少有四个，则 $X$ 的带符号 q-pilot 对数体积小于等于其 θ 包络的对数体积。素数条件要求 $\ell$ 不整除任何坏处的 Tate 参数的赋值阶数，剩余特征为 $\ell$ 时该阶数严格小于点高度的平方根，至少有一处坏处的剩余特征既非 $2$ 也非 $\ell$，并且模 $\ell$ 表示的像包含 $\operatorname{SL}_2(\mathbb F_\ell)$。带符号项为坏处归一化 q 次数乘以 $-1/(2\ell)$。包络项先对每个胶囊在所有有理位上求和，再对胶囊取平均。

### 日本語

曲線の供給データ、巡回部分群の評価とコアの例外集合の有限性、および固定した遠アーベル幾何とテンパード幾何に対する遠アーベル的存在データを固定する。十分に高さの大きい点についての定理は、任意のコンパクト有界集合 $K$、自然数の次数上限 $d$、およびこれらの幾何上の任意の変種データ $X$ について、次の前提を置く。$X$ が、$K$ に属しコアの例外集合の外にある次数 $d$ 以下の三点除去射影直線の点、P7 の局所条件と像の条件を満たす素数 $\ell\ge7$ から構成され、対応する曲線上に $2$ 倍が零となる有理点が四つ以上あるならば、$X$ の符号付き q パイロットの対数体積は θ 包の対数体積以下である。素数条件は、どの悪い素点での Tate パラメータの付値次数も $\ell$ で割り切れず、剰余標数 $\ell$ の場合の付値次数は点の高さの平方根より真に小さく、剰余標数が $2$ と $\ell$ のいずれとも異なる悪い素点が存在し、法 $\ell$ の表現の像が $\operatorname{SL}_2(\mathbb F_\ell)$ を含むことである。符号付きの項は、悪い素点における正規化された q 次数に $-1/(2\ell)$ を掛けた値である。包の項は、カプセルごとにすべての有理素点でのパケット対数体積を合計し、その和をカプセルについて平均した値である。

[Universal premise](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCanonicalCorollary22.lean:77) · [Source P7 predicate](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodP7.lean:27) · [Two-torsion condition](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutThetaLocalRoots.lean:34) · [Variant inequality](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_Statement.lean:113) · [Signed q-pilot](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_LeftHandSide.lean:110) · [Hull average](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_RightHandSide.lean:129)
