# Wild ramification in the Legendre tower

## English

Fix the Legendre curve attached to a point $x$, a prime $\ell\geq 7$, and its mod-$\ell$ representation. Write $K/F/U$ for its torsion field, field of definition, and tripodal field. Let $v,w,u$ be the corresponding places of $K,F,U$ and put $p=\operatorname{reschar}(v)$.

The relative degree $[F:U]$ divides $184320$. The Galois action on the signs of three selected square roots and on the 3- and 5-torsion is faithful, since these elements generate $F$ over $U$. This gives the degree divisibility by $2^3\lvert\mathrm{GL}_2(\mathbf F_3)\rvert\lvert\mathrm{GL}_2(\mathbf F_5)\rvert=184320$. The mod-$\ell$ representation gives $[K:F]\mid(\ell^2-1)(\ell^2-\ell)$.

For $p\neq\ell$, $K/F$ is tame at $v$. At $p=2$ this follows from the inertia involution argument. At odd $p\neq\ell$ the index is one at a good place. At a bad place every inertia element has $\ell$-th power one, so Cauchy's theorem excludes inertia elements of order $p$. Each relative index divides its respective extension degree. Multiplicativity of the indices gives

$$
\operatorname{ord}_p(e(v/u))\le
\begin{cases}
12 & p=2,\\
2 & p=3,\\
1 & p\in\{5,\ell\},\\
0 & p\notin\{2,3,5,\ell\}.
\end{cases}
$$

The theorem `padicValNat_relRamIdx_le` supplies this bound for the torsion field used by `TowerLocalFacts`. [Degree divisibility](../../../../Solutions/Source_TripodTpdDegree.lean#L22) · [Wild constants](../../../../Solutions/Source_ReferenceIutTowerWildBound.lean#L69) · [Tower bound](../../../../Solutions/Source_TripodWildRamIdx.lean#L48)

MCP-CI leaf checks passed for TameTwo and WildRamIdx. [TameTwo · ci-022406-aa16afa6](../receipts/round-ci-022406-aa16afa6-result.json) · [WildRamIdx · ci-022410-f598c120](../receipts/round-ci-022410-f598c120-result.json)

## 简体中文

固定点 $x$ 的 Legendre 曲线、素数 $\ell\geq 7$ 及相应的模 $\ell$ 表示。记 $K/F/U$ 为挠点域、定义域及三足域构成的域塔，$v,w,u$ 为三个域上对应的处，$p$ 为 $v$ 的剩余特征。

相对次数 $[F:U]$ 整除 $184320$。伽罗瓦群作用于三个所选平方根的符号以及 3 和 5 挠点。这些元素生成 $F/U$，所以作用忠实。由此得到相对次数整除 $2^3\lvert\mathrm{GL}_2(\mathbf F_3)\rvert\lvert\mathrm{GL}_2(\mathbf F_5)\rvert=184320$。模 $\ell$ 表示给出 $[K:F]\mid(\ell^2-1)(\ell^2-\ell)$。

若 $p\neq\ell$，则 $K/F$ 在 $v$ 处至多有温和分歧。$p=2$ 时使用惯性对合的结论。$p$ 为异于 $\ell$ 的奇素数时，良处的分歧指数为一。在坏处，每个惯性元素的 $\ell$ 次幂为一，由 Cauchy 定理排除阶为 $p$ 的惯性元素。两层分歧指数分别整除相应的域扩张次数。由分歧指数的乘法性得到

$$
\operatorname{ord}_p(e(v/u))\le
\begin{cases}
12 & p=2,\\
2 & p=3,\\
1 & p\in\{5,\ell\},\\
0 & p\notin\{2,3,5,\ell\}.
\end{cases}
$$

`padicValNat_relRamIdx_le` 为 `TowerLocalFacts` 所用的同一挠点域提供此界。 [次数整除](../../../../Solutions/Source_TripodTpdDegree.lean#L22) · [野分歧常数](../../../../Solutions/Source_ReferenceIutTowerWildBound.lean#L69) · [整塔界](../../../../Solutions/Source_TripodWildRamIdx.lean#L48)

TameTwo 和 WildRamIdx 的 MCP-CI 叶检查均已通过。 [TameTwo · ci-022406-aa16afa6](../receipts/round-ci-022406-aa16afa6-result.json) · [WildRamIdx · ci-022410-f598c120](../receipts/round-ci-022410-f598c120-result.json)

## 日本語

点 $x$ に付随する Legendre 曲線、素数 $\ell\geq 7$、およびその mod $\ell$ 表現を固定する。捩れ点体、定義体、三脚体からなる塔を $K/F/U$ と書く。対応する素点を $v,w,u$ とし、$v$ の剰余標数を $p$ とする。

相対次数 $[F:U]$ は $184320$ を割る。Galois 群は選んだ三つの平方根の符号および 3 と 5 の捩れ点に作用する。これらの元は $F/U$ を生成するため、この作用は忠実である。したがって相対次数は $2^3\lvert\mathrm{GL}_2(\mathbf F_3)\rvert\lvert\mathrm{GL}_2(\mathbf F_5)\rvert=184320$ を割る。mod $\ell$ 表現から $[K:F]\mid(\ell^2-1)(\ell^2-\ell)$ を得る。

$p\neq\ell$ なら、$K/F$ は $v$ で順分岐である。$p=2$ では惰性群の位数 2 の元に関する結果を使う。$p$ が $\ell$ と異なる奇素数の場合、良い素点では分岐指数は 1 である。悪い素点では惰性群の各元の $\ell$ 乗が単位元なので、Cauchy の定理により位数 $p$ の元は存在しない。各段の分岐指数はその拡大次数を割る。分岐指数の乗法性から

$$
\operatorname{ord}_p(e(v/u))\le
\begin{cases}
12 & p=2,\\
2 & p=3,\\
1 & p\in\{5,\ell\},\\
0 & p\notin\{2,3,5,\ell\}.
\end{cases}
$$

`padicValNat_relRamIdx_le` は `TowerLocalFacts` が用いる同じ捩れ点体に対してこの上界を与える。 [次数の整除](../../../../Solutions/Source_TripodTpdDegree.lean#L22) · [野分岐定数](../../../../Solutions/Source_ReferenceIutTowerWildBound.lean#L69) · [塔における上界](../../../../Solutions/Source_TripodWildRamIdx.lean#L48)

TameTwo と WildRamIdx の MCP-CI 葉モジュール検査はいずれも通過した。 [TameTwo · ci-022406-aa16afa6](../receipts/round-ci-022406-aa16afa6-result.json) · [WildRamIdx · ci-022410-f598c120](../receipts/round-ci-022410-f598c120-result.json)
