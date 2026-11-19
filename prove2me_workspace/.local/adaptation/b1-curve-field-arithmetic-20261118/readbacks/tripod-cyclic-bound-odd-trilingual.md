# The fixed-constant cyclic bound away from two

Upstream revision `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`. Public theorem source SHA-256 `a7a45d3da3c54d633941395644de7aab27442503317e29dd1a37a9faba180aa3`. [Public theorem](../../../../Theorems/Thm_AbcAdaptation_Tripod_cyclicBoundOdd.lean#L19) · [Leaf build ci-022822-9f139553](../receipts/round-ci-022822-9f139553-result.json)

## English

Fix a curve provider $P$, a `CompactlyBounded` datum $K$ with bound $c=K.c$, and a natural number $d$. The public theorem `cyclicBoundOdd` gives `CyclicBoundOddHyp` at a fixed constant. Take $x\in K.\mathrm{set}$ with $[\mathbb Q(\lambda):\mathbb Q]\le d$ for its parameter $\lambda$, a prime $\ell\ge7$, and a Galois-stable subgroup of order $\ell$ in the geometric points of the curve supplied at $x$. Assume (P2), which requires $\ell\nmid (P.\mathrm{localData}(x)).\mathrm{hv}(w)$ at every place $w$ in the bad locus of that local height data. Write $h(x)=P.h(x)$ and $h_2(x)=(P.\mathrm{localData}(x)).\mathrm{heightEq}(2)$. The conclusion is

$$
\frac{\ell-2}{24}\bigl(h(x)-h_2(x)\bigr)\le 2\log\ell+T_K,\qquad
T_K=\frac{2\log(32C_0)+6c+4\log 4}{6}.
$$

[Degree condition](../../../../Definitions/Def_AbcTripod.lean#L67) · [Cyclic subgroup](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean#L44) · [Statement](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts.lean#L24) · [Reference theorem](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/CyclicIsogeny.lean#L1064)

The general complex torsion theorem `exists_torsion_x_bound` gives `legendre_torsion_x_le c` by specialization to the bounded Legendre family. The specialization gives a nonnegative witness $B$ for the uniform bound $|a|\le BN^2$ on the first coordinate of each nonsingular affine point killed by $N\ge 1$. This bound applies when both parameter logarithms have absolute value at most $c$. The definition `torsionConst` uses classical choice on that existence theorem and sets $C_0=\max(1,B)$ for the chosen witness. The proof uses this same $C_0$ in `Cyclic.main_bound` and in $T_K$. [Complex torsion theorem](../../../../Theorems/Thm_AbcAdaptation_Reference_Heights_exists_torsion_x_bound.lean#L9) · [Legendre specialization](../../../../Theorems/Thm_AbcAdaptation_Tripod_legendre_torsion_x_le.lean#L16) · [Chosen constant](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound.lean#L30) · [Assembly](../../../../Solutions/Source_TripodCyclicBoundFromSource.lean#L19)

At each place of the $\ell$-torsion field above `VBadOdd`, the place below it in the curve's base field belongs to the multiplicative reduction locus. There the local height exponent is the order of the Tate parameter, so (P2) supplies the nondivisibility required by `cyclicLocalGraphLine`. The local proof uses an element of order $\ell$ in the decomposition group. If the given subgroup and the graph line differed, they would span the whole $\ell$-torsion. The element fixes each line pointwise since it preserves the line and its order divides $\ell$, while the automorphism group of a line of order $\ell$ has order $\ell-1$. This contradicts the faithful action on the torsion field. The resulting graph-line equality supplies the hypothesis of `Cyclic.main_bound`. Divide the Vélu inequality by six. Use $h(x)-h_2(x)\ge0$ to decrease $(\ell-1)/24$ to $(\ell-2)/24$, and use $\log\ell\ge0$ to bound $(10/6)\log\ell$ by $2\log\ell$. [Local theorem](../../../../Theorems/Thm_AbcAdaptation_Tripod_cyclicLocalGraphLine.lean#L17) · [Decomposition group argument](../../../../Solutions/Source_TripodCyclicLocal.lean#L180) · [Global Vélu bound](../../../../Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean#L106) · [Coefficient comparison](../../../../Solutions/Source_TripodCyclicBoundOdd.lean#L188)

MCP-CI review `ci-022825-5942080c` exited with code 0 after importing Checks, ImportAudit, Act1Scene1, and AxiomAudit. Its axiom output lists only `propext`, `Classical.choice`, and `Quot.sound` for each of `exists_torsion_x_bound`, `legendre_torsion_x_le`, `cyclicLocalGraphLine`, and `cyclicBoundOdd`. [Review source](../ReviewTripodCyclicBound.lean#L1) · [Review receipt](../receipts/round-ci-022825-5942080c-result.json)

## 中文

固定曲线数据提供者 $P$、界为 $c=K.c$ 的紧致有界子集数据 $K$ 和自然数 $d$。公开定理 `cyclicBoundOdd` 以固定常数给出 `CyclicBoundOddHyp`。取 $x\in K.\mathrm{set}$，其参数 $\lambda$ 满足 $[\mathbb Q(\lambda):\mathbb Q]\le d$。取素数 $\ell\ge7$，并假设 $P$ 在 $x$ 处给出的曲线有一个阶为 $\ell$ 的 Galois 稳定几何点子群。假设 (P2) 要求局部高度数据的坏位集合中每个 $w$ 都满足 $\ell\nmid (P.\mathrm{localData}(x)).\mathrm{hv}(w)$。记 $h(x)=P.h(x)$，$h_2(x)=(P.\mathrm{localData}(x)).\mathrm{heightEq}(2)$，则

$$
\frac{\ell-2}{24}\bigl(h(x)-h_2(x)\bigr)\le 2\log\ell+T_K,\qquad
T_K=\frac{2\log(32C_0)+6c+4\log 4}{6}.
$$

[次数条件](../../../../Definitions/Def_AbcTripod.lean#L67) · [循环子群](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean#L44) · [命题](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts.lean#L24) · [参考定理](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/CyclicIsogeny.lean#L1064)

把一般复挠点定理 `exists_torsion_x_bound` 专门用于有界的 Legendre 族，得到 `legendre_torsion_x_le c`。当参数的两个对数的绝对值均不超过 $c$ 时，这个定理给出一个非负的 $B$，使每个被 $N\ge1$ 消去的非奇异仿射点的横坐标满足 $|a|\le BN^2$。定义 `torsionConst` 从该存在性定理用经典选择取 $B$，并置 $C_0=\max(1,B)$。证明在 `Cyclic.main_bound` 和 $T_K$ 中使用同一个 $C_0$。 [复挠点定理](../../../../Theorems/Thm_AbcAdaptation_Reference_Heights_exists_torsion_x_bound.lean#L9) · [Legendre 特化](../../../../Theorems/Thm_AbcAdaptation_Tripod_legendre_torsion_x_le.lean#L16) · [选定常数](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound.lean#L30) · [定理组合](../../../../Solutions/Source_TripodCyclicBoundFromSource.lean#L19)

对 $\ell$-挠点域中位于 `VBadOdd` 上方的每个位，曲线底域中位于其下的位属于乘法约化位集。该处的局部高度指数等于 Tate 参数的阶，所以 (P2) 给出 `cyclicLocalGraphLine` 所需的不可整除条件。局部证明取分解群中阶为 $\ell$ 的元素。若给定子群与图像直线不同，它们便张成整个 $\ell$-挠点群。该元素保持每条直线，且其阶整除 $\ell$，而阶为 $\ell$ 的直线的自同构群阶为 $\ell-1$，因此该元素逐点固定两条直线。这与挠点域上的忠实作用矛盾。由此所得的图像直线等式用作 `Cyclic.main_bound` 的假设。将 Vélu 不等式除以六，由 $h(x)-h_2(x)\ge0$ 将系数 $(\ell-1)/24$ 降为 $(\ell-2)/24$，再由 $\log\ell\ge0$ 将 $(10/6)\log\ell$ 放宽为 $2\log\ell$。 [局部定理](../../../../Theorems/Thm_AbcAdaptation_Tripod_cyclicLocalGraphLine.lean#L17) · [分解群论证](../../../../Solutions/Source_TripodCyclicLocal.lean#L180) · [全局 Vélu 界](../../../../Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean#L106) · [系数比较](../../../../Solutions/Source_TripodCyclicBoundOdd.lean#L188)

MCP-CI 审查 `ci-022825-5942080c` 导入 Checks、ImportAudit、Act1Scene1 和 AxiomAudit，退出码为 0。公理输出显示 `exists_torsion_x_bound`、`legendre_torsion_x_le`、`cyclicLocalGraphLine` 和 `cyclicBoundOdd` 各自只依赖 `propext`、`Classical.choice` 与 `Quot.sound`。 [审查源文件](../ReviewTripodCyclicBound.lean#L1) · [审查回执](../receipts/round-ci-022825-5942080c-result.json)

## 日本語

曲線データの供給元 $P$、上界 $c=K.c$ を持つコンパクト有界集合のデータ $K$、自然数 $d$ を固定する。公開定理 `cyclicBoundOdd` は、固定した定数について `CyclicBoundOddHyp` を与える。$x\in K.\mathrm{set}$ を取り、そのパラメータ $\lambda$ は $[\mathbb Q(\lambda):\mathbb Q]\le d$ を満たすとする。素数 $\ell\ge7$ を取り、$x$ で与えられる曲線の幾何的な点の群に、位数 $\ell$ の Galois 安定部分群があるとする。仮定 (P2) は、局所高さデータの悪い素点の集合に属する各 $w$ について $\ell\nmid (P.\mathrm{localData}(x)).\mathrm{hv}(w)$ を要求する。$h(x)=P.h(x)$、$h_2(x)=(P.\mathrm{localData}(x)).\mathrm{heightEq}(2)$ と書くと、次が成り立つ。

$$
\frac{\ell-2}{24}\bigl(h(x)-h_2(x)\bigr)\le 2\log\ell+T_K,\qquad
T_K=\frac{2\log(32C_0)+6c+4\log 4}{6}.
$$

[次数の条件](../../../../Definitions/Def_AbcTripod.lean#L67) · [巡回部分群](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean#L44) · [命題](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts.lean#L24) · [参照元の定理](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/CyclicIsogeny.lean#L1064)

複素等分点に関する一般定理 `exists_torsion_x_bound` を有界な Legendre 族に特殊化して、`legendre_torsion_x_le c` を得る。パラメータに関する二つの対数の絶対値が $c$ 以下のとき、$N\ge1$ 倍で消える各非特異アフィン点の第一座標 $a$ について $|a|\le BN^2$ を満たす非負の $B$ が得られる。定義 `torsionConst` はこの存在定理から古典的選択で $B$ を取り、$C_0=\max(1,B)$ とする。証明は `Cyclic.main_bound` と $T_K$ に同じ $C_0$ を用いる。 [複素等分点の定理](../../../../Theorems/Thm_AbcAdaptation_Reference_Heights_exists_torsion_x_bound.lean#L9) · [Legendre 族への特殊化](../../../../Theorems/Thm_AbcAdaptation_Tripod_legendre_torsion_x_le.lean#L16) · [選んだ定数](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound.lean#L30) · [定理の組み立て](../../../../Solutions/Source_TripodCyclicBoundFromSource.lean#L19)

$\ell$ 等分点体の `VBadOdd` 上の各素点について、その下にある曲線の基礎体の素点は乗法的還元をもつ。その素点での局所高さの指数は Tate パラメータの位数に等しく、(P2) から `cyclicLocalGraphLine` の非可除条件が従う。局所的な証明では、分解群から位数 $\ell$ の元を取る。与えられた部分群とグラフ直線が異なるならば、二つは $\ell$ 等分点全体を生成する。この元は各直線を保ち、その位数は $\ell$ を割る。位数 $\ell$ の直線の自己同型群の位数は $\ell-1$ なので、この元は二つの直線を各点ごとに固定する。これは等分点体の Galois 群の作用が忠実であることに反する。得られたグラフ直線との等式を `Cyclic.main_bound` の仮定に用いる。Vélu の不等式を 6 で割り、$h(x)-h_2(x)\ge0$ により $(\ell-1)/24$ を $(\ell-2)/24$ に下げ、$\log\ell\ge0$ により $(10/6)\log\ell$ を $2\log\ell$ で抑える。 [局所定理](../../../../Theorems/Thm_AbcAdaptation_Tripod_cyclicLocalGraphLine.lean#L17) · [分解群の議論](../../../../Solutions/Source_TripodCyclicLocal.lean#L180) · [大域的 Vélu 評価](../../../../Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean#L106) · [係数の比較](../../../../Solutions/Source_TripodCyclicBoundOdd.lean#L188)

MCP-CI レビュー `ci-022825-5942080c` は Checks、ImportAudit、Act1Scene1、AxiomAudit をインポートし、終了コード 0 で完了した。公理の出力では、`exists_torsion_x_bound`、`legendre_torsion_x_le`、`cyclicLocalGraphLine`、`cyclicBoundOdd` の各定理について `propext`、`Classical.choice`、`Quot.sound` だけが示された。 [レビューのソース](../ReviewTripodCyclicBound.lean#L1) · [レビュー結果](../receipts/round-ci-022825-5942080c-result.json)
