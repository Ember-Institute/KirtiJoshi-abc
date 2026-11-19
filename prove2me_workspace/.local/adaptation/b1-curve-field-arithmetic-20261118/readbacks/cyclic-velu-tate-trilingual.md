# Source_TripodCyclicVeluTate.lean

Upstream revision `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`. Adapted source SHA-256 `ebb77ce3211af201bc311d531f07c6254918165d36b9d1a5f5ff2432537cf66f`. [Source header](../../../../Solutions/Source_TripodCyclicVeluTate.lean#L6)

## English

### `tate_bound`

Fix a tripod point $x$ and let $E/F$ be the elliptic curve that $P$ supplies at $x$. For an odd prime $\ell$, let $L$ be the torsion field, the fixed field of the kernel of the mod-$\ell$ representation supplied by $P$. Let $H\subset E(\overline F)$ be an additive subgroup of order $\ell$. The theorem takes a `Fintype` instance on its pullback $H_L\subset E(L)$, and `card_HL` gives $\#H_L=\ell$. For $i=1,2$, let $r_i=\operatorname{veluRatio}(H_L,T_i,R_i)$. The designated points $T_1,T_2$ are distinct and have order two, and $2R_i=T_i$. Write $\iota\colon F\hookrightarrow L$ and $j=j(E)$.

Let $w$ be a finite place of $L$ above a place in `VBadOdd` of the field of moduli of $E$. A place in `VBadOdd` has odd residue characteristic and has at least one place of $F$ above it. The curve has multiplicative reduction at every such place of $F$. This includes the case of residue characteristic $\ell$. At each $w$ above `VBadOdd`, `IsGraphLineOdd` requires $H_L$ to equal the pullback of the Tate graph line from the completion $L_w$. [Odd places](../../../../../refer/iut/Iut/Tripod/CyclicTorsion.lean#L49) · [Graph-line condition](../../../../Solutions/Source_TripodCyclicBoundOdd.lean#L145)

The theorem gives the bound at $w$.

$$
(|r_1|_w|r_2|_w)^4|\iota(j)|_w^{\ell-1}\le 1.
$$

Let $q_w$ be the Tate parameter at $w$. The norm in $L_w$ restricts to $|\cdot|_w$ on $L$. Odd residue characteristic gives $\|2\|=1$, so the proof applies `ratio_mul_bound` with the cardinality and graph-line conditions to get

$$
(|r_1|_w|r_2|_w)^4\le \|q_w\|^{\ell-1}.
$$

The adapted proof uses `variableChange_j` and `map_j` to identify the Tate $j$-invariant with the image of $j$ in $L_w$. The Tate identity gives $|\iota(j)|_w=\|q_w\|^{-1}$. Multiply the estimate by $|\iota(j)|_w^{\ell-1}$ and use $\|q_w\|>0$ to get the bound in the upstream theorem. [Adapted theorem](../../../../Solutions/Source_TripodCyclicVeluTate.lean#L72) · [Upstream theorem](../../../../../refer/iut/Iut/Tripod/CyclicIsogeny.lean#L425)

### `finite_tate`

Keep the hypotheses on $\ell$, $H$, and the graph line. Take $\rho\in F$ with the explicit hypothesis `hρ` that $\iota(\rho)=r_1r_2$ in $L$. Let $v$ be a finite place of $F$ of multiplicative reduction in the curve's `badAll`. Assume $v$ has odd residue characteristic. The corresponding upstream theorem gives

$$
|\rho|_v^4|j|_v^{\ell-1}\le 1.
$$

Choose $w$ of $L$ above $v$. The private helper `isBadPlace_of_liesOver` uses the provider's curve arithmetic to find a place in `VBadOdd` below $v$ and composes the two lies-over relations. These steps correspond to upstream `exists_mem_VBadOdd` and `FinitePlace.liesOver_trans`. [Adapted helper](../../../../Solutions/Source_TripodCyclicVeluTate.lean#L38) · [Upstream place existence](../../../../../refer/iut/Iut/Tripod/CyclicTorsion.lean#L58)

For $y\in F$, `apply_algebraMap_eq_pow` gives $|\iota(y)|_w=|y|_v^d$, where $d=\operatorname{relLocalDeg}(w,v)=e(w/v)f(w/v)>0$. Here $e(w/v)$ is the ramification index and $f(w/v)$ is the residue field degree. Apply `tate_bound` at $w$. Use `hρ` and multiplicativity of $|\cdot|_w$ to replace $|r_1|_w|r_2|_w$ by $|\iota(\rho)|_w$. Transport the values of $\rho$ and $j$ to get

$$
\bigl(|\rho|_v^4|j|_v^{\ell-1}\bigr)^d\le 1.
$$

A positive integer power is strictly increasing on the nonnegative reals, so the bound follows. [Adapted theorem](../../../../Solutions/Source_TripodCyclicVeluTate.lean#L132) · [Upstream theorem](../../../../../refer/iut/Iut/Tripod/CyclicIsogeny.lean#L605) · [Absolute-value transport](../../../../Solutions/Source_TripodRelativeAbsoluteValue.lean#L17)

## 中文

### `tate_bound`

固定 tripod 点 $x$，记 $P$ 在 $x$ 处给出的椭圆曲线为 $E/F$。对奇素数 $\ell$，记 $P$ 所给模 $\ell$ 表示的核的固定域，即挠点域，为 $L$。取阶为 $\ell$ 的加法子群 $H\subset E(\overline F)$。定理假定其拉回 $H_L\subset E(L)$ 带有 `Fintype` 实例，由 `card_HL` 得 $\#H_L=\ell$。对 $i=1,2$，令 $r_i=\operatorname{veluRatio}(H_L,T_i,R_i)$。指定的 $T_1,T_2$ 是两个不同的二阶点，且 $2R_i=T_i$。记包含映射为 $\iota\colon F\hookrightarrow L$，并记 $j=j(E)$。

取 $L$ 的有限位 $w$，使其位于 $E$ 的模域中某个 `VBadOdd` 位之上。`VBadOdd` 中的位具有奇剩余特征，在 $F$ 中至少有一个上方位，且 $E$ 在每个这样的上方位都有乘法约化。这包括剩余特征为 $\ell$ 的情形。`IsGraphLineOdd` 要求对每个在 `VBadOdd` 上方的 $w$，$H_L$ 等于从完备化 $L_w$ 上的 Tate 图像直线拉回所得的子群。 [奇剩余特征位](../../../../../refer/iut/Iut/Tripod/CyclicTorsion.lean#L49) · [图像直线条件](../../../../Solutions/Source_TripodCyclicBoundOdd.lean#L145)

定理给出 $w$ 处的界。

$$
(|r_1|_w|r_2|_w)^4|\iota(j)|_w^{\ell-1}\le 1.
$$

记 $w$ 处的 Tate 参数为 $q_w$。$L_w$ 上的范数限制到 $L$ 即为 $|\cdot|_w$。奇剩余特征给出 $\|2\|=1$，因此结合子群的基数和图像直线条件，应用 `ratio_mul_bound` 得

$$
(|r_1|_w|r_2|_w)^4\le \|q_w\|^{\ell-1}.
$$

适配后的证明用 `variableChange_j` 和 `map_j` 将 Tate 曲线的 $j$-不变量识别为 $j$ 在 $L_w$ 中的像。Tate 恒等式给出 $|\iota(j)|_w=\|q_w\|^{-1}$。将估计两边乘以 $|\iota(j)|_w^{\ell-1}$，由 $\|q_w\|>0$ 得到上游同名定理的界。 [适配后的定理](../../../../Solutions/Source_TripodCyclicVeluTate.lean#L72) · [上游定理](../../../../../refer/iut/Iut/Tripod/CyclicIsogeny.lean#L425)

### `finite_tate`

沿用关于 $\ell$、$H$ 和图像直线的假设。取 $\rho\in F$，显式假设 `hρ` 给出 $L$ 中的等式 $\iota(\rho)=r_1r_2$。取 $F$ 的乘法约化有限位 $v$，即曲线的 `badAll` 中的一位，并假设其剩余特征为奇数。对应的上游定理给出

$$
|\rho|_v^4|j|_v^{\ell-1}\le 1.
$$

选取 $L$ 中位于 $v$ 上方的 $w$。私有引理 `isBadPlace_of_liesOver` 利用提供者给出的曲线算术数据，在 $v$ 下方找到一个属于 `VBadOdd` 的位，再复合两层位的延拓关系。这两步对应上游的 `exists_mem_VBadOdd` 和 `FinitePlace.liesOver_trans`。 [适配后的引理](../../../../Solutions/Source_TripodCyclicVeluTate.lean#L38) · [上游位的存在性](../../../../../refer/iut/Iut/Tripod/CyclicTorsion.lean#L58)

对 $y\in F$，`apply_algebraMap_eq_pow` 给出 $|\iota(y)|_w=|y|_v^d$，其中 $d=\operatorname{relLocalDeg}(w,v)=e(w/v)f(w/v)>0$，$e(w/v)$ 为分歧指数，$f(w/v)$ 为剩余域次数。在 $w$ 处应用 `tate_bound`。用 `hρ` 和 $|\cdot|_w$ 的乘法性将 $|r_1|_w|r_2|_w$ 改写为 $|\iota(\rho)|_w$，再将 $\rho$ 和 $j$ 的绝对值换到 $v$，得到

$$
\bigl(|\rho|_v^4|j|_v^{\ell-1}\bigr)^d\le 1.
$$

正整数次幂在非负实数上严格递增，故得所求不等式。 [适配后的定理](../../../../Solutions/Source_TripodCyclicVeluTate.lean#L132) · [上游定理](../../../../../refer/iut/Iut/Tripod/CyclicIsogeny.lean#L605) · [绝对值的换域公式](../../../../Solutions/Source_TripodRelativeAbsoluteValue.lean#L17)

## 日本語

### `tate_bound`

tripod の点 $x$ を固定し、$P$ が $x$ に与える楕円曲線を $E/F$ とする。奇素数 $\ell$ に対し、$P$ が与える mod $\ell$ 表現の核の固定体をねじれ点体 $L$ とする。位数 $\ell$ の加法部分群 $H\subset E(\overline F)$ を取る。定理は引き戻し $H_L\subset E(L)$ に `Fintype` インスタンスを仮定し、`card_HL` から $\#H_L=\ell$ を得る。$i=1,2$ に対し $r_i=\operatorname{veluRatio}(H_L,T_i,R_i)$ と置く。指定された点 $T_1,T_2$ は相異なる位数 $2$ の点であり、$2R_i=T_i$ を満たす。包含写像を $\iota\colon F\hookrightarrow L$ とし、$j=j(E)$ と置く。

$E$ のモジュライ体の `VBadOdd` に属する素点の上にある $L$ の有限素点 $w$ を取る。`VBadOdd` の素点は剰余標数が奇数で、その上に $F$ の素点が少なくとも一つあり、$E$ はそのような $F$ の素点すべてで乗法的還元を持つ。剰余標数が $\ell$ の場合も含む。`IsGraphLineOdd` は、`VBadOdd` の上にある各 $w$ で、$H_L$ が完備化 $L_w$ 上の Tate グラフ直線の引き戻しに等しいことを要求する。 [奇剰余標数の素点](../../../../../refer/iut/Iut/Tripod/CyclicTorsion.lean#L49) · [グラフ直線の条件](../../../../Solutions/Source_TripodCyclicBoundOdd.lean#L145)

定理は $w$ における次の評価を与える。

$$
(|r_1|_w|r_2|_w)^4|\iota(j)|_w^{\ell-1}\le 1.
$$

$w$ における Tate パラメータを $q_w$ とする。$L_w$ のノルムを $L$ に制限すると $|\cdot|_w$ になる。剰余標数が奇数なので $\|2\|=1$ であり、部分群の位数とグラフ直線の条件を用いて `ratio_mul_bound` を適用すると次を得る。

$$
(|r_1|_w|r_2|_w)^4\le \|q_w\|^{\ell-1}.
$$

移植版の証明は `variableChange_j` と `map_j` を使い、Tate 曲線の $j$ 不変量を $L_w$ における $j$ の像と同一視する。Tate の恒等式から $|\iota(j)|_w=\|q_w\|^{-1}$ を得る。不等式の両辺に $|\iota(j)|_w^{\ell-1}$ を掛け、$\|q_w\|>0$ を用いると、上流の同名定理の評価が得られる。 [移植版の定理](../../../../Solutions/Source_TripodCyclicVeluTate.lean#L72) · [上流の定理](../../../../../refer/iut/Iut/Tripod/CyclicIsogeny.lean#L425)

### `finite_tate`

$\ell$、$H$、グラフ直線に関する仮定を引き継ぐ。$\rho\in F$ を取り、$L$ 内の等式 $\iota(\rho)=r_1r_2$ を明示的な仮定 `hρ` とする。$v$ を曲線の `badAll` に属する $F$ の乗法的還元の有限素点とし、剰余標数が奇数であると仮定する。対応する上流の定理は次を与える。

$$
|\rho|_v^4|j|_v^{\ell-1}\le 1.
$$

$v$ の上にある $L$ の素点 $w$ を取る。補題 `isBadPlace_of_liesOver` は、$P$ が与える曲線の算術データから $v$ の下にある `VBadOdd` の素点を取り、二つの素点の延長関係を合成する。この二つの手順は上流の `exists_mem_VBadOdd` と `FinitePlace.liesOver_trans` に対応する。 [移植版の補題](../../../../Solutions/Source_TripodCyclicVeluTate.lean#L38) · [上流の存在補題](../../../../../refer/iut/Iut/Tripod/CyclicTorsion.lean#L58)

$y\in F$ に対し、`apply_algebraMap_eq_pow` から $|\iota(y)|_w=|y|_v^d$ を得る。ここで $d=\operatorname{relLocalDeg}(w,v)=e(w/v)f(w/v)>0$ であり、$e(w/v)$ は分岐指数、$f(w/v)$ は剰余体次数である。$w$ で `tate_bound` を適用する。`hρ` と $|\cdot|_w$ の乗法性を用いて、$|r_1|_w|r_2|_w$ を $|\iota(\rho)|_w$ に書き換える。$\rho$ と $j$ の絶対値を $v$ での値に書き換えると次を得る。

$$
\bigl(|\rho|_v^4|j|_v^{\ell-1}\bigr)^d\le 1.
$$

正の整数乗は非負実数上で狭義単調増加であるため、求める不等式が従う。 [移植版の定理](../../../../Solutions/Source_TripodCyclicVeluTate.lean#L132) · [上流の定理](../../../../../refer/iut/Iut/Tripod/CyclicIsogeny.lean#L605) · [絶対値の移行公式](../../../../Solutions/Source_TripodRelativeAbsoluteValue.lean#L17)
