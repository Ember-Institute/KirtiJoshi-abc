# Legendre and Tate height comparison

The archived trilingual readbacks give the correct two inequalities and place the real constants before the point quantifier. Their archived checksums match. This supplement records the height on the supplied curve and its current consumers. [Comparison theorem](../../b1-tate-existence-v227-20261118/legendre-height-readbacks/legendre-height-readback.md) · [Bounded discrepancy](../../b1-tate-existence-v227-20261118/legendre-height-readbacks/legendre-height-hyp-readback.md) · [Canonical comparison](../../b1-tate-existence-v227-20261118/legendre-height-readbacks/canonical-legendre-height-comparison-of-provider-readback.md)

## English

Fix a supplied provider $P$. Its point $x$ is an algebraic number other than $0$ and $1$. Write $E_x/F_x$ for `P.curve x`. The arithmetic and Tate inputs `P.arith x` and `P.tate x` both refer to that curve. They give `P.localData x` and its height $P.h(x)$. Write $w$ for a finite place of multiplicative reduction of $E_x$. The summand uses the valuation exponent $m_w$ of its Tate parameter, its residue degree $f_w$, and its residue characteristic $p_w$. The height sums over every such $w$, including the places over $2$.

The two bounds in the archived readback hold simultaneously for all $x\in K.\mathrm{set}$. Here $V=K.V$ is a finite set of rational primes that contains $2$. Write $\lambda=\mathrm{gen}(x)$ for the image of $x$ in the point field $\mathbb Q(\lambda)$. Membership in $K.\mathrm{set}$ bounds $\left|\log\lvert\lambda\rvert_v\right|$ and $\left|\log\lvert\lambda-1\rvert_v\right|$ by $c=K.c$. These bounds apply at the finite places over $V$ and at every infinite place of $\mathbb Q(\lambda)$.

The source constructor `curveInputs` puts the comparison in `htCan_equiv` and uses it for `northcott`. The local constructor `curveInputsOfSL2Image` does the same with the provider's height, curve, arithmetic, and Tate inputs. For points of degree at most $d$, the Northcott argument uses $\mathrm{htCan}(x)\le P.h(x)/6+C_2$ to turn a bound on $P.h$ into a bound on $\mathrm{htCan}$. The source P7 and canonical Corollary 2.2 proofs pass `legendreHeight P K` to this constructor through `curveInputs_from_source`. The Statement II composition uses the absolute-value comparison from `canonicalLegendreHeightComparison_of_provider P` in its estimate for points of large height.

## 简体中文

固定一个给定的供应数据 $P$。点 $x$ 是异于 $0$ 和 $1$ 的代数数。将 `P.curve x` 记为 $E_x/F_x$。`P.arith x` 与 `P.tate x` 分别给出同一曲线的算术数据和 Tate 输入，并组成 `P.localData x`。其高度为 $P.h(x)$。令 $w$ 遍历 $E_x$ 有乘法约化的有限处，记该处的 Tate 参数的赋值指数为 $m_w$，剩余次数为 $f_w$，剩余特征为 $p_w$。求和包含所有这些有限处，也包含位于 $2$ 上方的乘法约化处。

原稿的两条界对 $K.\mathrm{set}$ 中的所有 $x$ 同时成立。这里 $V=K.V$ 为包含 $2$ 的有限有理素数集。以 $\lambda=\mathrm{gen}(x)$ 表示 $x$ 在点域 $\mathbb Q(\lambda)$ 中的代表元。$x\in K.\mathrm{set}$ 要求 $\left|\log\lvert\lambda\rvert_v\right|$ 与 $\left|\log\lvert\lambda-1\rvert_v\right|$ 在位于 $V$ 上方的各有限处及所有无穷处均至多为 $c=K.c$。

原构造器 `curveInputs` 将比较放入 `htCan_equiv`，并用它构造 `northcott`。本地 `curveInputsOfSL2Image` 同样取该供应数据的高度、曲线、算术数据和 Tate 输入。对次数至多为 $d$ 的点，Northcott 有限性用 $\mathrm{htCan}(x)\le P.h(x)/6+C_2$ 将 $P.h$ 的上界转换为 $\mathrm{htCan}$ 的上界。源 P7 与典范推论 2.2 的证明都通过 `curveInputs_from_source` 向构造器传入 `legendreHeight P K`。陈述 II 的拼接还将 `canonicalLegendreHeightComparison_of_provider P` 给出的绝对值比较用于高度较大的点的估计。

## 日本語

与えられた供給データ $P$ を固定する。点 $x$ は $0$ と $1$ を除く代数的数である。`P.curve x` を $E_x/F_x$ と書く。`P.arith x` と `P.tate x` は同じ曲線の算術データと Tate 入力を与える。これらから `P.localData x` を作り、その高さを $P.h(x)$ とする。$w$ を $E_x$ が乗法的還元を持つ有限素点とする。各項には Tate パラメータの付値指数 $m_w$、剰余次数 $f_w$、剰余標数 $p_w$ を用いる。和はこのようなすべての $w$ を含み、$2$ の上の乗法的還元の素点も含む。

保存された読解稿の二つの評価は、$K.\mathrm{set}$ のすべての $x$ について同時に成り立つ。$V=K.V$ は $2$ を含む有理素数の有限集合である。点の体 $\mathbb Q(\lambda)$ における $x$ の代表元を $\lambda=\mathrm{gen}(x)$ と書く。$x\in K.\mathrm{set}$ ならば、$V$ の上の各有限素点とすべての無限素点で $\left|\log\lvert\lambda\rvert_v\right|$ と $\left|\log\lvert\lambda-1\rvert_v\right|$ は $c=K.c$ 以下である。

参照実装の構成子 `curveInputs` は比較を `htCan_equiv` に入れ、`northcott` にも用いる。移植版の `curveInputsOfSL2Image` も同じ供給データの高さ、曲線、算術データおよび Tate 入力を使う。次数が $d$ 以下の点に対する Northcott の有限性では、$\mathrm{htCan}(x)\le P.h(x)/6+C_2$ により $P.h$ の上界を $\mathrm{htCan}$ の上界に変換する。参照 P7 と標準的な系 2.2 の証明は、`curveInputs_from_source` を介して `legendreHeight P K` をこの構成子に渡す。命題 II の組み立てでは、`canonicalLegendreHeightComparison_of_provider P` による絶対値評価を高さの大きい点の評価に用いる。

## Formulas and references

$$
\begin{aligned}
P.h(x)
  &=\frac{1}{[F_x:\mathbb Q]}\sum_{w\text{ multiplicative}}m_w f_w\log p_w
    =\frac{h_{\mathrm{fin}}(j(\lambda))}{[\mathbb Q(\lambda):\mathbb Q]},\\
\mathrm{htCan}(x)&=\frac{h(\lambda)}{[\mathbb Q(\lambda):\mathbb Q]},\\
P.h(x)/6&\le\mathrm{htCan}(x)+\underbrace{\log(2)/3}_{C_1},\\
\mathrm{htCan}(x)&\le P.h(x)/6+\underbrace{c|V|+c+\log(2)/3}_{C_2}.
\end{aligned}
$$

The local sum uses the degree of the provider's curve field $F_x$. The normalized finite and total logarithmic heights use the degree of the point field $\mathbb Q(\lambda)$. The first inequality has a universal constant. The second uses the data of $K$. [Provider local height](../../../../../refer/iut/Iut/Tripod/CurveFacts.lean#L384) · [Local height sum](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection.lean#L111) · [Height normalization](../../../../../refer/iut/Iut/Tripod/Height.lean#L603) · [Explicit bounds](../../../../../refer/iut/Iut/Tripod/Height.lean#L791) · [Compactly bounded set](../../../../Definitions/Def_AbcTripod.lean#L169)

- The upstream consumer builds `htCan_equiv` and `northcott` in `curveInputs`. The local constructor and Northcott lemma follow that wiring. [Upstream fields](../../../../../refer/iut/Iut/Tripod/CurveFacts.lean#L508) · [Local constructor](../../../../Solutions/Source_TripodCurveInputs.lean#L26) · [Northcott argument](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_NorthcottComparison.lean#L33)
- The project passes the original comparison to `curveInputs_from_source` for P7 and Corollary 2.2. The canonical comparison takes $\max(C_1,C_2)$, and the Statement II composition uses the resulting absolute-value bound. [P7](../../../../Solutions/Source_TripodP7.lean#L47) · [Corollary 2.2](../../../../Solutions/Source_TripodCanonicalCorollary22.lean#L25) · [Canonical comparison](../../../../Solutions/Source_TripodProviderLegendreComparison.lean#L20) · [Statement II](../../../../Solutions/Source_TripodStatementIIOnSourceP7.lean#L17)
- The historical source context calls the canonical consumer a draft, and the height ledger lists `curveInputs` as open. The current sources contain the conditional constructor and its callers. They take $P$ as a supplied argument. [Historical context](../../b1-tate-existence-v227-20261118/legendre-height-readbacks/source-context.md#L3) · [Height ledger](../../b1-tate-existence-v227-20261118/TATE_INPUTS_SOURCE_LEDGER.md#L137) · [Current constructor](../../../../Solutions/Source_TripodCurveInputsFromSource.lean#L40)
