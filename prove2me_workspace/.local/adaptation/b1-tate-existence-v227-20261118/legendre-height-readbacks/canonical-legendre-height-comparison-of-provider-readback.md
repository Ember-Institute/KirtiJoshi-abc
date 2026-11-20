# English

Given an actual Legendre curve provider $P$, `canonicalLegendreHeightComparison_of_provider P` proves the fixed numerical comparison `CanonicalLegendreHeightComparison`. For every compactly bounded set $K$, there is a real constant $B$ such that

$$\left|A(x)/6-\mathrm{htCan}(x)\right|\leq B\qquad(x\in K),$$

where $A(x)=h_{\mathrm{fin}}(j(\lambda))/[\mathbb Q(\lambda):\mathbb Q]$ is the existing `auxiliaryHeight` and $\lambda=\mathrm{gen}(x)$.

The proof takes the two bounds from `legendreHeight P K` and rewrites $P.h=A$ using `providerHeight_eq_auxiliaryHeight`. It sets $B=\max(C_1,C_2)$ and combines the inequalities into the absolute-value bound. The proof contains no degree restriction and retains $P$ as an input. Mochizuki's IUT IV, Corollary 2.2(i), provides the mathematical height comparison; this consumer expresses that comparison using the project's fixed numerical height.

# 简体中文

给定一个实际的 Legendre 曲线供应数据 $P$，`canonicalLegendreHeightComparison_of_provider P` 证明固定的数值比较 `CanonicalLegendreHeightComparison`。对每个紧致有界子集 $K$，存在实常数 $B$，使

$$\left|A(x)/6-\mathrm{htCan}(x)\right|\leq B\qquad(x\in K),$$

其中 $A(x)=h_{\mathrm{fin}}(j(\lambda))/[\mathbb Q(\lambda):\mathbb Q]$ 是既有的 `auxiliaryHeight`，且 $\lambda=\mathrm{gen}(x)$。

证明取出 `legendreHeight P K` 的两侧界，再利用 `providerHeight_eq_auxiliaryHeight` 将 $P.h$ 改写为 $A$。取 $B=\max(C_1,C_2)$ 后，两条不等式合成上述绝对值界。证明没有次数限制，且仍以 $P$ 为输入。望月新一《集合论多宇宙间算术 Teichmüller 理论》第四篇推论 2.2(i) 提供数学上的高度比较；这条接合定理将其改写为项目已经固定的数值高度表达式。

# 日本語

実際の Legendre 曲線の供給データ $P$ が与えられると、`canonicalLegendreHeightComparison_of_provider P` は固定された数値比較 `CanonicalLegendreHeightComparison` を証明する。任意のコンパクト有界集合 $K$ に対し、実数定数 $B$ が存在して

$$\left|A(x)/6-\mathrm{htCan}(x)\right|\leq B\qquad(x\in K)$$

となる。ここで $A(x)=h_{\mathrm{fin}}(j(\lambda))/[\mathbb Q(\lambda):\mathbb Q]$ は既存の `auxiliaryHeight` であり、$\lambda=\mathrm{gen}(x)$ である。

証明は `legendreHeight P K` の二つの評価を取り出し、`providerHeight_eq_auxiliaryHeight` により $P.h$ を $A$ に書き換える。$B=\max(C_1,C_2)$ とおくと、二つの不等式から上の絶対値評価を得る。次数の制限はなく、$P$ は引き続き入力として必要である。望月新一の「宇宙際 Teichmüller 理論」第 IV 論文、系 2.2(i) が数学的な高さ比較を与える。この補助定理 は、その比較をプロジェクトで固定された数値高さの式で表す。

[Canonical consumer](../../../../Solutions/Source_TripodProviderLegendreComparison.lean#L20) · [Auxiliary height identity](../../../../Solutions/Source_TripodProviderAuxiliaryHeight.lean#L17) · [Source Legendre comparison](../../../../../refer/iut/Iut/Tripod/Height.lean#L791)
