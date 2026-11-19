# Chebyshev bounds with threshold $10^{12}$

Adapted source SHA-256 `90fa992ba934b5669a25ca48fd58d26dea0fe74e5d545256ed69711be8920a21`. Iut reference snapshot SHA-256 `3d36fd7292c87fae5c5f4a29cbabf654a4bddf7a2ca479120f291ccd1e762a20`. Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The MCP-CI leaf check and Lean object build exited with code 0 and no diagnostics. Lean reports only `propext`, `Classical.choice`, and `Quot.sound` for the five declarations in the joint axiom review. [Leaf check ci-022906-bd4213ca](../receipts/round-ci-022906-bd4213ca-result.json) · [Leaf build ci-022909-af7dd6a8](../receipts/round-ci-022909-af7dd6a8-result.json) · [Joint axiom review ci-022926-2a7dcca5](../receipts/round-ci-022926-2a7dcca5-result.json)

## English

Write $\theta(x)=\sum_{p\le x,\ p\ \mathrm{prime}}\log p$. The certificate `chebyshevBoundExplicit` uses the threshold $\xi=10^{12}\ge5$ and gives, for every real $x\ge\xi$,

$$
\frac23x\le\theta(x)\le2x.
$$

For the upper bound, Mathlib gives $\theta(x)\le(\log4)x$ for $x\ge0$. Since $\log4\le2$, this gives the required upper factor. [Certificate structure](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection.lean#L45) · [Adapted certificate](../../../../Solutions/Source_ReferenceIutChebyshevExplicit.lean#L79) · [Iut reference](../../../../../refer/iut/Iut/Implication/ChebyshevExplicit.lean#L205) · [Mathlib upper bound](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Chebyshev.lean#L195)

For the lower bound, set $t=\sqrt{\sqrt{x}}$, so $t\ge1000$ and $x=t^4$. The estimate $\log t\le t-1$ gives $\log x\le4t$. Since $x\ge2$, the inequality $x+2\le x^2$ gives $\log(x+2)\le8t$. These bounds control the errors in Mathlib's `Chebyshev.theta_ge'` by

$$
\log2+\log(x+2)+2\sqrt{x}\log x
\le16t^3\le0.0264x\le(\log2-2/3)x.
$$

Mathlib's leading term is $x\log2$ after writing $(x-1)\log2=x\log2-\log2$. Subtract the error estimate to obtain the lower factor $2/3$. [Adapted lower bound](../../../../Solutions/Source_ReferenceIutChebyshevExplicit.lean#L19) · [Error comparison](../../../../Solutions/Source_ReferenceIutChebyshevExplicit.lean#L65) · [Iut lower bound](../../../../../refer/iut/Iut/Implication/ChebyshevExplicit.lean#L94) · [Mathlib lower bound](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Chebyshev.lean#L504)

For fixed curve providers `P`, the theorem `canonicalCorollary22HighHeightEstimate_of_explicitPrimeEstimates` supplies both prime estimates to the canonical high-height form of Corollary 2.2. Its hypotheses are core finiteness (`hcore`), anabelian existence (`anab`), and the Corollary 3.12 variant on all concrete inputs (`h312`). [Canonical estimate](../../../../Solutions/Source_TripodCanonicalCorollary22PrimeEstimates.lean#L14) · [Certificate use](../../../../Solutions/Source_TripodCanonicalCorollary22PrimeEstimates.lean#L23)

## 中文

记 $\theta(x)=\sum_{p\le x,\ p\ \mathrm{prime}}\log p$。证书 `chebyshevBoundExplicit` 取阈值 $\xi=10^{12}\ge5$，使每个实数 $x\ge\xi$ 都满足

$$
\frac23x\le\theta(x)\le2x.
$$

对上界，Mathlib 在 $x\ge0$ 时给出 $\theta(x)\le(\log4)x$。由 $\log4\le2$ 得到所需的上界系数。 [证书结构](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection.lean#L45) · [适配证书](../../../../Solutions/Source_ReferenceIutChebyshevExplicit.lean#L79) · [Iut 参考源码](../../../../../refer/iut/Iut/Implication/ChebyshevExplicit.lean#L205) · [Mathlib 上界](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Chebyshev.lean#L195)

对下界，置 $t=\sqrt{\sqrt{x}}$，则 $t\ge1000$ 且 $x=t^4$。由 $\log t\le t-1$ 得 $\log x\le4t$。由于 $x\ge2$，有 $x+2\le x^2$，从而 $\log(x+2)\le8t$。这些界将 Mathlib 的 `Chebyshev.theta_ge'` 中的误差项控制为

$$
\log2+\log(x+2)+2\sqrt{x}\log x
\le16t^3\le0.0264x\le(\log2-2/3)x.
$$

把 $(x-1)\log2$ 写成 $x\log2-\log2$ 后，主项为 $x\log2$。扣除误差界即得到下界系数 $2/3$。 [适配下界](../../../../Solutions/Source_ReferenceIutChebyshevExplicit.lean#L19) · [误差比较](../../../../Solutions/Source_ReferenceIutChebyshevExplicit.lean#L65) · [Iut 下界](../../../../../refer/iut/Iut/Implication/ChebyshevExplicit.lean#L94) · [Mathlib 下界](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Chebyshev.lean#L504)

给定曲线提供者 `P`，定理 `canonicalCorollary22HighHeightEstimate_of_explicitPrimeEstimates` 将两份素数估计证书接入规范推论 2.2 的高高度估计。定理仍取三个假设，即 core 有限性 `hcore`、远阿贝尔存在性 `anab` 和对所有具体数据成立的推论 3.12 变体 `h312`。 [规范估计定理](../../../../Solutions/Source_TripodCanonicalCorollary22PrimeEstimates.lean#L14) · [证书的使用](../../../../Solutions/Source_TripodCanonicalCorollary22PrimeEstimates.lean#L23)

## 日本語

$\theta(x)=\sum_{p\le x,\ p\ \mathrm{prime}}\log p$ とする。証明データ `chebyshevBoundExplicit` はしきい値 $\xi=10^{12}\ge5$ を取り、すべての実数 $x\ge\xi$ に対して

$$
\frac23x\le\theta(x)\le2x
$$

を与える。上界について、Mathlib は $x\ge0$ で $\theta(x)\le(\log4)x$ を与える。$\log4\le2$ なので、所定の上界係数が従う。 [証明データの構造](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection.lean#L45) · [適応版の証明データ](../../../../Solutions/Source_ReferenceIutChebyshevExplicit.lean#L79) · [Iut の参照元](../../../../../refer/iut/Iut/Implication/ChebyshevExplicit.lean#L205) · [Mathlib の上界](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Chebyshev.lean#L195)

下界については $t=\sqrt{\sqrt{x}}$ と置くと、$t\ge1000$ かつ $x=t^4$ となる。$\log t\le t-1$ から $\log x\le4t$ を得る。$x\ge2$ では $x+2\le x^2$ なので $\log(x+2)\le8t$ が成り立つ。これらの評価により、Mathlib の `Chebyshev.theta_ge'` の誤差項について

$$
\log2+\log(x+2)+2\sqrt{x}\log x
\le16t^3\le0.0264x\le(\log2-2/3)x
$$

を得る。$(x-1)\log2=x\log2-\log2$ と書けば主項は $x\log2$ である。誤差の上界を引くと、下界係数 $2/3$ を得る。 [適応版の下界](../../../../Solutions/Source_ReferenceIutChebyshevExplicit.lean#L19) · [誤差の比較](../../../../Solutions/Source_ReferenceIutChebyshevExplicit.lean#L65) · [Iut の下界](../../../../../refer/iut/Iut/Implication/ChebyshevExplicit.lean#L94) · [Mathlib の下界](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Chebyshev.lean#L504)

曲線の供給データ `P` を固定すると、定理 `canonicalCorollary22HighHeightEstimate_of_explicitPrimeEstimates` は二つの素数評価を系 2.2 の標準形における高い高さでの評価に用いる。仮定は core に関する有限性 `hcore`、遠アーベルの存在性 `anab`、すべての具体的なデータに対する系 3.12 の変種 `h312` である。 [標準形の評価定理](../../../../Solutions/Source_TripodCanonicalCorollary22PrimeEstimates.lean#L14) · [証明データの使用](../../../../Solutions/Source_TripodCanonicalCorollary22PrimeEstimates.lean#L23)
