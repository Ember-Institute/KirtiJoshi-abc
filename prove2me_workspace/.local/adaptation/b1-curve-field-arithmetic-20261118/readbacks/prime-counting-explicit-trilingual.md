# An eventual upper bound for the prime-counting function

Adapted source SHA-256 `48f32b5f83fa1e9a1ca1213aa9ff95e96276df049c44b4b35f16f692e0351b17`. Iut reference snapshot SHA-256 `3d36fd7292c87fae5c5f4a29cbabf654a4bddf7a2ca479120f291ccd1e762a20`. Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The MCP-CI leaf check and Lean object build exited with code 0 and no diagnostics. Lean reports only `propext`, `Classical.choice`, and `Quot.sound` for the five declarations in the joint axiom review. [Leaf check ci-022892-470be574](../receipts/round-ci-022892-470be574-result.json) · [Leaf build ci-022899-6e73563b](../receipts/round-ci-022899-6e73563b-result.json) · [Joint axiom review ci-022926-2a7dcca5](../receipts/round-ci-022926-2a7dcca5-result.json)

## English

The certificate `primeCountingBoundExplicit` supplies a real threshold $\eta>1$ such that, for every real $x\ge\eta$,

$$
\pi(\lfloor x\rfloor)\le \frac{3x}{2\log x}.
$$

Here $\pi(n)$ counts primes at most $n$. The certificate stores $\eta$, its strict lower bound, and the inequality in `PrimeCountingBound`. [Certificate structure](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Invariants.lean#L120) · [Adapted certificate](../../../../Solutions/Source_ReferenceIutPrimeCountingExplicit.lean#L38) · [Iut reference](../../../../../refer/iut/Iut/Implication/ChebyshevExplicit.lean#L259)

For $x\ge2$, Mathlib's Abel summation formula gives

$$
\pi(\lfloor x\rfloor)=\frac{\theta(x)}{\log x}+\int_2^x\frac{\theta(t)}{t(\log t)^2}\,dt.
$$

It bounds the first term using $\theta(x)\le(\log4)x$. The integral is $o(x/\log x)$, which gives the eventual bound with coefficient $\log4+\varepsilon$ for each $\varepsilon>0$. The adaptation uses $\varepsilon=3/2-\log4>0$. It obtains an eventual threshold $\eta_0$ from Mathlib and uses $\max(\eta_0,2)$ in the existence proof. The certificate chooses its threshold from that proof by classical choice. [Abel summation](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Chebyshev.lean#L637) · [Mathlib eventual inequality](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Chebyshev.lean#L802) · [Choice of coefficient and threshold](../../../../Solutions/Source_ReferenceIutPrimeCountingExplicit.lean#L21)

For fixed curve providers `P`, the theorem `canonicalCorollary22HighHeightEstimate_of_explicitPrimeEstimates` supplies both prime estimates to the canonical high-height form of Corollary 2.2. Its hypotheses are core finiteness (`hcore`), anabelian existence (`anab`), and the Corollary 3.12 variant on all concrete inputs (`h312`). [Canonical estimate](../../../../Solutions/Source_TripodCanonicalCorollary22PrimeEstimates.lean#L14) · [Certificate use](../../../../Solutions/Source_TripodCanonicalCorollary22PrimeEstimates.lean#L23)

## 中文

证书 `primeCountingBoundExplicit` 给出实数阈值 $\eta>1$，使每个实数 $x\ge\eta$ 都满足

$$
\pi(\lfloor x\rfloor)\le \frac{3x}{2\log x}.
$$

这里 $\pi(n)$ 计数不超过 $n$ 的素数。`PrimeCountingBound` 包含 $\eta$、它的严格下界以及上述不等式。 [证书结构](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Invariants.lean#L120) · [适配证书](../../../../Solutions/Source_ReferenceIutPrimeCountingExplicit.lean#L38) · [Iut 参考源码](../../../../../refer/iut/Iut/Implication/ChebyshevExplicit.lean#L259)

对 $x\ge2$，Mathlib 的 Abel 求和公式给出

$$
\pi(\lfloor x\rfloor)=\frac{\theta(x)}{\log x}+\int_2^x\frac{\theta(t)}{t(\log t)^2}\,dt.
$$

用 $\theta(x)\le(\log4)x$ 估计第一项。积分为 $o(x/\log x)$，故对每个 $\varepsilon>0$，充分大的 $x$ 有系数为 $\log4+\varepsilon$ 的上界。适配证明取 $\varepsilon=3/2-\log4>0$，从 Mathlib 得到阈值 $\eta_0$，并在存在性证明中用 $\max(\eta_0,2)$。证书通过经典选择从该证明取出阈值。 [Abel 求和](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Chebyshev.lean#L637) · [Mathlib 的最终上界](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Chebyshev.lean#L802) · [系数与阈值的选择](../../../../Solutions/Source_ReferenceIutPrimeCountingExplicit.lean#L21)

给定曲线提供者 `P`，定理 `canonicalCorollary22HighHeightEstimate_of_explicitPrimeEstimates` 将两份素数估计证书接入规范推论 2.2 的高高度估计。定理仍取三个假设，即 core 有限性 `hcore`、远阿贝尔存在性 `anab` 和对所有具体数据成立的推论 3.12 变体 `h312`。 [规范估计定理](../../../../Solutions/Source_TripodCanonicalCorollary22PrimeEstimates.lean#L14) · [证书的使用](../../../../Solutions/Source_TripodCanonicalCorollary22PrimeEstimates.lean#L23)

## 日本語

証明データ `primeCountingBoundExplicit` は、すべての実数 $x\ge\eta$ について

$$
\pi(\lfloor x\rfloor)\le \frac{3x}{2\log x}
$$

を満たす実数のしきい値 $\eta>1$ を与える。ここで $\pi(n)$ は $n$ 以下の素数の個数である。`PrimeCountingBound` は $\eta$、その狭義の下界、および上の不等式を持つ。 [証明データの構造](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Invariants.lean#L120) · [適応版の証明データ](../../../../Solutions/Source_ReferenceIutPrimeCountingExplicit.lean#L38) · [Iut の参照元](../../../../../refer/iut/Iut/Implication/ChebyshevExplicit.lean#L259)

$x\ge2$ に対し、Mathlib の Abel の部分和公式により

$$
\pi(\lfloor x\rfloor)=\frac{\theta(x)}{\log x}+\int_2^x\frac{\theta(t)}{t(\log t)^2}\,dt
$$

が成り立つ。第一項を $\theta(x)\le(\log4)x$ で評価する。積分は $o(x/\log x)$ なので、任意の $\varepsilon>0$ に対し、十分大きな $x$ で係数 $\log4+\varepsilon$ の上界を得る。適応版の証明は $\varepsilon=3/2-\log4>0$ を取る。Mathlib からしきい値 $\eta_0$ を取り出し、存在証明には $\max(\eta_0,2)$ を用いる。証明データはその存在証明から古典的選択でしきい値を得る。 [Abel の部分和公式](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Chebyshev.lean#L637) · [Mathlib の十分大きな引数での上界](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Chebyshev.lean#L802) · [係数としきい値の選択](../../../../Solutions/Source_ReferenceIutPrimeCountingExplicit.lean#L21)

曲線の供給データ `P` を固定すると、定理 `canonicalCorollary22HighHeightEstimate_of_explicitPrimeEstimates` は二つの素数評価を系 2.2 の標準形における高い高さでの評価に用いる。仮定は core に関する有限性 `hcore`、遠アーベルの存在性 `anab`、すべての具体的なデータに対する系 3.12 の変種 `h312` である。 [標準形の評価定理](../../../../Solutions/Source_TripodCanonicalCorollary22PrimeEstimates.lean#L14) · [証明データの使用](../../../../Solutions/Source_TripodCanonicalCorollary22PrimeEstimates.lean#L23)
