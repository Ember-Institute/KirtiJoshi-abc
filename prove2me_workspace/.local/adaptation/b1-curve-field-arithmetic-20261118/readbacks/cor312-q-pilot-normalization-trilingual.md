# The q-pilot normalization for Corollary 3.12

Adapted source SHA-256 `734c28846b5b524861f3b7723c9d2f6634907f25bf34bdb786705fc05e4e882f`. Iut reference snapshot SHA-256 `959bf4c0b2c79c1dcabfc206646b65ae40147572ffece43cd321d764a2a91533`. The MCP-CI leaf check and Lean object build exited with code 0. Each reported two unused-tactic warnings for `ring`. Lean reports only `propext`, `Classical.choice`, and `Quot.sound` for the five declarations in the joint axiom review. [Leaf check ci-022907-fcc7953c](../receipts/round-ci-022907-fcc7953c-result.json) · [Leaf build ci-022910-5ab80b74](../receipts/round-ci-022910-5ab80b74-result.json) · [Joint axiom review ci-022926-2a7dcca5](../receipts/round-ci-022926-2a7dcca5-result.json)

## English

Let $p$ be a rational prime and let $K$ be the field `D.Kt`. For $w$ in `LT.Fiber (.finite p)`, let $v_w=\mathrm{LT.fiberPlace}(w)$ and $r_w=\mathrm{TL.qroot}(v_w)$. Write $\log Q_p$ for `logQAt p` on the concrete q-pilot data. The adapted lemma proves

$$
\frac{\log Q_p}{2\ell}=\sum_{w\in\mathrm{LT.Fiber}(\mathrm{finite}\ p)}
\frac{-\log\lVert r_w\rVert}{[K:\mathbb Q]}.
$$

Here $r_w$ is the chosen Tate root at $v_w$ and $\lVert\cdot\rVert$ is the norm on the adic completion. [Adapted lemma](../../../../Solutions/Source_ReferenceIutCor312QPilotNormalization.lean#L18)

The proof starts from `logQAt_eq` and cancels $2\ell$. Let $n_w=[K_{v_w}:\mathbb Q_p]$ be the local degree. The residue characteristic is $p$ at each $v_w$, so the place weight is $n_w/[K:\mathbb Q]$ and $\operatorname{ord}_p(r_w)=-\log\lVert r_w\rVert/(n_w\log p)$. Each summand is the product of $\log p$, the place weight, and the normalized valuation. The factors $n_w$ and $\log p$ cancel, leaving the absolute degree $[K:\mathbb Q]$ in the denominator. Lean uses the positivity of the degrees and $p>1$ to clear the denominators. [Expanded q-pilot sum](../../../../Solutions/Source_ReferenceIutConcreteLocalEstimate.lean#L221) · [Iut reference](../../../../../refer/iut/Iut/Concrete/LocalEstimate.lean#L211) · [Place weight](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L78) · [Normalized valuation](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L87)

The proof of `vol_finite` uses the same quantity $\log Q_p/(2\ell)$. It obtains the weighted valuation sum directly from `logQAt_eq`. [Finite-place volume bound](../../../../Solutions/Source_ReferenceIutConcreteLocalEstimate.lean#L353)

## 中文

设 $p$ 为有理素数，$K$ 为数域 `D.Kt`。对 `LT.Fiber (.finite p)` 中的 $w$，令 $v_w=\mathrm{LT.fiberPlace}(w)$、$r_w=\mathrm{TL.qroot}(v_w)$。记具体 q-pilot 数据的 `logQAt p` 为 $\log Q_p$。适配引理证明

$$
\frac{\log Q_p}{2\ell}=\sum_{w\in\mathrm{LT.Fiber}(\mathrm{finite}\ p)}
\frac{-\log\lVert r_w\rVert}{[K:\mathbb Q]}.
$$

这里 $r_w$ 是在 $v_w$ 处选定的 Tate 根，$\lVert\cdot\rVert$ 是赋值完备化上的范数。 [适配引理](../../../../Solutions/Source_ReferenceIutCor312QPilotNormalization.lean#L18)

证明从 `logQAt_eq` 出发，约去 $2\ell$。记局部次数为 $n_w=[K_{v_w}:\mathbb Q_p]$。每个 $v_w$ 的剩余特征都是 $p$，故位点权重为 $n_w/[K:\mathbb Q]$，而 $\operatorname{ord}_p(r_w)=-\log\lVert r_w\rVert/(n_w\log p)$。每项取 $\log p$、位点权重与归一化赋值的乘积。约去 $n_w$ 和 $\log p$ 后，分母只剩绝对次数 $[K:\mathbb Q]$。Lean 用次数为正以及 $p>1$ 清除分母。 [展开的 q-pilot 和式](../../../../Solutions/Source_ReferenceIutConcreteLocalEstimate.lean#L221) · [Iut 参考源码](../../../../../refer/iut/Iut/Concrete/LocalEstimate.lean#L211) · [位点权重](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L78) · [归一化赋值](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L87)

`vol_finite` 的证明使用同一量 $\log Q_p/(2\ell)$，直接用 `logQAt_eq` 得到赋值的加权和。 [有限位点的体积界](../../../../Solutions/Source_ReferenceIutConcreteLocalEstimate.lean#L353)

## 日本語

$p$ を有理素数、$K$ を数体 `D.Kt` とする。`LT.Fiber (.finite p)` の各 $w$ に対し、$v_w=\mathrm{LT.fiberPlace}(w)$、$r_w=\mathrm{TL.qroot}(v_w)$ とおく。具体的な q-pilot データの `logQAt p` を $\log Q_p$ と書く。適応版の補題は

$$
\frac{\log Q_p}{2\ell}=\sum_{w\in\mathrm{LT.Fiber}(\mathrm{finite}\ p)}
\frac{-\log\lVert r_w\rVert}{[K:\mathbb Q]}
$$

を示す。ここで $r_w$ は $v_w$ で選んだ Tate 根であり、$\lVert\cdot\rVert$ は付値完備化上のノルムである。 [適応版の補題](../../../../Solutions/Source_ReferenceIutCor312QPilotNormalization.lean#L18)

証明は `logQAt_eq` から始め、$2\ell$ を約分する。局所次数を $n_w=[K_{v_w}:\mathbb Q_p]$ とおく。各 $v_w$ の剰余標数は $p$ なので、素点の重みは $n_w/[K:\mathbb Q]$、正規化付値は $\operatorname{ord}_p(r_w)=-\log\lVert r_w\rVert/(n_w\log p)$ である。各項は $\log p$、素点の重み、および正規化付値の積である。$n_w$ と $\log p$ が約分され、分母には絶対次数 $[K:\mathbb Q]$ が残る。Lean は次数の正値性と $p>1$ を使って分母を払う。 [q-pilot の和の展開](../../../../Solutions/Source_ReferenceIutConcreteLocalEstimate.lean#L221) · [Iut の参照元](../../../../../refer/iut/Iut/Concrete/LocalEstimate.lean#L211) · [素点の重み](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L78) · [正規化付値](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L87)

`vol_finite` の証明は同じ量 $\log Q_p/(2\ell)$ を用い、`logQAt_eq` から付値の重み付き和を直接得る。 [有限素点での体積の評価](../../../../Solutions/Source_ReferenceIutConcreteLocalEstimate.lean#L353)
