# Canonical Corollary 2.2 with the cyclic bound

Upstream Iut revision `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`. Adapted source SHA-256 `003af37bf85f1e34e965b201e5e1bde7d0f346793854e3b9f9d5c3ec62d74cfe`. The MCP-CI leaf check and build with Lean object output both exited with code 0 and reported no diagnostics. [Leaf check ci-022830-96a40723](../receipts/round-ci-022830-96a40723-result.json) · [Leaf build ci-022837-af11d9dc](../receipts/round-ci-022837-af11d9dc-result.json)

## English

The theorem `canonicalCorollary22HighHeightEstimate_of_cyclicBound` specializes the source assembly for Corollary 2.2. For each compactly bounded $K$, it sets `TK K = cyclicConst K (torsionConst K.c (legendre_torsion_x_le K.c))`. It packages `cyclicBoundOdd P K d` as `CurveFactsProp P K d (TK K)` for each $K,d$. The hypotheses are a curve provider $P$, `CoreFinitenessHyp` for each $K,d$, `AnabelianExistence`, `ChebyshevBound`, and `PrimeCountingBound`. The premise `h312` supplies `Corollary312Variant (concreteVariantData D LT TL QI)` for every tuple $D,LT,TL,QI$ of the stated types. [Specialization](../../../../Solutions/Source_TripodCanonicalCorollary22.lean#L58) · [Cyclic bound](tripod-cyclic-bound-odd-trilingual.md) · [Source assembly](tripod-canonical-corollary22-trilingual.md)

For $d>0$ and compactly bounded $K$, the conclusion gives a finite exception set $E$ and constants $H,C$ uniform in $x$. Take $x\in K.\mathrm{set}$ of degree at most $d$ outside $E$, with canonical auxiliary height $h\ge H$. Put $A=\mathrm{logDiff}(x)+\mathrm{logCond}(x)$, $\delta=552960d$, and $\epsilon_E(\delta,h)=(60\delta)^2\log(2\delta h)/\sqrt h$. Then

$$
\frac h6\le (1+\epsilon_E(\delta,h))A+C,\qquad
\epsilon_E(\delta,h)\le1,\qquad
0\le A.
$$

[Auxiliary height](../../../../Definitions/Def_TripodCanonicalHighHeightInputs.lean#L29) · [Conclusion](../../../../Definitions/Def_TripodCanonicalHighHeightInputs.lean#L54)

MCP-CI review `ci-022840-3258b7f9` printed only `propext`, `Classical.choice`, and `Quot.sound` for this specialization. [Review source](../ReviewCanonicalCorollary22Cyclic.lean#L7) · [Review receipt](../receipts/round-ci-022840-3258b7f9-result.json)

## 中文

定理 `canonicalCorollary22HighHeightEstimate_of_cyclicBound` 将推论 2.2 的组装定理特化到已证明的循环子群界。对每个紧致有界数据 $K$，取 `TK K = cyclicConst K (torsionConst K.c (legendre_torsion_x_le K.c))`，并对每组 $K,d$ 将 `cyclicBoundOdd P K d` 封装为 `CurveFactsProp P K d (TK K)`。定理假定曲线数据提供者 $P$、每组 $K,d$ 的 `CoreFinitenessHyp`、`AnabelianExistence`、`ChebyshevBound` 和 `PrimeCountingBound`。前提 `h312` 对每组指定类型的 $D,LT,TL,QI$ 给出 `Corollary312Variant (concreteVariantData D LT TL QI)`。 [特化定理](../../../../Solutions/Source_TripodCanonicalCorollary22.lean#L58) · [循环子群界](tripod-cyclic-bound-odd-trilingual.md) · [组装定理](tripod-canonical-corollary22-trilingual.md)

对 $d>0$ 及紧致有界数据 $K$，结论给出有限例外集 $E$，以及不依赖于 $x$ 的常数 $H,C$。取 $x\in K.\mathrm{set}$，其次数至多为 $d$，位于 $E$ 之外，且规范辅助高度 $h\ge H$。令 $A=\mathrm{logDiff}(x)+\mathrm{logCond}(x)$、$\delta=552960d$、$\epsilon_E(\delta,h)=(60\delta)^2\log(2\delta h)/\sqrt h$，则

$$
\frac h6\le (1+\epsilon_E(\delta,h))A+C,\qquad
\epsilon_E(\delta,h)\le1,\qquad
0\le A.
$$

[辅助高度](../../../../Definitions/Def_TripodCanonicalHighHeightInputs.lean#L29) · [结论](../../../../Definitions/Def_TripodCanonicalHighHeightInputs.lean#L54)

MCP-CI 审查 `ci-022840-3258b7f9` 对该特化定理仅列出公理 `propext`、`Classical.choice` 和 `Quot.sound`。 [审查源码](../ReviewCanonicalCorollary22Cyclic.lean#L7) · [审查回执](../receipts/round-ci-022840-3258b7f9-result.json)

## 日本語

定理 `canonicalCorollary22HighHeightEstimate_of_cyclicBound` は、系 2.2 を組み立てる定理を、証明済みの巡回部分群の評価に特殊化する。コンパクト有界集合のデータ $K$ ごとに `TK K = cyclicConst K (torsionConst K.c (legendre_torsion_x_le K.c))` と置き、各 $K,d$ について `cyclicBoundOdd P K d` から `CurveFactsProp P K d (TK K)` を作る。仮定は曲線データの供給元 $P$、各 $K,d$ に対する `CoreFinitenessHyp`、`AnabelianExistence`、`ChebyshevBound`、`PrimeCountingBound` である。仮定 `h312` は、所定の型を持つすべての $D,LT,TL,QI$ に対し `Corollary312Variant (concreteVariantData D LT TL QI)` を与える。 [特殊化の定理](../../../../Solutions/Source_TripodCanonicalCorollary22.lean#L58) · [巡回部分群の評価](tripod-cyclic-bound-odd-trilingual.md) · [組み立ての定理](tripod-canonical-corollary22-trilingual.md)

$d>0$ とコンパクト有界集合のデータ $K$ に対し、結論は有限な例外集合 $E$ と $x$ に依存しない定数 $H,C$ を与える。$K.\mathrm{set}$ に属し、次数が $d$ 以下で、$E$ の外にある点 $x$ を取る。標準の補助高さを $h$ とし、$h\ge H$ とする。$A=\mathrm{logDiff}(x)+\mathrm{logCond}(x)$、$\delta=552960d$、$\epsilon_E(\delta,h)=(60\delta)^2\log(2\delta h)/\sqrt h$ と置くと

$$
\frac h6\le (1+\epsilon_E(\delta,h))A+C,\qquad
\epsilon_E(\delta,h)\le1,\qquad
0\le A
$$

が成り立つ。 [補助高さ](../../../../Definitions/Def_TripodCanonicalHighHeightInputs.lean#L29) · [結論](../../../../Definitions/Def_TripodCanonicalHighHeightInputs.lean#L54)

MCP-CI レビュー `ci-022840-3258b7f9` は、この特殊化の定理の公理として `propext`、`Classical.choice`、`Quot.sound` だけを出力した。 [レビューのソース](../ReviewCanonicalCorollary22Cyclic.lean#L7) · [レビュー結果](../receipts/round-ci-022840-3258b7f9-result.json)
