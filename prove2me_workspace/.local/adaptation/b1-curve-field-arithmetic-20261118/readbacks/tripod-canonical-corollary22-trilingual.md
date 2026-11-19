# Corollary 2.2 for the canonical auxiliary height

## English

Fix `P : CurveProviders` and a function `TK : CompactlyBounded → ℝ`. For every `K,d`, supply the cyclic estimate `CurveFactsProp P K d (TK K)` and the finite core-exception locus `CoreFinitenessHyp P K d AG`. The other inputs are `AnabelianExistence AG TG`, `ChebyshevBound`, `PrimeCountingBound`, and `h312`. The last premise ranges over every `D : InitialThetaData AG TG`, `LT : LocalTheory.{0, 0} D.Kt`, `TL : ThetaLocalData D LT`, and `QI : QPilotInputs D`. It gives `Corollary312Variant (concreteVariantData D LT TL QI)`. The proof uses this premise on the very data that concrete (P7) supplies, through the equality in `IsConcrete`. The data also supply the Theorem 1.10 certificate and the local estimate used by `I.c2`. [Inputs and application](../../../../Solutions/Source_TripodCanonicalCorollary22.lean#L25) · [Concrete data and certificate](../../../../Solutions/Source_ReferenceIutConcreteExistence.lean#L55)

For $d>0$ and a compactly bounded $K$, let `I` denote the Corollary 2.2 inputs for these data. The chosen exception set is `I.excCore ∩ (tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d)`. Its finiteness follows from `I.excCore_finite`. Write $\delta=552960d$, $B=I.B$, $T_K=I.TK$, $\xi=\mathrm{cheb}.\xi$, and $\eta=\mathrm{pnt}.\eta$. The threshold $H=I.\mathrm{threshold}(\mathrm{cheb})$ is the maximum of

$$
\xi^2,\qquad 49+8\max(T_K,0)+B,\qquad
(B+11+2\delta)^4+1,\qquad ((60\delta)^2(2\delta+4))^4+1.
$$

The additive constant is $C=40\eta+B/3$. [Exception set and constants](../../../../Solutions/Source_TripodCanonicalCorollary22.lean#L40) · [Threshold](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Corollary22.lean#L133)

Take any $x\in K.\mathrm{set}$ of degree at most $d$ outside the chosen exception set, and set $h=\mathrm{auxiliaryHeight}(x)\ge H$. This is the finite height of the Legendre $j$-invariant in $\mathbb Q(x)$ divided by the degree of $x$. The provider height equals $h$. Put $A=\mathrm{logDiff}(x)+\mathrm{logCond}(x)$ and $\epsilon_E(\delta,h)=(60\delta)^2\log(2\delta h)/\sqrt h$. The single application of `I.c2` yields all three conclusions for this $x$ and $h$.

$$
\frac{h}{6}\le (1+\epsilon_E(\delta,h))A+C,\qquad
\epsilon_E(\delta,h)\le 1,\qquad 0\le A .
$$

[Canonical height](../../../../Definitions/Def_TripodCanonicalHighHeightInputs.lean#L29) · [Height identity](../../../../Solutions/Source_TripodProviderAuxiliaryHeight.lean#L17) · [Reference c2](../../../../../refer/iut/Iut/Implication/Corollary22.lean#L386) · [Canonical conclusions](../../../../Definitions/Def_TripodCanonicalHighHeightInputs.lean#L54)

## 中文

固定 `P : CurveProviders` 和 `TK : CompactlyBounded → ℝ`。对每一组 `K,d`，给定循环子群估计 `CurveFactsProp P K d (TK K)` 及核心条件例外集有限性 `CoreFinitenessHyp P K d AG`。其余输入为 `AnabelianExistence AG TG`、`ChebyshevBound`、`PrimeCountingBound` 和 `h312`。最后一项全称量化 `D : InitialThetaData AG TG`、`LT : LocalTheory.{0, 0} D.Kt`、`TL : ThetaLocalData D LT` 和 `QI : QPilotInputs D`，给出 `Corollary312Variant (concreteVariantData D LT TL QI)`。证明通过 `IsConcrete` 中的等式，将此前提用于具体 (P7) 供应的同一数据包。该数据包也供应 `I.c2` 使用的定理 1.10 证书与局部估计。 [输入及其应用](../../../../Solutions/Source_TripodCanonicalCorollary22.lean#L25) · [具体数据与证书](../../../../Solutions/Source_ReferenceIutConcreteExistence.lean#L55)

对 $d>0$ 和紧有界参数 $K$，记 `I` 为相应的推论 2.2 输入。选择例外集 `I.excCore ∩ (tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d)`，其有限性由 `I.excCore_finite` 给出。令 $\delta=552960d$、$B=I.B$、$T_K=I.TK$、$\xi=\mathrm{cheb}.\xi$、$\eta=\mathrm{pnt}.\eta$。阈值 $H=I.\mathrm{threshold}(\mathrm{cheb})$ 为以下四项的最大值。

$$
\xi^2,\qquad 49+8\max(T_K,0)+B,\qquad
(B+11+2\delta)^4+1,\qquad ((60\delta)^2(2\delta+4))^4+1.
$$

加性常数为 $C=40\eta+B/3$。 [例外集与常数](../../../../Solutions/Source_TripodCanonicalCorollary22.lean#L40) · [阈值](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Corollary22.lean#L133)

取 $K.\mathrm{set}$ 中次数至多为 $d$ 且位于所选例外集之外的任意点 $x$，令 $h=\mathrm{auxiliaryHeight}(x)\ge H$。该高度是在 $\mathbb Q(x)$ 中计算的 Legendre $j$ 不变量有限位高度除以 $x$ 的次数，等于曲线供应者的高度。记 $A=\mathrm{logDiff}(x)+\mathrm{logCond}(x)$，并令 $\epsilon_E(\delta,h)=(60\delta)^2\log(2\delta h)/\sqrt h$。一次应用 `I.c2`，在同一个 $x$ 和 $h$ 上得到三个结论。

$$
\frac{h}{6}\le (1+\epsilon_E(\delta,h))A+C,\qquad
\epsilon_E(\delta,h)\le 1,\qquad 0\le A .
$$

[规范高度](../../../../Definitions/Def_TripodCanonicalHighHeightInputs.lean#L29) · [高度等式](../../../../Solutions/Source_TripodProviderAuxiliaryHeight.lean#L17) · [参考 c2](../../../../../refer/iut/Iut/Implication/Corollary22.lean#L386) · [规范结论](../../../../Definitions/Def_TripodCanonicalHighHeightInputs.lean#L54)

## 日本語

`P : CurveProviders` と `TK : CompactlyBounded → ℝ` を固定する。各 `K,d` について、巡回部分群の評価 `CurveFactsProp P K d (TK K)` と、核の条件の例外集合の有限性 `CoreFinitenessHyp P K d AG` を仮定する。さらに `AnabelianExistence AG TG`、`ChebyshevBound`、`PrimeCountingBound`、`h312` を取る。`h312` はすべての `D : InitialThetaData AG TG`、`LT : LocalTheory.{0, 0} D.Kt`、`TL : ThetaLocalData D LT`、`QI : QPilotInputs D` に対し `Corollary312Variant (concreteVariantData D LT TL QI)` を与える。証明は `IsConcrete` の等式を用いて、具体的な (P7) が与える同じデータにこの仮定を適用する。そのデータは `I.c2` が使う定理 1.10 の証明書と局所評価も与える。 [入力と適用](../../../../Solutions/Source_TripodCanonicalCorollary22.lean#L25) · [具体的なデータと証明書](../../../../Solutions/Source_ReferenceIutConcreteExistence.lean#L55)

$d>0$ とコンパクト有界なパラメータ $K$ に対し、系 2.2 の入力を `I` とする。例外集合は `I.excCore ∩ (tripodTheory.cbsSet K ∩ tripodTheory.ptLE tripodTheory.tripod d)` であり、その有限性は `I.excCore_finite` による。$\delta=552960d$、$B=I.B$、$T_K=I.TK$、$\xi=\mathrm{cheb}.\xi$、$\eta=\mathrm{pnt}.\eta$ と置く。しきい値 $H=I.\mathrm{threshold}(\mathrm{cheb})$ は次の四項の最大値である。

$$
\xi^2,\qquad 49+8\max(T_K,0)+B,\qquad
(B+11+2\delta)^4+1,\qquad ((60\delta)^2(2\delta+4))^4+1.
$$

加法定数は $C=40\eta+B/3$ である。 [例外集合と定数](../../../../Solutions/Source_TripodCanonicalCorollary22.lean#L40) · [しきい値](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Corollary22.lean#L133)

$K.\mathrm{set}$ に属し、次数が $d$ 以下で、選んだ例外集合の外にある任意の点 $x$ を取る。$h=\mathrm{auxiliaryHeight}(x)\ge H$ とする。この高さは $\mathbb Q(x)$ で計算した Legendre の $j$ 不変量の有限素点の高さを $x$ の次数で割った値である。曲線の提供側が用いる高さも $h$ に等しい。$A=\mathrm{logDiff}(x)+\mathrm{logCond}(x)$、$\epsilon_E(\delta,h)=(60\delta)^2\log(2\delta h)/\sqrt h$ と置く。`I.c2` を一度適用し、同じ $x$ と $h$ について三つの結論を得る。

$$
\frac{h}{6}\le (1+\epsilon_E(\delta,h))A+C,\qquad
\epsilon_E(\delta,h)\le 1,\qquad 0\le A .
$$

[標準の高さ](../../../../Definitions/Def_TripodCanonicalHighHeightInputs.lean#L29) · [高さの等式](../../../../Solutions/Source_TripodProviderAuxiliaryHeight.lean#L17) · [参照元の c2](../../../../../refer/iut/Iut/Implication/Corollary22.lean#L386) · [標準の結論](../../../../Definitions/Def_TripodCanonicalHighHeightInputs.lean#L54)
