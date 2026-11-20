# Canonical Corollary 2.2 from CanLift

## English

In `canonicalCorollary22HighHeightEstimate_of_canLift27`, write `AG` for `modelAG (genuineEtalePi1Theory canLift27)` and let `TG : TemperedGeometry AG`. The theorem takes `P : CurveProviders` for the Legendre curves and `anab : AnabelianExistence AG TG`. For admissible prime data with the global theta and universal core conditions, `anab` supplies an orbicurve with local theta data. [Theorem](../../../../Solutions/Source_TripodCanonicalCorollary22FromCanLift.lean#L17) · [Anabelian existence](../../../../Solutions/Source_ReferenceIutInitialThetaData.lean#L26)

For each compactly bounded `K` and natural number `d`, `cyclicBoundOdd P K d` supplies the cyclic subgroup bound with `T_K = cyclicConst K (torsionConst K.c (legendre_torsion_x_le K.c))`. CanLift Proposition 2.7 supplies core finiteness through `coreFiniteness_of_modelAG`. The theorem builds `CI` with `curveInputs_from_source` using these two results, `northcottHyp`, `legendreHeight P K`, and `twoAdicBound P K`. [Cyclic bound](../../../../Theorems/Thm_AbcAdaptation_Tripod_cyclicBoundOdd.lean#L19) · [CanLift Proposition 2.7](../../../../Solutions/Source_ReferenceIutCanLiftProp27.lean#L12) · [Core finiteness](../../../../Solutions/Source_TripodCoreModel.lean#L71) · [Curve inputs](../../../../Solutions/Source_TripodCurveInputsFromSource.lean#L40)

For every such `K` and `d`, the premise `h312` assumes `Corollary312Variant X` for each `X : Corollary312VariantData.{0, 0} AG TG` satisfying `IsSourceP7Variant CI anab X`. The predicate identifies `X` with the concrete theta bundle from a point and an admissible prime in (P7). On this bundle the variant is `X.qPilot.lhs ≤ X.rhsData.rhs`. [Premise](../../../../Solutions/Source_TripodCanonicalCorollary22FromCanLift.lean#L21) · [Source (P7) predicate](../../../../Solutions/Source_TripodP7.lean#L27) · [Variant inequality](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_Statement.lean#L113)

For the same `CI` and `anab`, `pointThetaDataExistence_from_canLift27` supplies a bundle that satisfies the predicate at each admissible point and prime. The witness has a Theorem 1.10 certificate and a local estimate. It meets the prime and degree requirements and the comparisons for the $q$-pilot, logarithmic different, and logarithmic conductor. The proof passes this existence result, `h312`, and the two prime bounds to `canonicalCorollary22HighHeightEstimate_of_thetaDataExistence`. That theorem applies `I.c2` and rewrites the provider height as the canonical auxiliary height. [Pointwise existence](../../../../Solutions/Source_TripodP7FromCanLift.lean#L17) · [Witness](../../../../Solutions/Source_TripodP7.lean#L95) · [Application of Corollary 2.2](../../../../Solutions/Source_TripodCanonicalCorollary22.lean#L25) · [Height identity](../../../../Solutions/Source_TripodProviderAuxiliaryHeight.lean#L17)

Fix `d > 0` and `K`, and put `I := CI.toCorollary22Inputs`. Write $S_{K,d}$ for the points in `K.set` of degree at most $d$. The proof takes the finite exception set $E=I.\mathrm{excCore}\cap S_{K,d}$. Put $\delta=552960d$ and $B=I.B=\max(4\,K.c,0)$, the bound on the height contribution from places above $2$. The Chebyshev bound uses $\xi=10^{12}$. The prime-counting bound supplies a threshold $\eta>1$ by classical choice. The proof takes the following height threshold $H$ and additive constant $C$, both uniform in the point.

$$
\begin{aligned}
H&=\max\{\xi^2,\ 49+8\max(T_K,0)+B,\ (B+11+2\delta)^4+1,\
                    ((60\delta)^2(2\delta+4))^4+1\},\\
C&=40\eta+B/3.
\end{aligned}
$$

[Exception set and constants](../../../../Solutions/Source_TripodCanonicalCorollary22.lean#L36) · [Bound at 2](../../../../Solutions/Source_TripodCurveInputs.lean#L42) · [Threshold](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Corollary22.lean#L133) · [Chebyshev bound](../../../../Solutions/Source_ReferenceIutChebyshevExplicit.lean#L79) · [Prime-counting bound](../../../../Solutions/Source_ReferenceIutPrimeCountingExplicit.lean#L38)

For each $x\in S_{K,d}\setminus E$, set $h=\mathrm{auxiliaryHeight}(x)$. This is the finite height of the Legendre $j$-invariant in $\mathbb Q(x)$ divided by the degree of $x$. Let $A=\mathrm{logDiff}(x)+\mathrm{logCond}(x)$ and $\epsilon_E(\delta,h)=(60\delta)^2\log(2\delta h)/\sqrt h$. If $h\ge H$, the theorem gives all three conclusions for this point.

$$
\frac{h}{6}\le (1+\epsilon_E(\delta,h))A+C,\qquad
\epsilon_E(\delta,h)\le 1,\qquad
0\le A .
$$

[Height and error term](../../../../Definitions/Def_TripodCanonicalHighHeightInputs.lean#L29) · [Conclusion](../../../../Definitions/Def_TripodCanonicalHighHeightInputs.lean#L54) · [Reference tripod assembly](../../../../../refer/iut/Iut/Tripod/Main.lean#L129) · [Reference CanLift specialization](../../../../../refer/iut/Iut/Tripod/ClassicalAbcGenuineCanLift.lean#L40)

## 中文

在 `canonicalCorollary22HighHeightEstimate_of_canLift27` 中，令 `AG := modelAG (genuineEtalePi1Theory canLift27)`，取 `TG : TemperedGeometry AG`。定理的输入包括 Legendre 曲线提供器 `P : CurveProviders` 和远阿贝尔存在性 `anab : AnabelianExistence AG TG`。对满足全局 θ 条件和普遍核心条件的适用素数数据，`anab` 给出轨形曲线及其局部 θ 数据。 [定理](../../../../Solutions/Source_TripodCanonicalCorollary22FromCanLift.lean#L17) · [远阿贝尔存在性](../../../../Solutions/Source_ReferenceIutInitialThetaData.lean#L26)

对任意紧有界参数 `K` 与自然数 `d`，`cyclicBoundOdd P K d` 给出循环子群估计，所用常数为 `T_K = cyclicConst K (torsionConst K.c (legendre_torsion_x_le K.c))`。CanLift 命题 2.7 经由 `coreFiniteness_of_modelAG` 给出核心例外集有限性。定理用 `curveInputs_from_source` 将这两个结果与 `northcottHyp`、`legendreHeight P K`、`twoAdicBound P K` 组合成 `CI`。 [循环子群估计](../../../../Theorems/Thm_AbcAdaptation_Tripod_cyclicBoundOdd.lean#L19) · [CanLift 命题 2.7](../../../../Solutions/Source_ReferenceIutCanLiftProp27.lean#L12) · [核心例外集有限性](../../../../Solutions/Source_TripodCoreModel.lean#L71) · [曲线输入](../../../../Solutions/Source_TripodCurveInputsFromSource.lean#L40)

对每组 `K` 与 `d`，前提 `h312` 要求每个满足 `IsSourceP7Variant CI anab X` 的 `X : Corollary312VariantData.{0, 0} AG TG` 都满足 `Corollary312Variant X`。该谓词将 `X` 与 (P7) 由一个点及其适用素数构造的具体 θ 数据包等同。变体在此数据包上的不等式为 `X.qPilot.lhs ≤ X.rhsData.rhs`。 [前提](../../../../Solutions/Source_TripodCanonicalCorollary22FromCanLift.lean#L21) · [源端 (P7) 谓词](../../../../Solutions/Source_TripodP7.lean#L27) · [变体不等式](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_Statement.lean#L113)

对同一 `CI` 和 `anab`，`pointThetaDataExistence_from_canLift27` 为每个适用的点和素数提供满足该谓词的数据包。见证包含定理 1.10 的证书和局部估计，并满足素数、次数条件以及 $q$-pilot、对数相异和对数导子的比较式。证明把这一存在性结果、`h312` 和两项素数估计一并传给 `canonicalCorollary22HighHeightEstimate_of_thetaDataExistence`。后者应用 `I.c2`，再将提供器高度改写为规范辅助高度。 [逐点存在性](../../../../Solutions/Source_TripodP7FromCanLift.lean#L17) · [见证](../../../../Solutions/Source_TripodP7.lean#L95) · [推论 2.2 的应用](../../../../Solutions/Source_TripodCanonicalCorollary22.lean#L25) · [高度等式](../../../../Solutions/Source_TripodProviderAuxiliaryHeight.lean#L17)

固定 `d > 0` 和 `K`，令 `I := CI.toCorollary22Inputs`。记 $S_{K,d}$ 为 `K.set` 中次数至多为 $d$ 的点集。证明取有限例外集 $E=I.\mathrm{excCore}\cap S_{K,d}$。令 $\delta=552960d$，并记 $B=I.B=\max(4\,K.c,0)$ 为 $2$ 上方各处对高度贡献的上界。切比雪夫估计取 $\xi=10^{12}$，素数计数估计通过经典选择给出阈值 $\eta>1$。高度阈值 $H$ 与加性常数 $C$ 对所有这些点统一取值。

$$
\begin{aligned}
H&=\max\{\xi^2,\ 49+8\max(T_K,0)+B,\ (B+11+2\delta)^4+1,\
                    ((60\delta)^2(2\delta+4))^4+1\},\\
C&=40\eta+B/3.
\end{aligned}
$$

[例外集与常数](../../../../Solutions/Source_TripodCanonicalCorollary22.lean#L36) · [素数 2 的贡献上界](../../../../Solutions/Source_TripodCurveInputs.lean#L42) · [阈值](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Corollary22.lean#L133) · [切比雪夫估计](../../../../Solutions/Source_ReferenceIutChebyshevExplicit.lean#L79) · [素数计数估计](../../../../Solutions/Source_ReferenceIutPrimeCountingExplicit.lean#L38)

对每个 $x\in S_{K,d}\setminus E$，令 $h=\mathrm{auxiliaryHeight}(x)$。它是在 $\mathbb Q(x)$ 中计算的 Legendre $j$ 不变量的有限处高度除以 $x$ 的次数。令 $A=\mathrm{logDiff}(x)+\mathrm{logCond}(x)$，$\epsilon_E(\delta,h)=(60\delta)^2\log(2\delta h)/\sqrt h$。若 $h\ge H$，定理对该点同时给出三个结论。

$$
\frac{h}{6}\le (1+\epsilon_E(\delta,h))A+C,\qquad
\epsilon_E(\delta,h)\le 1,\qquad
0\le A .
$$

[高度与误差项](../../../../Definitions/Def_TripodCanonicalHighHeightInputs.lean#L29) · [结论](../../../../Definitions/Def_TripodCanonicalHighHeightInputs.lean#L54) · [参考 tripod 装配](../../../../../refer/iut/Iut/Tripod/Main.lean#L129) · [参考 CanLift 特化](../../../../../refer/iut/Iut/Tripod/ClassicalAbcGenuineCanLift.lean#L40)

## 日本語

`canonicalCorollary22HighHeightEstimate_of_canLift27` で、`AG := modelAG (genuineEtalePi1Theory canLift27)` とおき、`TG : TemperedGeometry AG` を取る。定理は Legendre 曲線の供給者 `P : CurveProviders` と遠アーベル的存在性 `anab : AnabelianExistence AG TG` を仮定する。大域的 θ 条件と普遍的コア条件を満たす許容素数データに対し、`anab` は軌道曲線とその上の局所 θ データを与える。 [定理](../../../../Solutions/Source_TripodCanonicalCorollary22FromCanLift.lean#L17) · [遠アーベル的存在性](../../../../Solutions/Source_ReferenceIutInitialThetaData.lean#L26)

各コンパクト有界なパラメータ `K` と自然数 `d` に対し、`cyclicBoundOdd P K d` は定数 `T_K = cyclicConst K (torsionConst K.c (legendre_torsion_x_le K.c))` を用いた巡回部分群の評価を与える。CanLift の命題 2.7 から、`coreFiniteness_of_modelAG` を通じてコア条件の例外集合の有限性を得る。`curveInputs_from_source` は、この二つの結果と `northcottHyp`、`legendreHeight P K`、`twoAdicBound P K` から `CI` を構成する。 [巡回部分群の評価](../../../../Theorems/Thm_AbcAdaptation_Tripod_cyclicBoundOdd.lean#L19) · [CanLift の命題 2.7](../../../../Solutions/Source_ReferenceIutCanLiftProp27.lean#L12) · [例外集合の有限性](../../../../Solutions/Source_TripodCoreModel.lean#L71) · [曲線の入力](../../../../Solutions/Source_TripodCurveInputsFromSource.lean#L40)

各 `K` と `d` について、仮定 `h312` は `IsSourceP7Variant CI anab X` を満たすすべての `X : Corollary312VariantData.{0, 0} AG TG` に対し、`Corollary312Variant X` を与える。この述語は `X` が、点と許容される素数から (P7) で構成する具体的な θ データに等しいことを表す。このデータについての変種の不等式は `X.qPilot.lhs ≤ X.rhsData.rhs` である。 [仮定](../../../../Solutions/Source_TripodCanonicalCorollary22FromCanLift.lean#L21) · [参照元の (P7) の述語](../../../../Solutions/Source_TripodP7.lean#L27) · [変種の不等式](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_Statement.lean#L113)

同じ `CI` と `anab` に対して、`pointThetaDataExistence_from_canLift27` は条件を満たす点と素数の各組に、この述語を満たすデータを与える。そのデータには定理 1.10 の証明書と局所評価が伴う。データは素数と次数の条件、および $q$-pilot、対数相異、対数導手の比較式を満たす。証明は、この存在性の結果、`h312`、および二つの素数の評価を `canonicalCorollary22HighHeightEstimate_of_thetaDataExistence` に渡す。この定理は `I.c2` を適用し、曲線の供給者が用いる高さを標準の補助高さで書き換える。 [点ごとの存在性](../../../../Solutions/Source_TripodP7FromCanLift.lean#L17) · [存在証明のデータ](../../../../Solutions/Source_TripodP7.lean#L95) · [系 2.2 の適用](../../../../Solutions/Source_TripodCanonicalCorollary22.lean#L25) · [高さの等式](../../../../Solutions/Source_TripodProviderAuxiliaryHeight.lean#L17)

`d > 0` と `K` を固定し、`I := CI.toCorollary22Inputs` とおく。`K.set` に属する次数が $d$ 以下の点の集合を $S_{K,d}$ とする。証明は有限例外集合 $E=I.\mathrm{excCore}\cap S_{K,d}$ を取る。$\delta=552960d$ とおき、$B=I.B=\max(4\,K.c,0)$ を $2$ の上にある素点からの高さへの寄与の上界とする。Chebyshev の評価では $\xi=10^{12}$ を用いる。素数計数の評価は古典的選択によってしきい値 $\eta>1$ を与える。高さのしきい値 $H$ と加法定数 $C$ は点によらず、次の値を取る。

$$
\begin{aligned}
H&=\max\{\xi^2,\ 49+8\max(T_K,0)+B,\ (B+11+2\delta)^4+1,\
                    ((60\delta)^2(2\delta+4))^4+1\},\\
C&=40\eta+B/3.
\end{aligned}
$$

[例外集合と定数](../../../../Solutions/Source_TripodCanonicalCorollary22.lean#L36) · [素数 2 の寄与の上界](../../../../Solutions/Source_TripodCurveInputs.lean#L42) · [しきい値](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Corollary22.lean#L133) · [Chebyshev の評価](../../../../Solutions/Source_ReferenceIutChebyshevExplicit.lean#L79) · [素数計数の評価](../../../../Solutions/Source_ReferenceIutPrimeCountingExplicit.lean#L38)

各 $x\in S_{K,d}\setminus E$ に対し、$h=\mathrm{auxiliaryHeight}(x)$ とおく。これは $\mathbb Q(x)$ で計算した Legendre の $j$ 不変量の有限素点の高さを $x$ の次数で割った値である。$A=\mathrm{logDiff}(x)+\mathrm{logCond}(x)$ および $\epsilon_E(\delta,h)=(60\delta)^2\log(2\delta h)/\sqrt h$ とおく。$h\ge H$ ならば、定理はこの点について次の三つの結論を同時に与える。

$$
\frac{h}{6}\le (1+\epsilon_E(\delta,h))A+C,\qquad
\epsilon_E(\delta,h)\le 1,\qquad
0\le A .
$$

[高さと誤差項](../../../../Definitions/Def_TripodCanonicalHighHeightInputs.lean#L29) · [結論](../../../../Definitions/Def_TripodCanonicalHighHeightInputs.lean#L54) · [参照元の tripod での組み立て](../../../../../refer/iut/Iut/Tripod/Main.lean#L129) · [参照元の CanLift による特殊化](../../../../../refer/iut/Iut/Tripod/ClassicalAbcGenuineCanLift.lean#L40)
