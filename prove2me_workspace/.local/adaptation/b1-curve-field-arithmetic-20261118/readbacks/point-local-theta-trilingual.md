# PointLocalTheta

## English

Fix initial theta data $D$ with base field $F$, torsion field $K_t$, and prime $\ell$. Let $B=$ `badPlacesOver D.F D.E D.VBad`, the finite places of $F$ above the selected bad places of the field of moduli. `TwoTorsionRational D` requires at least four points of $E(F)$ killed by $2$, including the identity. For the Legendre curve these are $\mathcal{O},(0,0),(1,0),(\lambda,0)$. The lemma `two_torsion_curveOf` supplies the required lower bound for the curve of each tripod point. [Rational 2-torsion premise](../../../../Solutions/Source_ReferenceIutThetaLocalRoots.lean#L35) · [Legendre 2-torsion](../../../../Solutions/Source_TripodTwoTorsion.lean#L23) · [Tripod curve](../../../../Solutions/Source_TripodTwoTorsion.lean#L81)

At each $v$ of $K_t$ above $B$, `exists_qroot` gives a $2\ell$-th root of the parameter of the selected local Tate curve in $(K_t)_v$. The proof uses the full $\ell$-torsion over the torsion field and the injection of the rational 2-torsion into the completion. The function `qrootOf` chooses a root $r_v$ there and sets $r_v=1$ elsewhere. For $v$ above $w\in B$, Tate parameter compatibility gives $r_v^{2\ell}=\iota_{w,v}(q_w)$ for the completion embedding $\iota_{w,v}\colon F_w\to (K_t)_v$. The order $\operatorname{ord}_p$ at $v$ is normalized by $\operatorname{ord}_p(p)=1$. Let $p$ be the residue characteristic, $e_w=e(w/p)$, and $\operatorname{qOrder}(w)$ the Tate order of $q_w$. The order formula is

$$
\operatorname{ord}_p(r_v)=\frac{\operatorname{qOrder}(w)}{2\ell e_w}.
$$

[Root existence](../../../../Solutions/Source_ReferenceIutThetaLocalRoots.lean#L100) · [Choice of root](../../../../Solutions/Source_ReferenceIutThetaLocalRoots.lean#L122) · [Tate parameter compatibility](../../../../Solutions/Source_ReferenceIutThetaLocalRoots.lean#L141) · [Order formula](../../../../Solutions/Source_ReferenceIutThetaLocalData.lean#L29)

For every rational prime $p$, `sum_weight_ordp_qrootOf` uses a finset whose underlying set is $B$. It identifies the fiber of the local theory over $p$ with the finite places $v\mid p$ of $K_t$. With $f_w$ the residue degree of $w$ over $p$, the grouping by places of $F$ gives

$$
\sum_{v\mid p}\frac{[(K_t)_v:\mathbb Q_p]}{[K_t:\mathbb Q]}\operatorname{ord}_p(r_v)
=\frac{1}{2\ell}\sum_{\substack{w\in B\\w\mid p}}\frac{f_w}{[F:\mathbb Q]}\operatorname{qOrder}(w).
$$

The q-pilot enumerates the bad places. The constructor `thetaLocalData` uses their residue characteristics and the roots just constructed. It records nonzero roots, nonnegative orders, the power formula, and the weighted identity. [Weighted identity](../../../../Solutions/Source_ReferenceIutThetaLocalData.lean#L48) · [Local theta data](../../../../Solutions/Source_ReferenceIutThetaLocalData.lean#L98) · [q-pilot bad characteristics](../../../../Solutions/Source_ReferenceIutThetaLocalBadChars.lean#L26)

The theorem `concreteThetaDataExistence_of_localArithmetic` takes `CI : CurveInputs`, `anab : AnabelianExistence AG TG`, and the rational 2-torsion bound for every curve indexed by a point in $T.\mathrm{cbsSet}(K)\cap T.\mathrm{ptLE}(T.\mathrm{tripod},d)$. The geometry input supplies an orbicurve and dependent geometric local data for that orbicurve over the canonical moduli-to-torsion inclusion. Write $I$ for `CI.toCorollary22Inputs`.  Fix $x\in T.\mathrm{cbsSet}(K)\cap T.\mathrm{ptLE}(T.\mathrm{tripod},d)$ outside `CI.excCore` and a prime $\ell\ge7$. P2 and P5 use the bad places of `I.localData x hx`. P2 requires that $\ell$ divide none of their Tate orders. P5 requires one of these places to have residue characteristic outside $\{2,\ell\}$. The theorem also takes `SL2Image x ℓ` as the prime-specific image condition. The exclusion `x ∉ CI.excCore` gives the core hypothesis for the selected curve. The selected `P := CI.pointThetaData ...` carries the initial data and q-pilot for that curve and prime. `P.localTheory` constructs `LocalTheory.{u,u} P.data.Kt`. The choice `TL := P.localThetaData (htwo x hx)` uses that theory and `P.qPilotInputs` on the same field. [Geometry input](../../../../Solutions/Source_ReferenceIutInitialThetaData.lean#L26) · [Selection at the point](../../../../Solutions/Source_ReferenceIutPointThetaData.lean#L39) · [Local theory and theorem hypotheses](../../../../Solutions/Source_ReferenceIutPointLocalTheta.lean#L29)

At each such point and prime, the remaining arithmetic input is `TowerArithmetic P.data P.localTheory (TL.withBadChars P.qPilotInputs)`. Its fields are R4 and Steps (ii) and (iii). The output `ConcreteThetaDataExistence` also assumes P3, namely $hv(w)<\sqrt{I.h(x)}$ at every bad place of residue characteristic $\ell$. The assembly uses $D=P.\mathrm{data}$ and the local data `TL.withBadChars P.qPilotInputs`. It gives $D.\ell=\ell$ and $D.\mathrm{dmod}\le d$. It equates the q-pilot’s `logQ` with `heightOther 2 ℓ`, the local height sum away from $2$ and $\ell$. The point’s `logDiff` equals the normalized different degree of the tripodal field. The conductor invariant lies between $D.\mathrm{logConductorDeg}$ and $D.\mathrm{logConductorDeg}+\log(2\ell)$. [Tower fields](../../../../Solutions/Source_ReferenceIutConcreteInvariants.lean#L173) · [P7 statement](../../../../Solutions/Source_ReferenceIutConcreteExistence.lean#L36) · [Pointwise assembly](../../../../Solutions/Source_ReferenceIutCurveConcreteExistence.lean#L54)

The review reports only `propext`, `Classical.choice`, and `Quot.sound` for the audited declarations. [PointLocalTheta review](../../../../.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-021884-70058d70-result.json) · [Reference P7 construction](../../../../../refer/iut/Iut/Tripod/Main.lean#L86)

## 中文

固定初始 Θ 数据 $D$，记底域为 $F$，挠点域为 $K_t$，素数为 $\ell$。令 $B=$ `badPlacesOver D.F D.E D.VBad`，即 $F$ 中位于模域所选坏位上方的有限位。`TwoTorsionRational D` 要求 $E(F)$ 中至少有四个满足 $[2]P=\mathcal{O}$ 的点，计入单位元。对于 Legendre 曲线，这四个点为 $\mathcal{O},(0,0),(1,0),(\lambda,0)$。`two_torsion_curveOf` 给出了每个三脚架点对应曲线所需的下界。 [有理 2 挠点假设](../../../../Solutions/Source_ReferenceIutThetaLocalRoots.lean#L35) · [Legendre 曲线的 2 挠点](../../../../Solutions/Source_TripodTwoTorsion.lean#L23) · [三脚架点的曲线](../../../../Solutions/Source_TripodTwoTorsion.lean#L81)

对于 $K_t$ 中位于 $B$ 上方的每个 $v$，`exists_qroot` 在完备化 $(K_t)_v$ 中给出所选局部 Tate 曲线参数的一个 $2\ell$ 次根。证明使用挠点域上的全体 $\ell$ 挠点，以及有理 2 挠点到完备化上挠点的单射。`qrootOf` 在这些位选取根 $r_v$，其余位取 $r_v=1$。若 $v$ 位于 $w\in B$ 上方，Tate 参数的相容性给出 $r_v^{2\ell}=\iota_{w,v}(q_w)$，其中 $\iota_{w,v}\colon F_w\to (K_t)_v$ 是完备化之间的嵌入。$v$ 处的阶数 $\operatorname{ord}_p$ 按 $\operatorname{ord}_p(p)=1$ 归一化。设 $p$ 为剩余特征，$e_w=e(w/p)$，$\operatorname{qOrder}(w)$ 为 $q_w$ 的 Tate 阶数，则

$$
\operatorname{ord}_p(r_v)=\frac{\operatorname{qOrder}(w)}{2\ell e_w}.
$$

[根的存在性](../../../../Solutions/Source_ReferenceIutThetaLocalRoots.lean#L100) · [根的选取](../../../../Solutions/Source_ReferenceIutThetaLocalRoots.lean#L122) · [Tate 参数相容性](../../../../Solutions/Source_ReferenceIutThetaLocalRoots.lean#L141) · [阶数公式](../../../../Solutions/Source_ReferenceIutThetaLocalData.lean#L29)

对每个有理素数 $p$，`sum_weight_ordp_qrootOf` 使用底层集合恰为 $B$ 的有限集。它将局部理论在 $p$ 上的纤维识别为 $K_t$ 的有限位 $v\mid p$。记 $f_w$ 为 $w$ 在 $p$ 上的剩余次数，按 $F$ 的位归并求和得到

$$
\sum_{v\mid p}\frac{[(K_t)_v:\mathbb Q_p]}{[K_t:\mathbb Q]}\operatorname{ord}_p(r_v)
=\frac{1}{2\ell}\sum_{\substack{w\in B\\w\mid p}}\frac{f_w}{[F:\mathbb Q]}\operatorname{qOrder}(w).
$$

`thetaLocalData` 使用这些根，并将同一 q-pilot 枚举的坏位在剩余特征映射下的像作为坏剩余特征集。它记录根非零、阶数非负、幂等式和加权恒等式。 [加权恒等式](../../../../Solutions/Source_ReferenceIutThetaLocalData.lean#L48) · [局部 Θ 数据](../../../../Solutions/Source_ReferenceIutThetaLocalData.lean#L98) · [q-pilot 的坏剩余特征](../../../../Solutions/Source_ReferenceIutThetaLocalBadChars.lean#L26)

`concreteThetaDataExistence_of_localArithmetic` 接收 `CI : CurveInputs`、`anab : AnabelianExistence AG TG`，以及 $T.\mathrm{cbsSet}(K)\cap T.\mathrm{ptLE}(T.\mathrm{tripod},d)$ 内每个点对应曲线的有理 2 挠点下界。几何输入在模域到挠点域的典范包含下给出一个轨形曲线及依赖于该轨形曲线的几何局部数据。记 $I$ 为 `CI.toCorollary22Inputs`。 取 $x\in T.\mathrm{cbsSet}(K)\cap T.\mathrm{ptLE}(T.\mathrm{tripod},d)$ 且 $x$ 在 `CI.excCore` 之外，再取素数 $\ell\ge7$。P2 和 P5 使用 `I.localData x hx` 的坏位。P2 要求这些位的 Tate 阶数均不被 $\ell$ 整除。P5 要求其中至少有一位的剩余特征在 $\{2,\ell\}$ 之外。定理还接收 `SL2Image x ℓ` 作为该素数的像条件。由 `x ∉ CI.excCore` 得到所选曲线的 core 假设。所选的 `P := CI.pointThetaData ...` 带有这条曲线和这个素数的初始数据及 q-pilot。`P.localTheory` 构造 `LocalTheory.{u,u} P.data.Kt`。`TL := P.localThetaData (htwo x hx)` 在同一挠点域上使用这个局部理论和 `P.qPilotInputs`。 [几何输入](../../../../Solutions/Source_ReferenceIutInitialThetaData.lean#L26) · [逐点选取](../../../../Solutions/Source_ReferenceIutPointThetaData.lean#L39) · [局部理论及定理假设](../../../../Solutions/Source_ReferenceIutPointLocalTheta.lean#L29)

对每个这样的点和素数，剩余的算术输入为 `TowerArithmetic P.data P.localTheory (TL.withBadChars P.qPilotInputs)`，包含 R4 及步骤 (ii)、(iii)。结论 `ConcreteThetaDataExistence` 还假设 P3，即剩余特征为 $\ell$ 的每个坏位都满足 $hv(w)<\sqrt{I.h(x)}$。组装取 $D=P.\mathrm{data}$，并取局部数据 `TL.withBadChars P.qPilotInputs`。结论给出 $D.\ell=\ell$ 和 $D.\mathrm{dmod}\le d$，并将 q-pilot 的 `logQ` 等同于 `heightOther 2 ℓ`，即在剩余特征 $2$ 和 $\ell$ 之外的局部高度和。结论还将点的 `logDiff` 等同于三脚架域不同理想的归一化对数次数。点的导子量介于 $D.\mathrm{logConductorDeg}$ 和 $D.\mathrm{logConductorDeg}+\log(2\ell)$ 之间。 [塔算术字段](../../../../Solutions/Source_ReferenceIutConcreteInvariants.lean#L173) · [P7 陈述](../../../../Solutions/Source_ReferenceIutConcreteExistence.lean#L36) · [逐点组装](../../../../Solutions/Source_ReferenceIutCurveConcreteExistence.lean#L54)

审查对受审声明只报告 `propext`、`Classical.choice` 和 `Quot.sound`。 [PointLocalTheta 审查](../../../../.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-021884-70058d70-result.json) · [参考 P7 构造](../../../../../refer/iut/Iut/Tripod/Main.lean#L86)

## 日本語

初期 Θ データ $D$ を固定し、基礎体を $F$、ねじれ点体を $K_t$、素数を $\ell$ とする。$B=$ `badPlacesOver D.F D.E D.VBad` は、モジュライ体の指定された悪い素点の上にある $F$ の有限素点の集合である。`TwoTorsionRational D` は、$2$ 倍すると単位元になる $E(F)$ の点が、単位元を含めて少なくとも四つあることを要求する。Legendre 曲線では $\mathcal{O},(0,0),(1,0),(\lambda,0)$ がその四点である。`two_torsion_curveOf` は、三脚の各点に対応する曲線について必要な下界を与える。 [有理 2 ねじれ点の仮定](../../../../Solutions/Source_ReferenceIutThetaLocalRoots.lean#L35) · [Legendre 曲線の 2 ねじれ点](../../../../Solutions/Source_TripodTwoTorsion.lean#L23) · [三脚の点に対応する曲線](../../../../Solutions/Source_TripodTwoTorsion.lean#L81)

$B$ の上にある $K_t$ の各素点 $v$ で、`exists_qroot` は、選ばれた局所 Tate 曲線のパラメータの $2\ell$ 乗根を完備化 $(K_t)_v$ の中に与える。証明は、ねじれ点体上の全 $\ell$ ねじれ点と、有理 2 ねじれ点から完備化上のねじれ点への単射を用いる。`qrootOf` はそのような素点では根 $r_v$ を選び、それ以外では $r_v=1$ とする。$v$ が $w\in B$ の上にあるとき、Tate パラメータの整合性から $r_v^{2\ell}=\iota_{w,v}(q_w)$ が成り立つ。ここで $\iota_{w,v}\colon F_w\to (K_t)_v$ は完備化の埋め込みである。$v$ での位数 $\operatorname{ord}_p$ は $\operatorname{ord}_p(p)=1$ で正規化する。剰余標数を $p$、分岐指数を $e_w=e(w/p)$、$q_w$ の Tate 位数を $\operatorname{qOrder}(w)$ とすると、位数は次の式で与えられる。

$$
\operatorname{ord}_p(r_v)=\frac{\operatorname{qOrder}(w)}{2\ell e_w}.
$$

[根の存在](../../../../Solutions/Source_ReferenceIutThetaLocalRoots.lean#L100) · [根の選択](../../../../Solutions/Source_ReferenceIutThetaLocalRoots.lean#L122) · [Tate パラメータの整合性](../../../../Solutions/Source_ReferenceIutThetaLocalRoots.lean#L141) · [位数の公式](../../../../Solutions/Source_ReferenceIutThetaLocalData.lean#L29)

有理素数 $p$ ごとに、`sum_weight_ordp_qrootOf` は台集合が $B$ に一致する有限集合を用いる。局所理論の $p$ 上のファイバーを、$K_t$ の有限素点 $v\mid p$ と同一視する。$w$ の $p$ 上の剰余次数を $f_w$ とすると、$F$ の素点ごとに項をまとめて次の等式を得る。

$$
\sum_{v\mid p}\frac{[(K_t)_v:\mathbb Q_p]}{[K_t:\mathbb Q]}\operatorname{ord}_p(r_v)
=\frac{1}{2\ell}\sum_{\substack{w\in B\\w\mid p}}\frac{f_w}{[F:\mathbb Q]}\operatorname{qOrder}(w).
$$

`thetaLocalData` はこれらの根を用い、同じ q-pilot が列挙する悪い素点の剰余標数の像を悪い剰余標数の集合とする。根が非零であること、位数が非負であること、べき乗の等式、および重み付きの等式を記録する。 [重み付きの等式](../../../../Solutions/Source_ReferenceIutThetaLocalData.lean#L48) · [局所 Θ データ](../../../../Solutions/Source_ReferenceIutThetaLocalData.lean#L98) · [q-pilot の悪い剰余標数](../../../../Solutions/Source_ReferenceIutThetaLocalBadChars.lean#L26)

`concreteThetaDataExistence_of_localArithmetic` は、`CI : CurveInputs`、`anab : AnabelianExistence AG TG`、および $T.\mathrm{cbsSet}(K)\cap T.\mathrm{ptLE}(T.\mathrm{tripod},d)$ に属する各点の曲線について、有理 2 ねじれ点数の下界を受け取る。幾何学の仮定は、モジュライ体からねじれ点体への標準的な包含のもとで、一つのオービ曲線と、そのオービ曲線に依存する幾何学的な局所データを与える。$I$ を `CI.toCorollary22Inputs` とする。$x\in T.\mathrm{cbsSet}(K)\cap T.\mathrm{ptLE}(T.\mathrm{tripod},d)$ で `CI.excCore` に属さない点と、素数 $\ell\ge7$ を取る。P2 と P5 は `I.localData x hx` の悪い素点についての条件である。P2 はこれらの素点の Tate 位数がどれも $\ell$ で割り切れないことを要求する。P5 はそのうち剰余標数が $\{2,\ell\}$ の外にある素点の存在を要求する。この素数での像の条件 `SL2Image x ℓ` も仮定する。`x ∉ CI.excCore` から、選ばれた曲線の core に関する仮定が従う。`P := CI.pointThetaData ...` は、この曲線と素数の初期データおよび q-pilot を持つ。`P.localTheory` は `LocalTheory.{u,u} P.data.Kt` を構成する。`TL := P.localThetaData (htwo x hx)` は、同じねじれ点体でこの局所理論と `P.qPilotInputs` を用いる。 [幾何学の仮定](../../../../Solutions/Source_ReferenceIutInitialThetaData.lean#L26) · [点ごとの選択](../../../../Solutions/Source_ReferenceIutPointThetaData.lean#L39) · [局所理論と定理の仮定](../../../../Solutions/Source_ReferenceIutPointLocalTheta.lean#L29)

この条件を満たす各点と各素数について、残る算術の仮定は `TowerArithmetic P.data P.localTheory (TL.withBadChars P.qPilotInputs)` である。これには R4 とステップ (ii)、(iii) が含まれる。結論 `ConcreteThetaDataExistence` は、剰余標数が $\ell$ のすべての悪い素点で $hv(w)<\sqrt{I.h(x)}$ が成り立つという P3 も仮定する。組み立てでは $D=P.\mathrm{data}$ と局所データ `TL.withBadChars P.qPilotInputs` を用いる。結論は $D.\ell=\ell$ と $D.\mathrm{dmod}\le d$ を与える。q-pilot の `logQ` は `heightOther 2 ℓ` に等しい。これは剰余標数 $2$ と $\ell$ を除いた局所高さの和である。点の `logDiff` は三脚体のディファレントの正規化対数次数に等しい。点の導手不変量の下界は $D.\mathrm{logConductorDeg}$、上界は $D.\mathrm{logConductorDeg}+\log(2\ell)$ である。 [体の塔の算術条件](../../../../Solutions/Source_ReferenceIutConcreteInvariants.lean#L173) · [P7 の定式化](../../../../Solutions/Source_ReferenceIutConcreteExistence.lean#L36) · [点ごとの組み立て](../../../../Solutions/Source_ReferenceIutCurveConcreteExistence.lean#L54)

レビューは、確認対象の宣言について `propext`、`Classical.choice`、`Quot.sound` のみを報告する。 [PointLocalTheta のレビュー](../../../../.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-021884-70058d70-result.json) · [参照元の P7 の構成](../../../../../refer/iut/Iut/Tripod/Main.lean#L86)
