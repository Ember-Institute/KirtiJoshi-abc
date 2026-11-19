# Pointwise P7 for the Legendre curves

## English

The theorem `concreteThetaDataExistence_from_source` takes `P : CurveProviders`, `K : CompactlyBounded`, a degree bound `d`, and a real constant `TK`. It assumes `CF : CurveFactsProp P K d TK` for the cyclic subgroup estimate. It also takes `CoreFinitenessHyp P K d AG` for finiteness of the exceptional core locus, `NorthcottHyp`, and `AnabelianExistence AG TG`. It supplies `legendreHeight P K` and `twoAdicBound P K` when constructing the `CurveInputs`. The result is `ConcreteThetaDataExistence` for the associated `Corollary22Inputs`. [Theorem](../../../../Solutions/Source_TripodP7.lean#L28) · [Curve inputs](../../../../Solutions/Source_TripodCurveInputsFromSource.lean#L48) · [Cyclic and core assumptions](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts.lean#L50)

The P7 statement quantifies over each $x\in \mathrm{cbsSet}(K)\cap\mathrm{ptLE}(d)$ outside `excCore` and each prime $\ell\ge7$ satisfying the following conditions. [Pointwise inputs](../../../../Solutions/Source_ReferenceIutConcreteExistence.lean#L36)

- (P2) $\ell$ does not divide the valuation of the Tate parameter at any bad place.
- (P3) At each bad place of residue characteristic $\ell$, the Tate parameter valuation is less than $\sqrt{I.h(x)}$, where `I` is the associated `Corollary22Inputs`.
- (P5) Some bad place has residue characteristic distinct from $2$ and $\ell$.
- (P6) `SL2Image x ℓ` supplies the inclusion $\mathrm{SL}_2(\mathbf F_\ell)\subseteq\operatorname{im}(\rho_\ell)$ for the selected curve.

The pointwise construction uses (P2), (P5), and (P6). It supplies rational $2$-torsion, constructs the initial theta data and q-pilot, and uses the concrete local theory on the same torsion field. It fills `TowerArithmetic` on `TL.withBadChars X.qPilotInputs` using `TowerLocalFacts`, the relative ramification bound of two over bad moduli places, and the degree bounds. Its fields give (R4), step (ii) for the normalized different, and step (iii) for the sum over the distinguished primes of that q-pilot. The witnesses also give the prime equality, the degree bound, and the q-pilot, different, and conductor comparisons with the point. [Assembly](../../../../Solutions/Source_TripodP7.lean#L34) · [Tower arithmetic](../../../../Solutions/Source_ReferenceIutTowerArithmetic.lean#L27)

## 中文

`concreteThetaDataExistence_from_source` 取 `P : CurveProviders`、`K : CompactlyBounded`、次数上界 `d` 和实常数 `TK`。其显式前提为供应循环子群估计的 `CF : CurveFactsProp P K d TK`、断言核心条件例外集有限的 `CoreFinitenessHyp P K d AG`、`NorthcottHyp` 和 `AnabelianExistence AG TG`。构造 `CurveInputs` 时，它供应 `legendreHeight P K` 与 `twoAdicBound P K`。所得 `ConcreteThetaDataExistence` 对应这组 `Corollary22Inputs`。 [定理](../../../../Solutions/Source_TripodP7.lean#L28) · [曲线输入](../../../../Solutions/Source_TripodCurveInputsFromSource.lean#L48) · [循环子群与核心前提](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts.lean#L50)

P7 陈述量化 $\mathrm{cbsSet}(K)\cap\mathrm{ptLE}(d)$ 中位于 `excCore` 之外的每个点 $x$，以及满足下列条件的每个素数 $\ell\ge7$。 [逐点输入](../../../../Solutions/Source_ReferenceIutConcreteExistence.lean#L36)

- (P2) 对每个坏位，Tate 参数的赋值不被 $\ell$ 整除。
- (P3) 对剩余特征为 $\ell$ 的每个坏位，Tate 参数的赋值小于 $\sqrt{I.h(x)}$，其中 `I` 为相应的 `Corollary22Inputs`。
- (P5) 存在剩余特征不同于 $2$ 和 $\ell$ 的坏位。
- (P6) `SL2Image x ℓ` 要求所选曲线的模 $\ell$ 表示满足 $\mathrm{SL}_2(\mathbf F_\ell)\subseteq\operatorname{im}(\rho_\ell)$。

逐点构造使用 (P2)、(P5) 和 (P6)。证明供应有理 $2$ 挠点，构造初始 theta 数据及其 q-pilot，并在同一挠点域上采用具体局部理论。它使用 `TowerLocalFacts`、模域坏位上方的相对分歧指数上界 $2$ 和次数界，为 `TL.withBadChars X.qPilotInputs` 填入 `TowerArithmetic`。其字段给出 (R4)、归一化不同理想的步骤 (ii)，以及对该 q-pilot 指定素数求和的步骤 (iii)。 所得见证还满足素数等式、次数界以及与该点的 q-pilot、不同理想和导子比较。 [装配](../../../../Solutions/Source_TripodP7.lean#L34) · [域塔算术](../../../../Solutions/Source_ReferenceIutTowerArithmetic.lean#L27)

## 日本語

`concreteThetaDataExistence_from_source` は `P : CurveProviders`、`K : CompactlyBounded`、次数の上界 `d`、実定数 `TK` を取る。巡回部分群の評価を与える `CF : CurveFactsProp P K d TK` と、核の条件の例外集合の有限性を表す `CoreFinitenessHyp P K d AG` を仮定する。さらに `NorthcottHyp` と `AnabelianExistence AG TG` を取る。`CurveInputs` の構成には `legendreHeight P K` と `twoAdicBound P K` を使う。結論は対応する `Corollary22Inputs` に対する `ConcreteThetaDataExistence` である。 [定理](../../../../Solutions/Source_TripodP7.lean#L28) · [曲線の入力](../../../../Solutions/Source_TripodCurveInputsFromSource.lean#L48) · [巡回部分群と核の仮定](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts.lean#L50)

P7 の命題は $\mathrm{cbsSet}(K)\cap\mathrm{ptLE}(d)$ に属し `excCore` の外にある各点 $x$ と、次の条件を満たす各素数 $\ell\ge7$ を対象とする。 [各点での入力](../../../../Solutions/Source_ReferenceIutConcreteExistence.lean#L36)

- (P2) 各悪い素点で Tate パラメータの付値は $\ell$ で割り切れない。
- (P3) 剰余標数が $\ell$ の各悪い素点で Tate パラメータの付値は $\sqrt{I.h(x)}$ より小さい。ここで `I` は対応する `Corollary22Inputs` である。
- (P5) 剰余標数が $2$ と $\ell$ のいずれとも異なる悪い素点が存在する。
- (P6) `SL2Image x ℓ` は、選んだ曲線の mod $\ell$ 表現に対して $\mathrm{SL}_2(\mathbf F_\ell)\subseteq\operatorname{im}(\rho_\ell)$ を与える。

各点での構成は (P2)、(P5)、(P6) を使う。証明は有理 $2$ ねじれ点を与え、初期 theta データと q-pilot を構成し、同じねじれ点体上の具体的な局所理論を使う。`TowerLocalFacts`、モジュライ体の悪い素点の上での相対分岐指数の上界 $2$、および拡大次数の上界から、`TL.withBadChars X.qPilotInputs` 上の `TowerArithmetic` を得る。そのフィールドは (R4)、正規化ディファレントのステップ (ii)、同じ q-pilot の指定素数の和を評価するステップ (iii) を与える。 得られるデータは素数の等式と次数の上界を満たし、点の q-pilot、ディファレント、導手との比較も与える。 [構成](../../../../Solutions/Source_TripodP7.lean#L34) · [体の塔の算術](../../../../Solutions/Source_ReferenceIutTowerArithmetic.lean#L27)
