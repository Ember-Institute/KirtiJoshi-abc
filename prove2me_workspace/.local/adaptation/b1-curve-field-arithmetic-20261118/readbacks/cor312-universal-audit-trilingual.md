# Counterexample to the universal Corollary 3.12 premise

Adapted source SHA-256 `a2237987ac1161432653e645c2cb549c73cafd883aaefe923860afa99fe87f89`. The MCP-CI leaf check, object build, and project review exited with code 0 and reported no diagnostics. The review checked the signature of the negated premise. It printed only `propext`, `Classical.choice`, and `Quot.sound` for all five public declarations. [Leaf check ci-023146-92a4a68d](../receipts/round-ci-023146-92a4a68d-result.json) · [Object build ci-023154-fe73209f](../receipts/round-ci-023154-fe73209f-result.json) · [Review source](../ReviewCor312UniversalAudit.lean#L11) · [Review ci-023160-024629d3](../receipts/round-ci-023160-024629d3-result.json)

## English

Fix the geometry interfaces `AG` and `TG`. Supply `D : InitialThetaData AG TG`, `LT : LocalTheory D.Kt`, `TL : ThetaLocalData D LT`, and `QI : QPilotInputs D`. Let $L$ be `QI.qPilot.lhs`. The theorem `ThetaLocalData.exists_not_corollary312Variant` constructs a local theory `T` and local theta data `U` on the same `D`. It gives a strict failure of the inequality for `concreteVariantData D T U QI`. The construction needs the supplied data tuple and can start from any such tuple. [Variant inequality](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_Statement.lean#L113) · [Concrete data constructor](../../../../Solutions/Source_ReferenceIutConcreteThetaRegion.lean#L238) · [Counterexample theorem](../../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L351)

For $0<r\le1$, `LocalTheory.withArchimedeanRadius` uses the log-shell $rB_c$ for each archimedean component $c$, where $B_c$ is its integral unit ball. Its archimedean set of indeterminacy maps is $\{\mathrm{id}\}$. Positive real scalars give units, so scaled-integral admissibility gives the required admissibility and relative compactness. The archimedean bound `prop15` holds since $r\le1\le\pi^{|I|}$ for the label set $I$. The finite-place fields follow from `LT`. The corresponding `ThetaLocalData.withArchimedeanRadius` takes the same roots and bad residue characteristics from `TL`. It transports the weighted root-valuation sum along the equivalence of finite fibers. [Local-theory construction](../../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L54) · [Archimedean upper bound](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L304) · [Theta-data construction](../../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L121)

The archimedean theta-pilot component is the union of images of $rB_c$ under $\{\mathrm{id}\}$, hence it is $rB_c$. The product of these balls already belongs to the hull class, so its hull equals that product. The scaling formula gives $\log r$ in every component. The tuple weights sum to $1$, since each place fiber has total weight $1$. Thus the packet contributes $\log r$ at the archimedean rational place. [Scaling formula](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L202) · [Archimedean hull and packet volume](../../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L172)

At a finite prime, the pilot products agree with the original products. Their least hulls agree because the input regions and hull classes agree. The finite packet volumes therefore agree for all radii. Let $R(r)$ be the right-hand side for radius $r$. Each capsule has the same global log-volume difference $\log r$ relative to radius $1$. The number of capsules is $\lfloor(\ell-1)/2\rfloor>0$ since $\ell\ge5$. Averaging gives `rhs_withArchimedeanRadius`.

$$
R(r)=R(1)+\log r.
$$

[Finite packet volumes](../../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L214) · [Global volume](../../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L273) · [Right-hand side](../../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L322)

Set $r=\exp(\min(0,L-R(1)-1))$. Then $0<r\le1$ and $R(r)\le L-1<L$. The theorem `ThetaLocalData.not_forall_corollary312Variant` applies this witness to the claimed universal premise over all `D', T, U, Q` for the fixed `AG` and `TG`. This is the quantifier used by the universal `h312` in the adapted high-height theorem and in the reference tripod implication. The (P7) premise asks for the inequality on every bundle identified by `IsSourceP7Variant`. This predicate requires equality with the bundle from `pointThetaData` for an admissible point and prime. The inequality on that family remains an open proof obligation. [Negation with its input tuple](../../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L369) · [Adapted universal premise](../../../../Solutions/Source_TripodCanonicalCorollary22PrimeEstimates.lean#L18) · [Reference premise](../../../../../refer/iut/Iut/Tripod/Main.lean#L130) · [Source (P7) family](../../../../Solutions/Source_TripodP7.lean#L27)

## 中文

固定几何接口 `AG` 和 `TG`。给定 `D : InitialThetaData AG TG`、`LT : LocalTheory D.Kt`、`TL : ThetaLocalData D LT` 及 `QI : QPilotInputs D`。记 `QI.qPilot.lhs` 为 $L$。定理 `ThetaLocalData.exists_not_corollary312Variant` 在同一个 `D` 上构造局部理论 `T` 和局部 θ 数据 `U`，使 `concreteVariantData D T U QI` 的不等式严格失败。构造以任意一组这样的已给数据为起点。 [变体不等式](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_Statement.lean#L113) · [具体数据构造器](../../../../Solutions/Source_ReferenceIutConcreteThetaRegion.lean#L238) · [反例定理](../../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L351)

对 $0<r\le1$，`LocalTheory.withArchimedeanRadius` 取每个阿基米德分量 $c$ 的对数壳为 $rB_c$，其中 $B_c$ 是该分量的整单位球。其阿基米德不定性映射的集合为 $\{\mathrm{id}\}$。正实数标量映为单位元，故由整结构缩放的可容许性得到所需的可容许性与相对紧性。对标签集 $I$，由 $r\le1\le\pi^{|I|}$ 得到阿基米德上界 `prop15`。有限处字段取自 `LT`。相应的 `ThetaLocalData.withArchimedeanRadius` 从 `TL` 取同一组根和坏剩余特征，并沿有限纤维等价搬运根赋值的加权和。 [局部理论构造](../../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L54) · [阿基米德上界](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L304) · [θ 数据构造](../../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L121)

阿基米德 θ-pilot 分量是 $rB_c$ 在 $\{\mathrm{id}\}$ 下的像的并，故等于 $rB_c$。这些球的乘积已属于包络区域类，故其包络等于该乘积。缩放公式给每个分量的对数体积 $\log r$。每个位置纤维的权重和为 $1$，故元组权重和也为 $1$，在阿基米德有理位的包体积贡献即为 $\log r$。 [缩放公式](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L202) · [阿基米德包络与包体积](../../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L172)

在有限素数处，pilot 乘积等于原来的乘积。输入区域与包络区域类相同，故最小包络也相同。因此所有半径给出相同的有限包体积。记半径为 $r$ 时的右端为 $R(r)$。与半径 $1$ 相比，每个胶囊的全局对数体积都相差 $\log r$。由 $\ell\ge5$，胶囊数 $\lfloor(\ell-1)/2\rfloor>0$。取平均得到 `rhs_withArchimedeanRadius`。

$$
R(r)=R(1)+\log r.
$$

[有限包体积](../../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L214) · [全局体积](../../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L273) · [右端](../../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L322)

取 $r=\exp(\min(0,L-R(1)-1))$，则 $0<r\le1$，且 $R(r)\le L-1<L$。定理 `ThetaLocalData.not_forall_corollary312Variant` 用此见证反驳固定 `AG` 和 `TG` 下对所有 `D', T, U, Q` 的全称前提。适配的高高度定理与参考三足曲线推导中的全称 `h312` 均采用此量化。(P7) 前提要求对每个满足 `IsSourceP7Variant` 的数据包证明不等式。此谓词要求数据包等于对适用的点和素数用 `pointThetaData` 构造的结果。该数据族上的不等式仍待证明。 [含已给数据的全称否定](../../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L369) · [适配的全称前提](../../../../Solutions/Source_TripodCanonicalCorollary22PrimeEstimates.lean#L18) · [参考前提](../../../../../refer/iut/Iut/Tripod/Main.lean#L130) · [来源 (P7) 数据族](../../../../Solutions/Source_TripodP7.lean#L27)

## 日本語

幾何のインターフェース `AG` と `TG` を固定する。`D : InitialThetaData AG TG`、`LT : LocalTheory D.Kt`、`TL : ThetaLocalData D LT`、`QI : QPilotInputs D` を与え、`QI.qPilot.lhs` を $L$ とおく。定理 `ThetaLocalData.exists_not_corollary312Variant` は同じ `D` 上の局所理論 `T` と局所 θ データ `U` を構成する。`concreteVariantData D T U QI` において右辺は左辺より真に小さくなる。構成は、与えられた任意のこのようなデータの組から始まる。 [変種の不等式](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_Statement.lean#L113) · [具体的なデータの構成](../../../../Solutions/Source_ReferenceIutConcreteThetaRegion.lean#L238) · [反例の定理](../../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L351)

$0<r\le1$ とする。`LocalTheory.withArchimedeanRadius` はアルキメデス成分 $c$ ごとに、整単位球 $B_c$ の拡大縮小 $rB_c$ を対数殻とする。アルキメデスでの不定性写像の集合は $\{\mathrm{id}\}$ とする。正の実数スカラーは単元に移るので、整構造のスカラー倍に関する許容性から、必要な許容性と相対コンパクト性が従う。ラベル集合を $I$ とすると、$r\le1\le\pi^{|I|}$ によってアルキメデスでの上界 `prop15` が成り立つ。有限素点のフィールドは `LT` から取る。対応する `ThetaLocalData.withArchimedeanRadius` は `TL` の根と悪い剰余標数を用い、有限ファイバーの同値を通じて根の付値の重み付き和を移す。 [局所理論の構成](../../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L54) · [アルキメデスでの上界](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L304) · [θ データの構成](../../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L121)

アルキメデスでの θ-pilot 成分は $\{\mathrm{id}\}$ による $rB_c$ の像の和集合なので、$rB_c$ に等しい。球の積は包の領域のクラスにすでに属するので、その包は積そのものである。拡大縮小の公式から各成分の対数体積は $\log r$ となる。各素点のファイバーで重みの総和が $1$ なので、タプルの重みの総和も $1$ である。従って有理数体のアルキメデス素点でのパケットの寄与は $\log r$ となる。 [拡大縮小の公式](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L202) · [アルキメデスでの包とパケット体積](../../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L172)

有限素数では pilot の積が元の積と一致する。入力領域と包の領域のクラスが同じなので、最小の包も一致する。従って有限素数でのパケット体積はすべての半径で等しい。半径 $r$ に対する右辺を $R(r)$ とする。半径 $1$ の場合と比べると、各カプセルの大域対数体積の差は $\log r$ である。$\ell\ge5$ なのでカプセル数は $\lfloor(\ell-1)/2\rfloor>0$ である。平均を取ると `rhs_withArchimedeanRadius` の等式を得る。

$$
R(r)=R(1)+\log r.
$$

[有限素数でのパケット体積](../../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L214) · [全体積](../../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L273) · [右辺](../../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L322)

$r=\exp(\min(0,L-R(1)-1))$ とすると、$0<r\le1$ かつ $R(r)\le L-1<L$ となる。定理 `ThetaLocalData.not_forall_corollary312Variant` は、この反例によって固定した `AG` と `TG` のもとでのすべての `D', T, U, Q` に対する全称の仮定を否定する。適応版の高い高さでの評価と参照元の三脚曲線についての含意における全称の `h312` は、この量化を使う。(P7) の仮定は `IsSourceP7Variant` を満たす各データの組に対して不等式を要求する。この述語は、条件を満たす点と素数から `pointThetaData` で構成したデータの組との等しさを要求する。そのデータ族についての不等式は証明課題として残る。 [入力データを伴う全称の否定](../../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L369) · [適応版の全称の仮定](../../../../Solutions/Source_TripodCanonicalCorollary22PrimeEstimates.lean#L18) · [参照元の仮定](../../../../../refer/iut/Iut/Tripod/Main.lean#L130) · [参照元の (P7) データ族](../../../../Solutions/Source_TripodP7.lean#L27)
