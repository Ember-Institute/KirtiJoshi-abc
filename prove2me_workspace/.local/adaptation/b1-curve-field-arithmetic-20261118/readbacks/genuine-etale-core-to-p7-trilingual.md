# Étale fundamental groups, cores, and P7 / Étale 基本群、核心与 P7 / エタール基本群、コアと P7

## English

### `normalizationHasCore_iff_of_cover`

Let $k$ be a field of characteristic zero, let $X,Y,C$ be model orbicurves over $k$, and let $c\colon X\to Y$ be a cover. Write $A_X,A_Y,A_C$ for their normalization presentations. The theorem states that $A_C$ is a core of $A_X$ if and only if it is a core of $A_Y$. For affine presentations $A,W$, `LocBar A W` means that $A$ and $W$ have a common finite étale cover. A core of $A$ belongs to this class and receives exactly one finite étale cover from every member. [Definitions](../../../../Solutions/Source_ReferenceIutCanLiftPresentation.lean#L22) · [Theorem](../../../../Solutions/Source_ReferenceIutGenuineCore.lean#L73) · [Pi1 reference](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Core.lean#L125)

The data of $c$ identify the elliptic curves underlying $X$ and $Y$. This places the two normalization fields in one algebraic closure of the rational function field of the $x$-coordinate. The induced cover of the normalization presentations has the ring map given by the inclusion of those fields in the direction from the field of $Y$ to the field of $X$. For any cover $V\to A_Y$, the proof embeds the function field of $V$ in the same algebraic closure and normalizes in its compositum with the field of $X$. At a closed point $w$ above $v$ on the presentation of $Y$, the new multiplicity is $m_Y(v)/e(w\mid v)$. The ramification divisibility in the compositum and the ramification tower formula give the cover conditions for the two projections. [Ring map](../../../../Solutions/Source_ReferenceIutGenuineNormalizationCover.lean#L148) · [Multiplicities](../../../../Solutions/Source_ReferenceIutCanLiftSubfieldPullback.lean#L33) · [Common cover](../../../../Solutions/Source_ReferenceIutCanLiftPresentationPullback.lean#L85) · [Pi1 reference](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Pullback.lean#L398)

A common cover of $A_X$ and $W$ also covers $A_Y$ by composition. Given a common cover $V$ of $A_Y$ and $W$, the compositum construction gives a common cover of $A_X$ and $V$, which also covers $W$. Thus the two `LocBar` classes agree, and the condition of being terminal in that class transfers in both directions. [Transfer of core terminality](../../../../Solutions/Source_ReferenceIutGenuineCore.lean#L20) · [Application to the normalization presentations](../../../../Solutions/Source_ReferenceIutGenuineCore.lean#L52)

### `genuineEtalePi1Theory`

Given `h27 : CanLift27.{u}`, the definition constructs an `EtalePi1Theory.{u}`. In characteristic zero, its group is the profinite quotient of the stabilizer of the normalization data by its closed inertia kernel. Each cover induces a continuous homomorphism that is an open embedding. In positive characteristic the definition assigns the one-element group and the identity homomorphism. The core relation is `normalizationHasCore`, which includes a witness of characteristic zero. Its cover law is `normalizationHasCore_iff_of_cover`. [Groups and cover maps](../../../../Solutions/Source_ReferenceIutGenuinePi1.lean#L58) · [Core relation](../../../../Solutions/Source_ReferenceIutCanLiftPresentation.lean#L118) · [Theory](../../../../Solutions/Source_ReferenceIutGenuineCore.lean#L80) · [iut reference](../../../../../refer/iut/Iut/Anabelian/GenuineEtale.lean#L111)

The four exceptional rational $j$-values are $0$, $1728$, $488095744/125$, and $1556068/81$. For each elliptic Weierstrass curve in characteristic zero with $j$ outside this set, $h_{27}$ supplies the sign quotient of the once-punctured curve as its core. The parameter-free `canLift27 : CanLift27.{0}` follows from `canLift27Complex` by Lefschetz descent. The complex proof uses squared-trace integrality in the Fricke normal form and the proved uniformizations of the four Takeuchi model curves. For a dense commensurator, the integrality proof first gives rationality and then bounds the $p$-adic norm of each squared trace by one at every prime. [Exceptional values and core theorem](../../../../Solutions/Source_ReferenceIutCanLiftPresentation.lean#L104) · [Trace integrality](../../../../Solutions/Source_ReferenceIutCanLiftFinal.lean#L26) · [Complex assembly](../../../../Solutions/Source_ReferenceIutCanLiftComplexFromFricke.lean#L15) · [Lefschetz descent](../../../../Solutions/Source_ReferenceIutCanLiftLefschetz.lean#L16) · [Proposition 2.7](../../../../Solutions/Source_ReferenceIutCanLiftProp27.lean#L8)

### `pointThetaDataExistence_from_canLift27`

Set $\mathrm{AG}=\mathrm{modelAG}(\mathrm{genuineEtalePi1Theory}\ \mathrm{canLift27})$. The theorem takes a curve provider $P$, a compactly bounded set $K$, a degree bound $d$, a real parameter $TK$ and cyclic bound `CF : CurveFactsProp P K d TK`, `hN : NorthcottHyp`, and tempered geometry $\mathrm{TG}$ over $\mathrm{AG}$ with `anab : AnabelianExistence AG TG`. It uses the once-punctured core theorem and the base-change identities for the puncture and the sign quotient to prove the universal core condition when the selected curve has nonexceptional $j$. The exceptional $j$-fibres are finite for the provider's Legendre curves. This supplies `CoreFinitenessHyp P K d AG` for the given $P,K,d$. The theorem passes that proof to `pointThetaDataExistence_from_source` and constructs the same `CI` in the conclusion using `legendreHeight P K` and `twoAdicBound P K`. [Base change](../../../../Solutions/Source_TripodCoreGeometry.lean#L38) · [Finite exceptional set](../../../../Solutions/Source_TripodCoreFiniteness.lean#L62) · [Model core finiteness](../../../../Solutions/Source_TripodCoreModel.lean#L71) · [Endpoint](../../../../Solutions/Source_TripodP7FromCanLift.lean#L17)

Write $T=\mathrm{tripodTheory}$ and $I=\mathrm{CI.toCorollary22Inputs}$. The conclusion applies to each tripodal point $x$ with a proof $h_x$ that $x\inT.\mathrm{cbsSet}(K)\cap T.\mathrm{ptLE}(T.\mathrm{tripod},d)$, outside $I.\mathrm{excCore}$. It then applies to every prime $\ell\ge7$ with the following properties. Put $L=I.\mathrm{localData}(x,h_x)$. The places in $L.\mathrm{bad}$ are the finite places of multiplicative reduction. At each such place $w$, $L.\mathrm{hv}(w)$ is the integer order of the Tate parameter. [Quantifiers](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Corollary22.lean#L112)

- P2 requires $\ell\nmid L.\mathrm{hv}(w)$ at every $w\in L.\mathrm{bad}$.
- P3 requires $L.\mathrm{hv}(w)<\sqrt{I.\mathrm{h}(x)}$ at each $w\in L.\mathrm{bad}$ with residue characteristic $L.\mathrm{p}(w)=\ell$, with the Tate order viewed as a real number.
- P5 requires one $w\in L.\mathrm{bad}$ with $L.\mathrm{p}(w)\notin\{2,\ell\}$.
- P6 is `I.SL2Image x ℓ`. It requires that the mod-$\ell$ image contain $\mathrm{SL}_2(\mathbb Z/\ell\mathbb Z)$ for every membership and primality proof. [Image condition](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean#L154)

The result supplies variant data $X$ and invariants $\mathrm{inv}$ on $X$. The predicate `IsSourceP7Variant CI anab` records the construction from the pointwise theta data and a witness that the full $2$-torsion is rational, with the local theta data augmented by the distinguished residue characteristics. The tower arithmetic gives a `Theorem110Certificate inv` and `Nonempty inv.LocalEstimate`. The remaining conclusions are

$$
\begin{gathered}
X.\ell=\ell,\qquad X.\mathrm{dmod}\le d,\qquad
X.\mathrm{qPilot.logQ}=L.\mathrm{heightOther}(2,\ell),\\
T.\mathrm{logDiff}(T.\mathrm{tripod},x)=\mathrm{inv.logDtpd},\qquad
\mathrm{inv.logFtpd}\leT.\mathrm{logCond}(T.\mathrm{tripod},x)\le\mathrm{inv.logFtpd}+\log(2\ell).
\end{gathered}
$$

Here $X.\mathrm{dmod}$ is the degree of the field of moduli over $\mathbb Q$, and $\mathrm{inv.logDtpd}$ and $\mathrm{inv.logFtpd}$ are the normalized logarithmic different and conductor degrees used by the variant. The iut reference is the repository copy at revision `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`. [Variant predicate](../../../../Solutions/Source_TripodP7.lean#L27) · [Witnesses and bounds](../../../../Solutions/Source_TripodP7.lean#L95) · [iut P7 construction](../../../../../refer/iut/Iut/Tripod/Main.lean#L86)

## 简体中文

### `normalizationHasCore_iff_of_cover`

设 $k$ 是特征零域，$X,Y,C$ 是 $k$ 上的模型轨形曲线，$c\colon X\to Y$ 是一个覆盖。记三者的正规化表示为 $A_X,A_Y,A_C$。定理断言，$A_C$ 是 $A_X$ 的核心当且仅当它是 $A_Y$ 的核心。对仿射表示 $A,W$，`LocBar A W` 表示二者有公共有限 étale 覆盖。$A$ 的核心属于这一类，且该类中每个对象到核心都恰有一个有限 étale 覆盖。 [定义](../../../../Solutions/Source_ReferenceIutCanLiftPresentation.lean#L22) · [定理](../../../../Solutions/Source_ReferenceIutGenuineCore.lean#L73) · [Pi1 参考](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Core.lean#L125)

覆盖 $c$ 的数据给出 $X$ 与 $Y$ 的底层椭圆曲线相等的证明。两个正规化域都位于 $x$ 坐标有理函数域的同一个代数闭包内。诱导的正规化表示覆盖所用的环映射来自 $Y$ 的域到 $X$ 的域的包含。给定任意覆盖 $V\to A_Y$，证明把 $V$ 的函数域嵌入同一个代数闭包，再取它与 $X$ 的域的复合域并在其中正规化。对位于 $Y$ 的表示中闭点 $v$ 上方的闭点 $w$，新重数为 $m_Y(v)/e(w\mid v)$。复合域上的分歧整除关系和分歧指数的塔公式保证两个投影满足覆盖条件。 [环映射](../../../../Solutions/Source_ReferenceIutGenuineNormalizationCover.lean#L148) · [重数](../../../../Solutions/Source_ReferenceIutCanLiftSubfieldPullback.lean#L33) · [公共覆盖](../../../../Solutions/Source_ReferenceIutCanLiftPresentationPullback.lean#L85) · [Pi1 参考](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Pullback.lean#L398)

$A_X$ 与 $W$ 的公共覆盖经复合也覆盖 $A_Y$。给定 $A_Y$ 与 $W$ 的公共覆盖 $V$，复合域构造给出 $A_X$ 和 $V$ 的公共覆盖，它也覆盖 $W$。因此两个 `LocBar` 类相同，在该类中为终对象的条件可双向传递。 [核心终端性的传递](../../../../Solutions/Source_ReferenceIutGenuineCore.lean#L20) · [应用于正规化表示](../../../../Solutions/Source_ReferenceIutGenuineCore.lean#L52)

### `genuineEtalePi1Theory`

给定 `h27 : CanLift27.{u}`，此定义构造 `EtalePi1Theory.{u}`。在特征零时，它取正规化数据的稳定子按闭惯性核取商所得的预有限群。每个覆盖诱导连续同态，且该同态为开嵌入。在正特征时，定义取平凡群与恒等同态。核心关系是 `normalizationHasCore`，其中包含特征零的证明。其覆盖不变性由 `normalizationHasCore_iff_of_cover` 给出。 [群与覆盖映射](../../../../Solutions/Source_ReferenceIutGenuinePi1.lean#L58) · [核心关系](../../../../Solutions/Source_ReferenceIutCanLiftPresentation.lean#L118) · [理论](../../../../Solutions/Source_ReferenceIutGenuineCore.lean#L80) · [iut 参考](../../../../../refer/iut/Iut/Anabelian/GenuineEtale.lean#L111)

四个有理 $j$ 例外值为 $0$、$1728$、$488095744/125$ 和 $1556068/81$。对特征零域上 $j$ 在该集合之外的每条 Weierstrass 椭圆曲线，$h_{27}$ 给出其去掉一点后按符号对合取商所得的核心。无参定理 `canLift27 : CanLift27.{0}` 由 `canLift27Complex` 经 Lefschetz 下降得到。复数证明使用 Fricke 正规形中迹平方的整性和四条 Takeuchi 模型曲线的已证一致化。可公度子稠密时，整性证明先给出有理性，再在每个素数 $p$ 处把每个迹平方的 $p$-进范数界在一以内。 [例外值与核心定理](../../../../Solutions/Source_ReferenceIutCanLiftPresentation.lean#L104) · [迹的整性](../../../../Solutions/Source_ReferenceIutCanLiftFinal.lean#L26) · [复数情形](../../../../Solutions/Source_ReferenceIutCanLiftComplexFromFricke.lean#L15) · [Lefschetz 下降](../../../../Solutions/Source_ReferenceIutCanLiftLefschetz.lean#L16) · [命题 2.7](../../../../Solutions/Source_ReferenceIutCanLiftProp27.lean#L8)

### `pointThetaDataExistence_from_canLift27`

记 $\mathrm{AG}=\mathrm{modelAG}(\mathrm{genuineEtalePi1Theory}\ \mathrm{canLift27})$。定理取曲线提供者 $P$、紧致有界集 $K$、次数界 $d$、实参数 $TK$ 与循环子群界 `CF : CurveFactsProp P K d TK`、`hN : NorthcottHyp`，以及 $\mathrm{AG}$ 上的缓和几何 $\mathrm{TG}$ 与 `anab : AnabelianExistence AG TG`。若所选曲线的 $j$ 避开例外值，去点曲线的核心定理与去点和符号商的基变换恒等式给出普遍核心条件。对提供者给出的 Legendre 曲线，每个例外 $j$ 的纤维都是有限集。这就为给定的 $P,K,d$ 提供 `CoreFinitenessHyp P K d AG`。定理把此证明传给 `pointThetaDataExistence_from_source`，并在结论中用 `legendreHeight P K` 和 `twoAdicBound P K` 构造同一个 `CI`。 [基变换](../../../../Solutions/Source_TripodCoreGeometry.lean#L38) · [例外集有限性](../../../../Solutions/Source_TripodCoreFiniteness.lean#L62) · [模型上的核心有限性](../../../../Solutions/Source_TripodCoreModel.lean#L71) · [端点定理](../../../../Solutions/Source_TripodP7FromCanLift.lean#L17)

记 $T=\mathrm{tripodTheory}$ 和 $I=\mathrm{CI.toCorollary22Inputs}$。结论适用于每个三脚架点 $x$，其中 $h_x$ 证明 $x\inT.\mathrm{cbsSet}(K)\cap T.\mathrm{ptLE}(T.\mathrm{tripod},d)$，且 $x$ 在 $I.\mathrm{excCore}$ 之外。对这样的点，取满足下列条件的任意素数 $\ell\ge7$。记 $L=I.\mathrm{localData}(x,h_x)$。$L.\mathrm{bad}$ 由乘法约化的有限处组成，对其中每个 $w$，$L.\mathrm{hv}(w)$ 是 Tate 参数的整数阶。 [量化条件](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Corollary22.lean#L112)

- P2 要求每个 $w\in L.\mathrm{bad}$ 都满足 $\ell\nmid L.\mathrm{hv}(w)$。
- P3 要求每个剩余特征 $L.\mathrm{p}(w)=\ell$ 的 $w\in L.\mathrm{bad}$ 都满足 $L.\mathrm{hv}(w)<\sqrt{I.\mathrm{h}(x)}$，其中 Tate 阶数视作实数。
- P5 要求存在 $w\in L.\mathrm{bad}$ 满足 $L.\mathrm{p}(w)\notin\{2,\ell\}$。
- P6 是 `I.SL2Image x ℓ`，要求对每个成员资格证明和素性证明，模 $\ell$ 像均包含 $\mathrm{SL}_2(\mathbb Z/\ell\mathbb Z)$。 [像条件](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean#L154)

结论给出变体数据 $X$ 和其上的不变量 $\mathrm{inv}$。`IsSourceP7Variant CI anab` 记录了从逐点 Θ 数据及全部 $2$-挠点均为有理点的见证得到 $X$ 的构造，其中局部 Θ 数据加入了指定的剩余特征。塔算术给出 `Theorem110Certificate inv` 和 `Nonempty inv.LocalEstimate`。其余结论为

$$
\begin{gathered}
X.\ell=\ell,\qquad X.\mathrm{dmod}\le d,\qquad
X.\mathrm{qPilot.logQ}=L.\mathrm{heightOther}(2,\ell),\\
T.\mathrm{logDiff}(T.\mathrm{tripod},x)=\mathrm{inv.logDtpd},\qquad
\mathrm{inv.logFtpd}\leT.\mathrm{logCond}(T.\mathrm{tripod},x)\le\mathrm{inv.logFtpd}+\log(2\ell).
\end{gathered}
$$

其中 $X.\mathrm{dmod}$ 是模域在 $\mathbb Q$ 上的次数，$\mathrm{inv.logDtpd}$ 和 $\mathrm{inv.logFtpd}$ 是变体所用的归一化不同理想与导子对数次数。iut 参考使用仓库中版本 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8` 的副本。 [变体谓词](../../../../Solutions/Source_TripodP7.lean#L27) · [见证与界](../../../../Solutions/Source_TripodP7.lean#L95) · [iut 的 P7 构造](../../../../../refer/iut/Iut/Tripod/Main.lean#L86)

## 日本語

### `normalizationHasCore_iff_of_cover`

標数零の体 $k$ 上のモデル軌道曲線 $X,Y,C$ と被覆 $c\colon X\to Y$ をとる。それぞれの正規化表示を $A_X,A_Y,A_C$ とする。この定理は、$A_C$ が $A_X$ のコアであることと、$A_Y$ のコアであることが同値だと述べる。アフィン表示 $A,W$ に対し、`LocBar A W` は両者が共通の有限エタール被覆を持つことを表す。$A$ のコアはこのクラスに属し、クラスの各対象からコアへの有限エタール被覆はただ一つ存在する。 [定義](../../../../Solutions/Source_ReferenceIutCanLiftPresentation.lean#L22) · [定理](../../../../Solutions/Source_ReferenceIutGenuineCore.lean#L73) · [Pi1 の参照箇所](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Core.lean#L125)

被覆 $c$ のデータにより、$X,Y$ の基礎にある楕円曲線は同じである。両方の正規化の関数体は、$x$ 座標の有理関数体の一つの代数閉包に入る。正規化表示の間に誘導される被覆の環準同型は、$Y$ の関数体から $X$ の関数体への包含で定まる。任意の被覆 $V\to A_Y$ に対し、$V$ の関数体を同じ代数閉包に埋め込み、$X$ の関数体との合成体で正規化する。$Y$ の表示の閉点 $v$ の上にある閉点 $w$ に、新しい重複度 $m_Y(v)/e(w\mid v)$ を与える。合成体における分岐指数の整除性と拡大の塔での分岐指数の積公式により、二つの射影は被覆の条件を満たす。 [環準同型](../../../../Solutions/Source_ReferenceIutGenuineNormalizationCover.lean#L148) · [重複度](../../../../Solutions/Source_ReferenceIutCanLiftSubfieldPullback.lean#L33) · [共通被覆](../../../../Solutions/Source_ReferenceIutCanLiftPresentationPullback.lean#L85) · [Pi1 の参照箇所](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Pullback.lean#L398)

$A_X,W$ の共通被覆は、被覆を合成すると $A_Y$ も覆う。$A_Y,W$ の共通被覆 $V$ があれば、合成体の構成から $A_X,V$ の共通被覆が得られ、それは $W$ も覆う。よって二つの `LocBar` クラスは一致し、そのクラスの終対象であるという条件は双方向に移る。 [コアの終対象性](../../../../Solutions/Source_ReferenceIutGenuineCore.lean#L20) · [正規化表示への適用](../../../../Solutions/Source_ReferenceIutGenuineCore.lean#L52)

### `genuineEtalePi1Theory`

`h27 : CanLift27.{u}` から `EtalePi1Theory.{u}` を構成する。標数零では、正規化データの安定化群を閉な惰性核で割った副有限群をとる。各被覆が誘導する群準同型は連続な開埋め込みである。正標数では自明群と恒等準同型を用いる。コア関係 `normalizationHasCore` は標数零の証明を含む。被覆に関する不変性を `normalizationHasCore_iff_of_cover` が与える。 [群と被覆の写像](../../../../Solutions/Source_ReferenceIutGenuinePi1.lean#L58) · [コア関係](../../../../Solutions/Source_ReferenceIutCanLiftPresentation.lean#L118) · [理論](../../../../Solutions/Source_ReferenceIutGenuineCore.lean#L80) · [iut の参照箇所](../../../../../refer/iut/Iut/Anabelian/GenuineEtale.lean#L111)

四つの有理数の例外 $j$ 値は $0$、$1728$、$488095744/125$、$1556068/81$ である。標数零の体上の Weierstrass 楕円曲線の $j$ がこれらの値を避けるとき、$h_{27}$ により、一点を除いた曲線の符号対合による商がそのコアとなる。引数を取らない `canLift27 : CanLift27.{0}` は `canLift27Complex` から Lefschetz 降下で得られる。複素数体の場合の証明は、Fricke 標準形のトレースの平方の整性と、四つの Takeuchi モデル曲線について証明済みの一意化を用いる。可公度化群が稠密な場合、整性の証明はまず有理性を示し、次に各素数 $p$ でトレースの平方の $p$ 進ノルムが一以下であることを示す。 [例外値とコア定理](../../../../Solutions/Source_ReferenceIutCanLiftPresentation.lean#L104) · [トレースの整性](../../../../Solutions/Source_ReferenceIutCanLiftFinal.lean#L26) · [複素数体の場合](../../../../Solutions/Source_ReferenceIutCanLiftComplexFromFricke.lean#L15) · [Lefschetz 降下](../../../../Solutions/Source_ReferenceIutCanLiftLefschetz.lean#L16) · [命題 2.7](../../../../Solutions/Source_ReferenceIutCanLiftProp27.lean#L8)

### `pointThetaDataExistence_from_canLift27`

$\mathrm{AG}=\mathrm{modelAG}(\mathrm{genuineEtalePi1Theory}\ \mathrm{canLift27})$ とおく。定理への入力は、曲線の供給者 $P$、コンパクト有界な集合 $K$、次数の上界 $d$、実パラメータ $TK$ と巡回部分群に関する評価 `CF : CurveFactsProp P K d TK`、`hN : NorthcottHyp`、および $\mathrm{AG}$ 上の緩和幾何学 $\mathrm{TG}$ と `anab : AnabelianExistence AG TG` である。選んだ曲線の $j$ が例外値を避けるとき、一点を除いた曲線のコア定理と、一点除去および符号対合による商についての底変換の等式から、普遍的なコア条件を得る。供給される Legendre 曲線では各例外 $j$ のファイバーは有限である。これにより、与えた $P,K,d$ に対する `CoreFinitenessHyp P K d AG` が得られる。定理はこの証明を `pointThetaDataExistence_from_source` に渡し、結論では `legendreHeight P K` と `twoAdicBound P K` を使って同じ `CI` を構成する。 [底変換](../../../../Solutions/Source_TripodCoreGeometry.lean#L38) · [例外集合の有限性](../../../../Solutions/Source_TripodCoreFiniteness.lean#L62) · [モデルのコアの有限性](../../../../Solutions/Source_TripodCoreModel.lean#L71) · [定理](../../../../Solutions/Source_TripodP7FromCanLift.lean#L17)

$T=\mathrm{tripodTheory}$、$I=\mathrm{CI.toCorollary22Inputs}$ とする。結論は、$x\inT.\mathrm{cbsSet}(K)\cap T.\mathrm{ptLE}(T.\mathrm{tripod},d)$ の証明 $h_x$ を持ち、$I.\mathrm{excCore}$ の外にある各三脚の点 $x$ に適用される。その点について、次の条件を満たす任意の素数 $\ell\ge7$ をとる。$L=I.\mathrm{localData}(x,h_x)$ とおく。$L.\mathrm{bad}$ は乗法的還元を持つ有限素点からなる。各素点 $w$ において $L.\mathrm{hv}(w)$ は Tate パラメータの整数位数である。 [量化条件](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Corollary22.lean#L112)

- P2 は、各 $w\in L.\mathrm{bad}$ で $\ell\nmid L.\mathrm{hv}(w)$ を要求する。
- P3 は、剰余標数 $L.\mathrm{p}(w)=\ell$ の各 $w\in L.\mathrm{bad}$ で $L.\mathrm{hv}(w)<\sqrt{I.\mathrm{h}(x)}$ を要求する。ここで Tate の位数は実数として扱う。
- P5 は、$L.\mathrm{p}(w)\notin\{2,\ell\}$ を満たす $w\in L.\mathrm{bad}$ の存在を要求する。
- P6 は `I.SL2Image x ℓ` である。所属の証明と素数性の証明の各組に対し、mod $\ell$ 表現の像が $\mathrm{SL}_2(\mathbb Z/\ell\mathbb Z)$ を含むことを要求する。 [像の条件](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_CurveInputs.lean#L154)

結論は変種データ $X$ とその不変量 $\mathrm{inv}$ を与える。`IsSourceP7Variant CI anab` は、点ごとの Θ データと すべての $2$-ねじれ点が有理であることの証明から $X$ を構成することを記録する。この構成では、局所 Θ データに指定の剰余標数を加える。体の塔の算術から `Theorem110Certificate inv` と `Nonempty inv.LocalEstimate`を得る。残りの結論は次の通りである。

$$
\begin{gathered}
X.\ell=\ell,\qquad X.\mathrm{dmod}\le d,\qquad
X.\mathrm{qPilot.logQ}=L.\mathrm{heightOther}(2,\ell),\\
T.\mathrm{logDiff}(T.\mathrm{tripod},x)=\mathrm{inv.logDtpd},\qquad
\mathrm{inv.logFtpd}\leT.\mathrm{logCond}(T.\mathrm{tripod},x)\le\mathrm{inv.logFtpd}+\log(2\ell).
\end{gathered}
$$

ここで $X.\mathrm{dmod}$ はモジュライ体の $\mathbb Q$ 上の次数である。$\mathrm{inv.logDtpd}$ と $\mathrm{inv.logFtpd}$ は、この変種で用いる正規化された相異と導手の対数次数である。iut の参照先には、リポジトリに収録された改訂 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8` の写しを用いる。 [変種の述語](../../../../Solutions/Source_TripodP7.lean#L27) · [証拠と評価](../../../../Solutions/Source_TripodP7.lean#L95) · [iut の P7 構成](../../../../../refer/iut/Iut/Tripod/Main.lean#L86)
