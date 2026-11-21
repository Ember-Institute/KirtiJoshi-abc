# The model tempered fundamental group and P7 / 模型的缓和基群与 P7 / モデルの緩和基本群と P7

## English

### Étale comparison

Take a model orbicurve $X=(E,\ell,M,\pm)$ over a field $k$ of characteristic zero. Let $\Omega$ be the chosen algebraic closure of $k(E)$ and $x$ the $x$-coordinate of its generic point. The local Galois base identifies with $k(x)$. In $\operatorname{Aut}(\Omega/k(x))$, let $H$ and $H_L$ be the images of the model stabilizer and the unsigned model stabilizer. The subgroup $H_L$ is open and normal in $H$. [Base field](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/ReferenceIut/Iut/Anabelian/Genuine/GenericPoint.lean#L58) · [Galois data](../../../../Solutions/Source_ReferenceIutGenuineEtaleComparison.lean#L81)

Put $L=\Omega^{H_L}$ and let $R$ be the integral closure of $k[x]$ in $L$. The group $A=H/H_L$ acts on $R$. The map $R\hookrightarrow\Omega$ gives the geometric point of $[\operatorname{Spec} R/A]$. The inertia set $S$ consists of $\sigma\in H_L$ that act trivially modulo the maximal ideal of some valuation subring of $\Omega$ containing $k$ and $x$. The unsigned inertia generators equal the base inertia generators. Their closed normal closure in $H$ gives the kernel of the local inertia quotient. [Source presentation](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Anabelian/Genuine/Orbifold.lean#L230) · [Inertia generators](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/GenuineInertiaGenerators.lean#L78) · [Kernel comparison](../../../../Solutions/Source_ReferenceIutGenuineEtaleComparison.lean#L115)

The finite étale fiber functor takes an $A$-equivariant cover to its geometric fiber at $R\hookrightarrow\Omega$. The action of $H$ on these fibers factors through the profinite quotient. The pinned Pi1 comparison gives the local isomorphism of topological groups
$$
\operatorname{Aut}(F_{\mathrm{\acute{e}t}})\ \simeq_{\mathrm{top}}\ H/\overline{\langle\!\langle S\rangle\!\rangle_H}.
$$
The group on the right is the characteristic-zero value of `genuinePi1 X`. [Fiber comparison, SGA 1 V.8.2](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbifold/Comparison.lean#L155) · [Local comparison](../../../../Solutions/Source_ReferenceIutGenuineEtaleComparison.lean#L147)

### Tempered theory

For characteristic zero, `modelTemperedPresentation` uses $[\operatorname{Spec} R/A]$ and the preceding isomorphism. In positive characteristic it uses the pinned geometric orbifold. Its ring consists of functions regular away from the geometric points in $E[\ell]+M$. Its action comes from $P\mapsto\varepsilon P+m$ for $m\in M$ and the signs allowed by the model flag. The map from its étale group to `genuinePi1 X` sends each element to $1$. [Two branches](../../../../Solutions/Source_ReferenceIutGenuineTempered.lean#L27) · [Geometric orbifold](https://github.com/lana-agents/tempered-fundamental-groups/blob/2006651f52b70ea2fe3388238c7d9db14d21748f/TemperedFundamentalGroups/Orbicurve/Orbifold.lean#L11) · [Source branches](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Anabelian/Tempered.lean#L71)

The construction chooses a henselian discrete valuation ring of $k$ when one exists and the trivial valuation ring $k$ otherwise. It then chooses an extension of that valuation ring to the field of the geometric point. Finite étale covers give tempered covers whose fibers identify with their étale fibers. Restriction along this identification gives the continuous map from the tempered group to the étale group of the chosen presentation. `genuineTemperedPi1Theory h27` composes that map with the comparison for the selected branch. [Valuation](https://github.com/lana-agents/tempered-fundamental-groups/blob/2006651f52b70ea2fe3388238c7d9db14d21748f/TemperedFundamentalGroups/Setup/Valuation.lean#L65) · [Extension at the base point](https://github.com/lana-agents/tempered-fundamental-groups/blob/2006651f52b70ea2fe3388238c7d9db14d21748f/TemperedFundamentalGroups/Setup/Orbifold.lean#L55) · [Restriction of fiber automorphisms](https://github.com/lana-agents/tempered-fundamental-groups/blob/2006651f52b70ea2fe3388238c7d9db14d21748f/TemperedFundamentalGroups/Tempered/Comparison.lean#L160) · [Concrete theory](../../../../Solutions/Source_ReferenceIutGenuineTempered.lean#L39)

### P7 on the concrete theory

Take the curve providers $P$, a compactly bounded set $K$, a degree bound $d$, and a real parameter $TK$. The inputs include `CF : CurveFactsProp P K d TK` and `hN : NorthcottHyp`. The wrapper uses the proved `canLift27` to obtain both theories. Write `Pi1 := genuineEtalePi1Theory canLift27` and `T := genuineTemperedPi1Theory canLift27`. The tempered geometry is `modelTG Pi1 T` and its anabelian existence proof is `anabelianExistence Pi1 T`. The same `Pi1` supplies core finiteness for the curve inputs `CI`. [CanLift proof](../../../../Solutions/Source_ReferenceIutCanLiftProp27.lean#L12) · [Core finiteness](../../../../Solutions/Source_TripodCoreModel.lean#L71) · [Anabelian existence](../../../../Solutions/Source_ReferenceIutAnabelianExistence.lean#L112) · [Wrapper](../../../../Solutions/Source_TripodP7FromGenuineTempered.lean#L15)

The result is `ThetaDataExistence (IsSourceP7Variant CI (anabelianExistence Pi1 T)) CI.toCorollary22Inputs`. It applies to each point in the given domain outside `excCore` and to each prime $\ell\ge7$ satisfying P2, P3, P5, and P6. It supplies source variant data, Theorem 1.10 invariants and their certificate, and a local estimate. The witness has level $\ell$, degree of the field of moduli at most $d$, the specified equality for $\log Q$, and the logarithmic different and conductor comparisons. [P7 statement](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Corollary22.lean#L112) · [P7 conditions and bounds](genuine-etale-core-to-p7-trilingual.md) · [Pinned P7 construction](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/Main.lean#L86)

## 简体中文

### Étale 比较

取特征零域 $k$ 上的模型轨形曲线 $X=(E,\ell,M,\pm)$。记 $\Omega$ 为所选的 $k(E)$ 的代数闭包，$x$ 为泛点的 $x$ 坐标。本地 Galois 底域等于 $k(x)$。在 $\operatorname{Aut}(\Omega/k(x))$ 中，记模型稳定子及不带符号的模型稳定子的像为 $H$ 和 $H_L$。$H_L$ 在 $H$ 中是开正规子群。 [底域](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/ReferenceIut/Iut/Anabelian/Genuine/GenericPoint.lean#L58) · [Galois 数据](../../../../Solutions/Source_ReferenceIutGenuineEtaleComparison.lean#L81)

令 $L=\Omega^{H_L}$，取 $R$ 为 $k[x]$ 在 $L$ 中的整闭包。$A=H/H_L$ 作用在 $R$ 上。$R\hookrightarrow\Omega$ 给出 $[\operatorname{Spec} R/A]$ 的几何点。惯性集合 $S$ 由满足下列条件的 $\sigma\in H_L$ 组成：存在包含 $k$ 和 $x$ 的 $\Omega$ 的赋值子环，使得 $\sigma$ 模该子环的极大理想作用平凡。不带符号的惯性生成元与底空间的惯性生成元相同。它们在 $H$ 中生成的闭正规子群就是本地惯性商的核。 [来源表示](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Anabelian/Genuine/Orbifold.lean#L230) · [惯性生成元](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/GenuineInertiaGenerators.lean#L78) · [核的比较](../../../../Solutions/Source_ReferenceIutGenuineEtaleComparison.lean#L115)

有限 étale 纤维函子把 $A$-等变覆盖送到 $R\hookrightarrow\Omega$ 处的几何纤维。$H$ 在这些纤维上的作用经该预有限商分解。固定版本的 Pi1 比较定理给出本地使用的拓扑群同构
$$
\operatorname{Aut}(F_{\mathrm{\acute{e}t}})\ \simeq_{\mathrm{top}}\ H/\overline{\langle\!\langle S\rangle\!\rangle_H}.
$$
右侧是 `genuinePi1 X` 在特征零时的值。 [纤维比较，SGA 1 V.8.2](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbifold/Comparison.lean#L155) · [本地比较](../../../../Solutions/Source_ReferenceIutGenuineEtaleComparison.lean#L147)

### 缓和理论

在特征零时，`modelTemperedPresentation` 取 $[\operatorname{Spec} R/A]$ 与上述同构。在正特征时，它取固定版本的几何轨形表示。其环由在 $E[\ell]+M$ 的几何点之外正则的函数组成。群作用由 $P\mapsto\varepsilon P+m$ 给出，其中 $m\in M$，符号由模型的标志允许。该表示的 étale 基群到 `genuinePi1 X` 的映射把每个元素送到 $1$。 [两种特征的定义](../../../../Solutions/Source_ReferenceIutGenuineTempered.lean#L27) · [几何轨形表示](https://github.com/lana-agents/tempered-fundamental-groups/blob/2006651f52b70ea2fe3388238c7d9db14d21748f/TemperedFundamentalGroups/Orbicurve/Orbifold.lean#L11) · [源中的两种特征](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Anabelian/Tempered.lean#L71)

若 $k$ 有 Hensel 离散赋值环，构造就选取这样的一个环，否则取平凡赋值环 $k$。然后把该赋值环延拓到几何点所在的域。有限 étale 覆盖给出缓和覆盖，其纤维与 étale 纤维相同。沿该识别限制纤维函子的自同构，得到从缓和基群到所选表示的 étale 基群的连续映射。`genuineTemperedPi1Theory h27` 再把该映射与相应特征下的比较映射复合。 [赋值](https://github.com/lana-agents/tempered-fundamental-groups/blob/2006651f52b70ea2fe3388238c7d9db14d21748f/TemperedFundamentalGroups/Setup/Valuation.lean#L65) · [基点上的延拓](https://github.com/lana-agents/tempered-fundamental-groups/blob/2006651f52b70ea2fe3388238c7d9db14d21748f/TemperedFundamentalGroups/Setup/Orbifold.lean#L55) · [限制纤维函子自同构](https://github.com/lana-agents/tempered-fundamental-groups/blob/2006651f52b70ea2fe3388238c7d9db14d21748f/TemperedFundamentalGroups/Tempered/Comparison.lean#L160) · [具体理论](../../../../Solutions/Source_ReferenceIutGenuineTempered.lean#L39)

### 具体理论上的 P7

取曲线提供器 $P$、紧致有界子集 $K$、次数界 $d$ 与实参数 $TK$。输入包括 `CF : CurveFactsProp P K d TK` 和 `hN : NorthcottHyp`。包装定理用已证明的 `canLift27` 构造两种理论。记 `Pi1 := genuineEtalePi1Theory canLift27` 和 `T := genuineTemperedPi1Theory canLift27`。缓和几何为 `modelTG Pi1 T`，其远 Abel 存在性证明为 `anabelianExistence Pi1 T`。同一个 `Pi1` 为曲线输入 `CI` 给出核心有限性。 [CanLift 证明](../../../../Solutions/Source_ReferenceIutCanLiftProp27.lean#L12) · [核心有限性](../../../../Solutions/Source_TripodCoreModel.lean#L71) · [远 Abel 存在性](../../../../Solutions/Source_ReferenceIutAnabelianExistence.lean#L112) · [包装定理](../../../../Solutions/Source_TripodP7FromGenuineTempered.lean#L15)

结论为 `ThetaDataExistence (IsSourceP7Variant CI (anabelianExistence Pi1 T)) CI.toCorollary22Inputs`。它适用于所给区域中 `excCore` 之外的每个点，以及满足 P2、P3、P5、P6 的每个素数 $\ell\ge7$。它给出来源变体数据、定理 1.10 的不变量及其证书，以及局部估计。见证的层级为 $\ell$，模域次数至多为 $d$，并满足规定的 $\log Q$ 等式以及不同理想和导子的对数次数比较。 [P7 陈述](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Corollary22.lean#L112) · [P7 的条件与界](genuine-etale-core-to-p7-trilingual.md) · [固定版本的 P7 构造](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/Main.lean#L86)

## 日本語

### エタール比較

標数零の体 $k$ 上のモデル軌道曲線 $X=(E,\ell,M,\pm)$ を取る。$\Omega$ を $k(E)$ の選んだ代数閉包、$x$ を生成点の $x$ 座標とする。局所構成の Galois 基礎体は $k(x)$ に等しい。$\operatorname{Aut}(\Omega/k(x))$ におけるモデルの安定化群の像を $H$、符号を付けないモデルの安定化群の像を $H_L$ とする。$H_L$ は $H$ の開正規部分群である。 [基礎体](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/ReferenceIut/Iut/Anabelian/Genuine/GenericPoint.lean#L58) · [Galois データ](../../../../Solutions/Source_ReferenceIutGenuineEtaleComparison.lean#L81)

$L=\Omega^{H_L}$ とし、$R$ を $L$ における $k[x]$ の整閉包とする。$A=H/H_L$ は $R$ に作用する。$R\hookrightarrow\Omega$ は $[\operatorname{Spec} R/A]$ の幾何点を定める。惰性集合 $S$ は、$k$ と $x$ を含む $\Omega$ のある付値部分環の極大イデアルを法として自明に作用する $\sigma\in H_L$ からなる。符号を付けない被覆の惰性生成元は基底の惰性生成元と一致する。これらが $H$ で生成する閉正規部分群が局所構成の惰性商の核である。 [原典の表示](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Anabelian/Genuine/Orbifold.lean#L230) · [惰性生成元](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/GenuineInertiaGenerators.lean#L78) · [核の比較](../../../../Solutions/Source_ReferenceIutGenuineEtaleComparison.lean#L115)

有限エタール・ファイバー関手は $A$ 同変被覆を $R\hookrightarrow\Omega$ における幾何ファイバーに送る。これらのファイバーへの $H$ の作用は副有限商を経由する。固定版の Pi1 の比較定理から、局所構成で使う位相群の同型を得る。
$$
\operatorname{Aut}(F_{\mathrm{\acute{e}t}})\ \simeq_{\mathrm{top}}\ H/\overline{\langle\!\langle S\rangle\!\rangle_H}.
$$
右辺は標数零での `genuinePi1 X` の値である。 [ファイバー比較、SGA 1 V.8.2](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbifold/Comparison.lean#L155) · [局所構成の比較](../../../../Solutions/Source_ReferenceIutGenuineEtaleComparison.lean#L147)

### 緩和理論

標数零では、`modelTemperedPresentation` は $[\operatorname{Spec} R/A]$ と上の同型を用いる。正標数では、固定版の幾何的軌道曲線の表示を用いる。その環は $E[\ell]+M$ の幾何点の外で正則な関数からなる。群作用は $P\mapsto\varepsilon P+m$ で与えられ、$m\in M$ であり、符号はモデルのフラグで定まる。この表示のエタール基本群から `genuinePi1 X` への写像は各元を $1$ に送る。 [二つの標数の場合](../../../../Solutions/Source_ReferenceIutGenuineTempered.lean#L27) · [幾何的軌道曲線の表示](https://github.com/lana-agents/tempered-fundamental-groups/blob/2006651f52b70ea2fe3388238c7d9db14d21748f/TemperedFundamentalGroups/Orbicurve/Orbifold.lean#L11) · [原典の二つの場合](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Anabelian/Tempered.lean#L71)

$k$ が Hensel 離散付値環をもつときはそのような環を選び、それ以外の場合は自明な付値環 $k$ を取る。次にその付値環を幾何点の体へ延長する。有限エタール被覆から緩和被覆が得られ、そのファイバーはエタール・ファイバーと同一視される。この同一視に沿ってファイバー関手の自己同型を制限すると、緩和基本群から選んだ表示のエタール基本群への連続写像を得る。`genuineTemperedPi1Theory h27` はこの写像と標数に応じた比較写像を合成する。 [付値](https://github.com/lana-agents/tempered-fundamental-groups/blob/2006651f52b70ea2fe3388238c7d9db14d21748f/TemperedFundamentalGroups/Setup/Valuation.lean#L65) · [基点での延長](https://github.com/lana-agents/tempered-fundamental-groups/blob/2006651f52b70ea2fe3388238c7d9db14d21748f/TemperedFundamentalGroups/Setup/Orbifold.lean#L55) · [ファイバー関手の自己同型の制限](https://github.com/lana-agents/tempered-fundamental-groups/blob/2006651f52b70ea2fe3388238c7d9db14d21748f/TemperedFundamentalGroups/Tempered/Comparison.lean#L160) · [具体的な理論](../../../../Solutions/Source_ReferenceIutGenuineTempered.lean#L39)

### 具体的な理論上の P7

曲線の供給者 $P$、コンパクト有界集合 $K$、次数界 $d$、実パラメータ $TK$ を取る。入力に `CF : CurveFactsProp P K d TK` と `hN : NorthcottHyp` を含む。包装定理では証明済みの `canLift27` から二つの理論を得る。`Pi1 := genuineEtalePi1Theory canLift27` および `T := genuineTemperedPi1Theory canLift27` と置く。緩和幾何は `modelTG Pi1 T` であり、その遠アーベル的存在性の証明は `anabelianExistence Pi1 T` である。同じ `Pi1` が曲線入力 `CI` に対するコアの有限性を与える。 [CanLift の証明](../../../../Solutions/Source_ReferenceIutCanLiftProp27.lean#L12) · [コアの有限性](../../../../Solutions/Source_TripodCoreModel.lean#L71) · [遠アーベル的存在性](../../../../Solutions/Source_ReferenceIutAnabelianExistence.lean#L112) · [特化した定理](../../../../Solutions/Source_TripodP7FromGenuineTempered.lean#L15)

結論は `ThetaDataExistence (IsSourceP7Variant CI (anabelianExistence Pi1 T)) CI.toCorollary22Inputs` である。指定された領域内で `excCore` の外にある各点と、P2、P3、P5、P6 を満たす各素数 $\ell\ge7$ に適用できる。原典の変種データ、定理 1.10 の不変量とその証明書、および局所評価を与える。そのデータのレベルは $\ell$、モジュライ体の次数は $d$ 以下であり、指定された $\log Q$ の等式と不同イデアルおよび導手の対数次数の比較が成り立つ。 [P7 の主張](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Corollary22.lean#L112) · [P7 の条件と評価](genuine-etale-core-to-p7-trilingual.md) · [固定版の P7 の構成](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Tripod/Main.lean#L86)
