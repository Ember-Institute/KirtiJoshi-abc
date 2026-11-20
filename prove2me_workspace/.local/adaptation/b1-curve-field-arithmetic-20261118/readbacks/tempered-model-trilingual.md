# Tempered geometry on the orbicurve model

Upstream / 上游 / 上流 `lana-agents/iut@07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`

## English

Fix `Pi1 : EtalePi1Theory.{u}`. For each model orbicurve $X$ over a field $k$ in universe $u$, `TemperedPi1Theory Pi1` supplies a type $\Pi_X^{\mathrm{temp}}$, a group structure, and a topology. It also supplies a group homomorphism $\Pi_X^{\mathrm{temp}}\to\mathrm{Pi1.pi1}(X)$ and a proof of its continuity. `modelTG Pi1 T` uses these five fields from the given `T` to build `TemperedGeometry (modelAG Pi1)`. [Lean interface](../../../../Solutions/Source_ReferenceIutTemperedModel.lean#L24) · [Upstream interface](../../../../../refer/iut/Iut/Anabelian/Geometry.lean#L70) · [Upstream model](../../../../../refer/iut/Iut/Anabelian/Geometry.lean#L88)

For the local predicates, take $k$ complete with a rank-one valuation valued in `WithZero (Multiplicative ℤ)`. Let `S : TateStructure X.E`. The theta-root predicate requires that $\ell$ be prime, $X.\mathrm{level}=\ell$, $X.M=S.\mathrm{graphLine}(\ell)$, and $|X.M|=\ell$. The predicate applies to either value of the sign flag `X.pm`. [Lean model and predicate](../../../../Solutions/Source_ReferenceIutTemperedModel.lean#L45) · [Graph-line condition](../../../../Solutions/Source_TripodCoreModel.lean#L44) · [Upstream theta-root predicate](../../../../../refer/iut/Iut/Anabelian/Local.lean#L46)

If a level-torsion point $R$ satisfies `S.IsCanonical X.level R`, the definition `canonicalGraphCusp X S` selects such a point by classical choice. It projects $R$ with `X.toQ` and takes the cusp of that class. If there is no such point, it takes `X.cuspOf 0`. The model supplies this cusp and the theta-root predicate for each supplied `T`. The fixed upstream has a separate `temperedTheory` construction from integral models, which is one source of such an input on its own étale theory. [Lean cusp](../../../../Solutions/Source_ReferenceIutTemperedModel.lean#L36) · [Upstream cusp](../../../../../refer/iut/Iut/Anabelian/Local.lean#L56) · [Upstream tempered group construction](../../../../../refer/iut/Iut/Anabelian/Tempered.lean#L130)

## 中文

固定 `Pi1 : EtalePi1Theory.{u}`。对宇宙层级 $u$ 中任一域 $k$ 上的模型轨形曲线 $X$，`TemperedPi1Theory Pi1` 给出类型 $\Pi_X^{\mathrm{temp}}$、群结构和拓扑，并给出群同态 $\Pi_X^{\mathrm{temp}}\to\mathrm{Pi1.pi1}(X)$ 及其连续性。`modelTG Pi1 T` 从给定的 `T` 取这五个字段，构造 `TemperedGeometry (modelAG Pi1)`。 [Lean 接口](../../../../Solutions/Source_ReferenceIutTemperedModel.lean#L24) · [上游接口](../../../../../refer/iut/Iut/Anabelian/Geometry.lean#L70) · [上游模型](../../../../../refer/iut/Iut/Anabelian/Geometry.lean#L88)

对于局部谓词，取完备域 $k$，其秩一赋值取值于 `WithZero (Multiplicative ℤ)`。给定 `S : TateStructure X.E`，θ 根模型谓词要求 $\ell$ 为素数、$X.\mathrm{level}=\ell$、$X.M=S.\mathrm{graphLine}(\ell)$ 且 $|X.M|=\ell$。符号标志 `X.pm` 取任一值均适用该谓词。 [Lean 模型与谓词](../../../../Solutions/Source_ReferenceIutTemperedModel.lean#L45) · [图直线条件](../../../../Solutions/Source_TripodCoreModel.lean#L44) · [上游 θ 根模型谓词](../../../../../refer/iut/Iut/Anabelian/Local.lean#L46)

若存在满足 `S.IsCanonical X.level R` 的相应阶挠点 $R$，`canonicalGraphCusp X S` 通过经典选择取其中一点，用 `X.toQ` 取其商类，再取该类对应的尖点。若无这样的点，定义取 `X.cuspOf 0`。对于每个给定的 `T`，模型都给出此尖点及 θ 根模型谓词。固定上游另有从整模型构造的 `temperedTheory`，它在上游自身的 étale 理论上提供这类输入。 [Lean 尖点](../../../../Solutions/Source_ReferenceIutTemperedModel.lean#L36) · [上游尖点](../../../../../refer/iut/Iut/Anabelian/Local.lean#L56) · [上游缓和基本群构造](../../../../../refer/iut/Iut/Anabelian/Tempered.lean#L130)

## 日本語

`Pi1 : EtalePi1Theory.{u}` を固定する。宇宙レベル $u$ の体 $k$ 上の各モデル軌道曲線 $X$ に対し、`TemperedPi1Theory Pi1` は型 $\Pi_X^{\mathrm{temp}}$、群構造、位相を与える。さらに群準同型 $\Pi_X^{\mathrm{temp}}\to\mathrm{Pi1.pi1}(X)$ とその連続性を与える。`modelTG Pi1 T` は、与えられた `T` のこれら五つのフィールドを用いて `TemperedGeometry (modelAG Pi1)` を構成する。 [Lean のインターフェース](../../../../Solutions/Source_ReferenceIutTemperedModel.lean#L24) · [上流のインターフェース](../../../../../refer/iut/Iut/Anabelian/Geometry.lean#L70) · [上流のモデル](../../../../../refer/iut/Iut/Anabelian/Geometry.lean#L88)

局所述語では、`WithZero (Multiplicative ℤ)` に値を取る階数一の付値をもつ完備体 $k$ を用いる。`S : TateStructure X.E` を与えると、θ 根モデルの述語は、$\ell$ が素数であり、$X.\mathrm{level}=\ell$、$X.M=S.\mathrm{graphLine}(\ell)$、$|X.M|=\ell$ が成り立つことを要求する。符号フラグ `X.pm` のどちらの値にもこの述語が適用される。 [Lean のモデルと述語](../../../../Solutions/Source_ReferenceIutTemperedModel.lean#L45) · [グラフ直線の条件](../../../../Solutions/Source_TripodCoreModel.lean#L44) · [上流の θ 根モデルの述語](../../../../../refer/iut/Iut/Anabelian/Local.lean#L46)

`canonicalGraphCusp X S` は、`S.IsCanonical X.level R` を満たすレベルのねじれ点 $R$ が存在するとき、古典的選択によってその一つを選ぶ。`X.toQ` で商類を取り、その類のカスプを取る。そのような点がなければ `X.cuspOf 0` を取る。モデルは、与えられた各 `T` に対し、このカスプと θ 根モデルの述語を与える。固定した上流には整モデルからの `temperedTheory` の構成もあり、上流自身のエタール理論上でこの種の入力を与える。 [Lean のカスプ](../../../../Solutions/Source_ReferenceIutTemperedModel.lean#L36) · [上流のカスプ](../../../../../refer/iut/Iut/Anabelian/Local.lean#L56) · [上流の緩和基本群の構成](../../../../../refer/iut/Iut/Anabelian/Tempered.lean#L130)
