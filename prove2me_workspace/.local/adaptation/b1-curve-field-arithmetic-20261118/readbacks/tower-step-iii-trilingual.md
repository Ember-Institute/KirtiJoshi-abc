# Step (iii) and the normalized different

## `sum_log_distinguished_le`

### Parameters

**English.** Let `F : Type u` be a number field and `E : WeierstrassCurve F` satisfy `[E.IsElliptic]`. Let `Fbar : Type u` be a field with an `F`-algebra structure. Write `M = ↥(fieldOfModuli F E)` and `T = ↥(tripodalFieldOf F E)`. Take `VBad : Set (FinitePlace M)` and `Pr : AdmissiblePrimeData F E Fbar VBad`. Put `K = ↥Pr.torsionField` and `ℓ = Pr.ℓ`, and assume `[NumberField K]` and `[IsGalois M T]`. The named parameters `F`, `E`, `Fbar`, `VBad`, and `Pr` are implicit. The field, number-field, algebra, ellipticity, and Galois assumptions are typeclass parameters.

**中文。** 设 `F : Type u` 为数域，`E : WeierstrassCurve F` 带有 `[E.IsElliptic]` 实例，`Fbar : Type u` 为带有 `F`-代数结构的域。记 `M = ↥(fieldOfModuli F E)`、`T = ↥(tripodalFieldOf F E)`。取 `VBad : Set (FinitePlace M)` 与 `Pr : AdmissiblePrimeData F E Fbar VBad`。令 `K = ↥Pr.torsionField`、`ℓ = Pr.ℓ`，并假设 `[NumberField K]` 和 `[IsGalois M T]`。`F`、`E`、`Fbar`、`VBad` 和 `Pr` 均为隐式参数。域、数域、代数、椭圆性和伽罗瓦性通过类型类实例传入。

**日本語。** `F : Type u` を数体とし、`E : WeierstrassCurve F` は `[E.IsElliptic]` を満たすとする。`Fbar : Type u` は `F`-代数構造を持つ体とする。`M = ↥(fieldOfModuli F E)`、`T = ↥(tripodalFieldOf F E)` と書き、`VBad : Set (FinitePlace M)` と `Pr : AdmissiblePrimeData F E Fbar VBad` を取る。`K = ↥Pr.torsionField`、`ℓ = Pr.ℓ` とし、`[NumberField K]` と `[IsGalois M T]` を仮定する。`F`、`E`、`Fbar`、`VBad`、`Pr` は暗黙の引数であり、体、数体、代数、楕円性、ガロア性は型クラスのインスタンスとして与えられる。

### Hypotheses and bound

**English.** Assume `H : TowerLocalFacts E VBad Pr`, `he2 : RelRamIdxModLeTwo E VBad`, and `hfin : (badPlacesOver F E VBad).Finite`. Thus `he2` bounds the relative ramification index by 2 for each finite place of `T` lying over a member of `VBad`. The set in `hfin` consists of the finite places of `F` lying over a member of `VBad`. For a given `S : Finset ℕ`, assume `hS` gives, for every `p ∈ S`, at least one of the following.

1. `p ∈ ({2, 3, 5, ℓ} : Finset ℕ)`.
2. There is a finite place `w ∈ badPlacesOver F E VBad` with `residueChar w = p`.
3. There is a finite place `v : FinitePlace K` with `residueChar v = p` and `ramIdx K v ≠ 1`.

Then the real inequality is

```lean
∑ p ∈ S, Real.log p ≤
  2 * Module.finrank ℚ M * (logDifferentDeg T + logConductorDegOf F E VBad)
    + 5 + Real.log ℓ
```

**中文。** 假设 `H : TowerLocalFacts E VBad Pr`、`he2 : RelRamIdxModLeTwo E VBad` 和 `hfin : (badPlacesOver F E VBad).Finite`。`he2` 断言，`T` 的任何有限位只要位于某个 `VBad` 成员上方，其相对分歧指数就不超过 2。`hfin` 中的集合由 `F` 的有限位组成，这些有限位位于某个 `VBad` 成员上方。给定 `S : Finset ℕ`，假设 `hS` 对每个 `p ∈ S` 给出以下至少一种情形。

1. `p ∈ ({2, 3, 5, ℓ} : Finset ℕ)`。
2. 存在有限位 `w ∈ badPlacesOver F E VBad`，使 `residueChar w = p`。
3. 存在有限位 `v : FinitePlace K`，使 `residueChar v = p` 且 `ramIdx K v ≠ 1`。

于是 `S` 中各元素的实对数之和至多为 `2 * Module.finrank ℚ M * (logDifferentDeg T + logConductorDegOf F E VBad) + 5 + Real.log ℓ`。

**日本語。** `H : TowerLocalFacts E VBad Pr`、`he2 : RelRamIdxModLeTwo E VBad`、`hfin : (badPlacesOver F E VBad).Finite` を仮定する。`he2` は、`VBad` の元の上にある `T` の任意の有限素点で相対分岐指数が 2 以下であることを表す。`hfin` に現れる集合は、`VBad` のいずれかの元の上にある `F` の有限素点からなる。`S : Finset ℕ` を与え、任意の `p ∈ S` に対し `hS` により次のうち少なくとも一つが成立すると仮定する。

1. `p ∈ ({2, 3, 5, ℓ} : Finset ℕ)`。
2. `residueChar w = p` を満たす有限素点 `w ∈ badPlacesOver F E VBad` が存在する。
3. `residueChar v = p` かつ `ramIdx K v ≠ 1` を満たす有限素点 `v : FinitePlace K` が存在する。

このとき、`S` の各元の実対数の和は `2 * Module.finrank ℚ M * (logDifferentDeg T + logConductorDegOf F E VBad) + 5 + Real.log ℓ` 以下である。

### The tripodal contributions

**English.** The proof bounds the part in `{2, 3, 5, ℓ}` by `5 + Real.log ℓ`. Among the remaining elements, those that occur as a residue characteristic in `VBad` enter the conductor estimate. For each other element, the proof takes a witness `v` in `K` from `hS`. Write `uₜ = placeTpd F E Pr.torsionField v` for its lower place in `T`. The predicate `¬ IsBadTpdOf F E VBad uₜ` holds, since a bad place above `uₜ` would give a member of `VBad` with the same residue characteristic. These are the places to which the proof applies `H.relRamIdx_eq_one`. Since that relative index is 1, the absolute index at the lower place equals `ramIdx K v` and differs from 1. These elements enter the different estimate for `T`. The conductor is the sum of the logarithmic ideal norms over finite places of `T` that lie below a member of `badPlacesOver F E VBad`, divided by `Module.finrank ℚ T`.

**中文。** 证明先把 `{2, 3, 5, ℓ}` 内的部分限制在 `5 + Real.log ℓ` 以内。余下元素中，在 `VBad` 中作为剩余特征出现的元素由导子估计处理。对其他每个元素，证明从 `hS` 中取出 `K` 中的见证 `v`。记其在 `T` 中的下方有限位为 `uₜ = placeTpd F E Pr.torsionField v`。由于位于 `uₜ` 上方的坏位会给出一个剩余特征相同的 `VBad` 成员，故有 `¬ IsBadTpdOf F E VBad uₜ`。在这些有限位上应用 `H.relRamIdx_eq_one`。相对分歧指数为 1，故下方有限位的绝对分歧指数等于 `ramIdx K v`，且不等于 1。这些元素由 `T` 的不同理想估计处理。导子项对 `T` 中位于某个 `badPlacesOver F E VBad` 成员下方的有限位求理想范数的对数之和，再除以 `Module.finrank ℚ T`。

**日本語。** 証明は、`{2, 3, 5, ℓ}` に属する部分を `5 + Real.log ℓ` で上から評価する。残りのうち、`VBad` の剰余標数として現れる元には導手の評価を用いる。それ以外の各元について、`hS` による `K` の有限素点 `v` を取る。その下にある `T` の有限素点を `uₜ = placeTpd F E Pr.torsionField v` とする。`uₜ` の上に悪い有限素点があれば同じ剰余標数を持つ `VBad` の元が得られるので、`¬ IsBadTpdOf F E VBad uₜ` が成り立つ。このような有限素点で `H.relRamIdx_eq_one` を用いる。相対分岐指数が 1 なので、その下の素点の絶対分岐指数は `ramIdx K v` に等しく、1 と異なる。これらの元には `T` のディファレントの評価を用いる。導手の項は、`badPlacesOver F E VBad` の元の下にある `T` の有限素点についてイデアルノルムの対数を足し、`Module.finrank ℚ T` で割ったものである。

[Step III](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerStepIII.lean:324) · [Tripodal invariant definitions](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean:24)

## `LocalTheory.sum_logDK_eq` and `ThetaLocalData.sum_dst_logDK_eq`

**English.** For any `K : Type u` with `[Field K]` and `[NumberField K]`, take `LT : LocalTheory.{u, v} K`. The finite set `LT.ramifiedChars` is the image under `residueChar` of the finite places `w` with `ramIdx K w ≠ 1`. For a natural number `p`, `LT.logDK p` is zero when `p` is composite, 0, or 1. When `p` is prime, it is the sum over the finite places `w` of `K` with `residueChar w = p` of `placeWeight K w * differentExponent K w * Real.log p`. The weight is `e_w * f_w / [K : ℚ]` and the normalized exponent is `ordDifferent K w / e_w`, both in `ℝ`, where `e_w` and `f_w` are the absolute ramification index and residue degree. Their product with `Real.log p` equals `ordDifferent K w * Real.log (Ideal.absNorm w.maximalIdeal.asIdeal) / [K : ℚ]`. The value `ordDifferent K w` is the multiplicity of the prime ideal of `w` in `differentIdeal ℤ (𝓞 K)`.

For every `S : Finset ℕ` with `hS : LT.ramifiedChars ⊆ S`, the exact equality is

```lean
∑ p ∈ S, LT.logDK p = logDifferentDeg K
```

The definition is `logDifferentDeg K = Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K))) / Module.finrank ℚ K`. Every finite place with nonzero different multiplicity lies in the set of ramified finite places, by `LT.ordDifferent_eq_zero` for `ramIdx K w = 1`. Summing the local terms over that set and grouping them by `residueChar` gives the equality.

For implicit `AG : AnabelianGeometry.{u}`, `TG : TemperedGeometry AG`, `D : InitialThetaData AG TG`, and `LT : LocalTheory.{u, v} D.Kt`, the only explicit parameter of `ThetaLocalData.sum_dst_logDK_eq` is `TL : ThetaLocalData D LT`. It gives `∑ p ∈ TL.dst, LT.logDK p = logDifferentDeg D.Kt`, because `TL.dst` contains `LT.ramifiedChars`.

**中文。** 对任意带有 `[Field K]`、`[NumberField K]` 的 `K : Type u`，取 `LT : LocalTheory.{u, v} K`。有限集合 `LT.ramifiedChars` 是所有满足 `ramIdx K w ≠ 1` 的有限位 `w` 在 `residueChar` 下的像。对自然数 `p`，当 `p` 是合数、0 或 1 时，`LT.logDK p` 为零。当 `p` 是素数时，它对 `K` 中满足 `residueChar w = p` 的所有有限位 `w` 求和，求和项为 `placeWeight K w * differentExponent K w * Real.log p`。令 `e_w`、`f_w` 分别为绝对分歧指数和剩余次数，则权重为 `e_w * f_w / [K : ℚ]`，归一化指数为 `ordDifferent K w / e_w`，两式都在 `ℝ` 中计算。两者与 `Real.log p` 相乘等于 `ordDifferent K w * Real.log (Ideal.absNorm w.maximalIdeal.asIdeal) / [K : ℚ]`。`ordDifferent K w` 是 `w` 对应的素理想在 `differentIdeal ℤ (𝓞 K)` 中的重数。

对任意 `S : Finset ℕ`，若 `hS : LT.ramifiedChars ⊆ S`，则 `∑ p ∈ S, LT.logDK p = logDifferentDeg K`，其中 `logDifferentDeg K = Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K))) / Module.finrank ℚ K`。由 `LT.ordDifferent_eq_zero`，`ramIdx K w = 1` 时不同理想在 `w` 上的重数为零。因此所有重数非零的有限位都在分歧有限位的集合中，对该集合求和，再按 `residueChar` 分组即可得到等式。

对于隐式参数 `AG : AnabelianGeometry.{u}`、`TG : TemperedGeometry AG`、`D : InitialThetaData AG TG` 和 `LT : LocalTheory.{u, v} D.Kt`，`ThetaLocalData.sum_dst_logDK_eq` 的显式参数为 `TL : ThetaLocalData D LT`。由于 `TL.dst` 包含 `LT.ramifiedChars`，该定理给出 `∑ p ∈ TL.dst, LT.logDK p = logDifferentDeg D.Kt`。

**日本語。** 任意の `K : Type u` に `[Field K]` と `[NumberField K]` を仮定し、`LT : LocalTheory.{u, v} K` を取る。有限集合 `LT.ramifiedChars` は、`ramIdx K w ≠ 1` を満たす有限素点 `w` の `residueChar` による像である。自然数 `p` が合成数、0、または 1 のとき、`LT.logDK p` は 0 である。`p` が素数のときは、`residueChar w = p` を満たすすべての `K` の有限素点 `w` にわたる `placeWeight K w * differentExponent K w * Real.log p` の和である。`e_w` と `f_w` をそれぞれ絶対分岐指数と剰余次数とすると、重みは `e_w * f_w / [K : ℚ]`、正規化した指数は `ordDifferent K w / e_w` であり、どちらも `ℝ` 上で計算する。これらと `Real.log p` の積は `ordDifferent K w * Real.log (Ideal.absNorm w.maximalIdeal.asIdeal) / [K : ℚ]` に等しい。`ordDifferent K w` は `differentIdeal ℤ (𝓞 K)` における `w` の素イデアルの重複度である。

任意の `S : Finset ℕ` に対し、`hS : LT.ramifiedChars ⊆ S` ならば `∑ p ∈ S, LT.logDK p = logDifferentDeg K` である。ここで `logDifferentDeg K = Real.log (Ideal.absNorm (differentIdeal ℤ (𝓞 K))) / Module.finrank ℚ K` である。`LT.ordDifferent_eq_zero` によると、`ramIdx K w = 1` ならば、`w` におけるディファレントの重複度は 0 である。したがって、重複度が 0 でない有限素点はすべて分岐する有限素点の集合に属する。この集合上の和を `residueChar` ごとにまとめると、等式が得られる。

暗黙の引数を `AG : AnabelianGeometry.{u}`、`TG : TemperedGeometry AG`、`D : InitialThetaData AG TG`、`LT : LocalTheory.{u, v} D.Kt` とすると、`ThetaLocalData.sum_dst_logDK_eq` の明示的な引数は `TL : ThetaLocalData D LT` である。`TL.dst` が `LT.ramifiedChars` を含むので、この定理は `∑ p ∈ TL.dst, LT.logDK p = logDifferentDeg D.Kt` を与える。

[Normalized different equality](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteDifferentDegree.lean:109) · [Different contribution on the distinguished set](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteDifferentDegree.lean:126) · [Local contribution definition](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:29)

## `ThetaLocalData.step_iii_of_localFacts`

**English.** For the same implicit `AG`, `TG`, `D`, and `LT`, take `TL : ThetaLocalData D LT`. The field `D.Kt` has type `Type u` and the tensor types of `LT` lie in `Type v`. The underlying number-field and ellipticity instances, including `[NumberField ↥D.prime.torsionField]`, come from `D`. Assume `H : TowerLocalFacts D.E D.VBad D.prime`, `he2 : RelRamIdxModLeTwo D.E D.VBad`, `[IsGalois ↥(fieldOfModuli D.F D.E) ↥D.tripodalField]`, and `hfin : (badPlacesOver D.F D.E D.VBad).Finite`. Also assume `hbad : ∀ p ∈ TL.badChars, ∃ w ∈ badPlacesOver D.F D.E D.VBad, residueChar w = p`. The conclusion is

```lean
∑ p ∈ TL.dst, Real.log p ≤
  2 * D.dmod * (logDifferentDeg ↥D.tripodalField + D.logConductorDeg)
    + 5 + Real.log D.ℓ
```

The proof applies `sum_log_distinguished_le` with `Pr = D.prime`, `S = TL.dst`, and `TL.dst = {2, 3, 5, D.ℓ} ∪ TL.badChars ∪ LT.ramifiedChars`. The middle part supplies witnesses via `hbad`. The last part supplies ramified finite places through `LT.ramifiedChars`. Those places are in `D.Kt = ↥D.prime.torsionField`, the same torsion field used by `H` and the normalized different equality. The abbreviations on the right are `D.dmod = Module.finrank ℚ ↥(fieldOfModuli D.F D.E)`, `D.tripodalField = tripodalFieldOf D.F D.E`, `D.logConductorDeg = logConductorDegOf D.F D.E D.VBad`, and `D.ℓ = D.prime.ℓ`.

**中文。** 对相同的隐式参数 `AG`、`TG`、`D` 和 `LT`，取 `TL : ThetaLocalData D LT`。数域 `D.Kt` 的类型为 `Type u`，`LT` 的张量类型在 `Type v` 中。所用的数域和椭圆性实例由 `D` 提供，其中包括 `[NumberField ↥D.prime.torsionField]`。假设 `H : TowerLocalFacts D.E D.VBad D.prime`、`he2 : RelRamIdxModLeTwo D.E D.VBad`、`[IsGalois ↥(fieldOfModuli D.F D.E) ↥D.tripodalField]` 和 `hfin : (badPlacesOver D.F D.E D.VBad).Finite`。另外假设 `hbad : ∀ p ∈ TL.badChars, ∃ w ∈ badPlacesOver D.F D.E D.VBad, residueChar w = p`。结论是 `∑ p ∈ TL.dst, Real.log p ≤ 2 * D.dmod * (logDifferentDeg ↥D.tripodalField + D.logConductorDeg) + 5 + Real.log D.ℓ`。

证明以 `Pr = D.prime` 和 `S = TL.dst` 应用 `sum_log_distinguished_le`，其中 `TL.dst = {2, 3, 5, D.ℓ} ∪ TL.badChars ∪ LT.ramifiedChars`。中间一项的见证来自 `hbad`，最后一项通过 `LT.ramifiedChars` 给出分歧有限位。它们属于 `D.Kt = ↥D.prime.torsionField`，这也是 `H` 与归一化不同理想等式使用的扭点域。右侧的简写分别为 `D.dmod = Module.finrank ℚ ↥(fieldOfModuli D.F D.E)`、`D.tripodalField = tripodalFieldOf D.F D.E`、`D.logConductorDeg = logConductorDegOf D.F D.E D.VBad` 和 `D.ℓ = D.prime.ℓ`。

**日本語。** 同じ暗黙の引数 `AG`、`TG`、`D`、`LT` に対し、`TL : ThetaLocalData D LT` を取る。数体 `D.Kt` の型は `Type u` であり、`LT` のテンソルの型は `Type v` に属する。数体と楕円性のインスタンスは `D` が持ち、この中には `[NumberField ↥D.prime.torsionField]` が含まれる。`H : TowerLocalFacts D.E D.VBad D.prime`、`he2 : RelRamIdxModLeTwo D.E D.VBad`、`[IsGalois ↥(fieldOfModuli D.F D.E) ↥D.tripodalField]`、`hfin : (badPlacesOver D.F D.E D.VBad).Finite` を仮定する。さらに、`hbad : ∀ p ∈ TL.badChars, ∃ w ∈ badPlacesOver D.F D.E D.VBad, residueChar w = p` を仮定する。結論は `∑ p ∈ TL.dst, Real.log p ≤ 2 * D.dmod * (logDifferentDeg ↥D.tripodalField + D.logConductorDeg) + 5 + Real.log D.ℓ` である。

証明では `Pr = D.prime` と `S = TL.dst` を用いて `sum_log_distinguished_le` を適用する。ここで `TL.dst = {2, 3, 5, D.ℓ} ∪ TL.badChars ∪ LT.ramifiedChars` である。中央の項では `hbad` により有限素点の存在が従い、最後の項では `LT.ramifiedChars` から分岐する有限素点を得る。それらは `D.Kt = ↥D.prime.torsionField` に属し、`H` と正規化したディファレントの等式もこの同じねじれ点体を用いる。右辺の略記は `D.dmod = Module.finrank ℚ ↥(fieldOfModuli D.F D.E)`、`D.tripodalField = tripodalFieldOf D.F D.E`、`D.logConductorDeg = logConductorDegOf D.F D.E D.VBad`、`D.ℓ = D.prime.ℓ` である。

[Initial theta bridge](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerStepIIIForTheta.lean:26) · [Torsion field of the initial theta data](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteThetaRegion.lean:41) · [Instances carried by the initial theta data](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Basic.lean:158)
