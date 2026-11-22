# Stable reduction of the Legendre curve over $F_\lambda$

## 简体中文

令 $\lambda=x.1$，其中 `x : Pt`。`curveOf x h3 h5` 接受几何三挠点和五挠点集合的有限性证明，取 `F := fieldOf' x.1`、`Fbar := Qbar` 和 `E := legendre (gen' x.1)`。实际定义域为

$$
F_\lambda=\mathbb Q\bigl(\lambda,\sqrt{-1},\sqrt{\lambda},
       \sqrt{1-\lambda},E_\lambda[3],E_\lambda[5]\bigr)
     \subseteq\overline{\mathbb Q}.
$$

式中的 $E_\lambda[3]$ 与 $E_\lambda[5]$ 表示添入相应挠点的仿射坐标。`HasStableReductionAt E w` 表示可在 $F_\lambda$ 上作变量变换，使所得模型在 $w$ 处完成域的赋值环上有好约化或乘法约化，即半稳定约化。 [定义域][field] · [实际曲线][curve] · [约化谓词][reduction]

### `independent_three_torsion_curveOf`

结论在实际 $F_\lambda$ 上给出两个仿射曲线点 $P,Q$，满足

$$
3P=3Q=0,\qquad P\ne0,\qquad Q\ne0,\qquad Q\ne P,\qquad Q\ne-P.
$$

在 $\overline{\mathbb Q}$ 上，`legendre_torsionBasis_three` 给出与 `Fin 2 → ZMod 3` 的加法同构。证明取 $(1,0)$ 与 $(0,1)$ 的原像。这两个几何点也被 $6$ 消去，因而由 `six_torsion_rational_curveOf` 提升为 $F_\lambda$ 上的点。基变换的单射性给出 $3P=3Q=0$，几何像的非零性与独立性给出其余条件。 [三挠点定理][torsion] · [几何基][basis] · [六挠点有理性][rationality]

### `hasStableReductionAt_legendre`

设 $F$ 为数域、$w$ 为有限位，$v_w$ 为乘法赋值。签名要求 `residueChar w ≠ 2`、$l\ne0$ 及 $s^2=l$（$s\in F$）。若 $v_w(l)\le1$，证明使用原模型 $E_l$。若 $v_w(l)>1$，变量变换 $x=lX,\ y=lsY$ 得到整参数模型 $E_{l^{-1}}$。对所得整参数 $t$，公式为

$$
\Delta(E_t)=16t^2(t-1)^2,\qquad c_4(E_t)=16(t^2-t+1).
$$

这里 $v_w(2)=1$。若 $t$ 与 $t-1$ 都是单位，判别式是单位，给出好约化。其余情形满足 $v_w(\Delta)<1$ 且 $v_w(c_4)=1$，给出乘法约化。实际曲线的 `stable_reduction_of_residueChar_ne_two` 使用 $F_\lambda$ 已有的 `sqrtLam x.1`。剩余特征 $3$ 属于这一分支。 [Legendre 模型][integral-legendre] · [坐标变换][coordinate-change] · [奇剩余特征定理][odd] · [实际曲线的特化][specialization]

### `hasStableReductionAt_of_three_torsion`

数域 $F$ 带 `DecidableEq F`。给定 $F$ 上的 Weierstrass 曲线 $E$ 及有限位 $w$，Raynaud 的 $n=3$ 情形要求 `residueChar w ≠ 3`，以及 $E$ 上满足上述六项条件的 $F$ 有理点 $P,Q$。由于 $Q$ 与 $P,-P$ 都不同，两点的横坐标相异。证明取 $w$ 的一致化元，利用 $v_w(3)=1$，把这两个点作为两个拐点处理。先取整模型，再用第一个拐点变换至标准形。第二个拐点的横坐标 $z$ 给出下式。

$$
y^2+Axy+By=x^3,\qquad
3z^3+A^2z^2+3ABz+3B^2=0,\qquad z\ne 0.
$$

标准形引理给出一个好模型或乘法模型，进而得到 `HasStableReductionAt E w`。 [Raynaud 定理][raynaud] · [两个拐点][flexes] · [标准形引理][normal-form] · [从模型到约化][model-to-reduction]

### `stable_reduction_curveOf`

给定 `x`、`h3`、`h5`，定理对每个 `w : FinitePlace (curveOf x h3 h5).F` 证明 `HasStableReductionAt (curveOf x h3 h5).E w`。若剩余特征为 $2$，证明从 `independent_three_torsion_curveOf` 取得 $F_\lambda$ 上的 $P,Q$，由 $2\ne3$ 应用 Raynaud 定理。每个奇剩余特征的有限位（包括 $3$ 上方的有限位）均由 Legendre 分支处理。 [逐处稳定约化][all-places]

## English

Let $\lambda=x.1$ for `x : Pt`. The definition `curveOf x h3 h5` takes finiteness proofs for the geometric $3$-torsion and $5$-torsion. It uses `F := fieldOf' x.1`, `Fbar := Qbar`, and `E := legendre (gen' x.1)`. The field of definition is

$$
F_\lambda=\mathbb Q\bigl(\lambda,\sqrt{-1},\sqrt{\lambda},
       \sqrt{1-\lambda},E_\lambda[3],E_\lambda[5]\bigr)
     \subseteq\overline{\mathbb Q}.
$$

Here $E_\lambda[3]$ and $E_\lambda[5]$ contribute their affine coordinates. The predicate `HasStableReductionAt E w` means good or multiplicative reduction over the valuation ring of the completion at $w$. The change of variables is over $F_\lambda$. Thus stable reduction here means semistable reduction. [Field of definition][field] · [Legendre curve][curve] · [Reduction predicate][reduction]

### `independent_three_torsion_curveOf`

The theorem gives points $P,Q$ on the affine curve over $F_\lambda$ with

$$
3P=3Q=0,\qquad P\ne0,\qquad Q\ne0,\qquad Q\ne P,\qquad Q\ne-P.
$$

Over $\overline{\mathbb Q}$, `legendre_torsionBasis_three` gives an additive isomorphism with `Fin 2 → ZMod 3`. The proof takes the inverse images of $(1,0)$ and $(0,1)$. Multiplication by $6$ also kills these points, so `six_torsion_rational_curveOf` gives preimages over $F_\lambda$. Injectivity of base change gives $3P=3Q=0$. The geometric images give the remaining nonzero and independence conditions. [Rational torsion points][torsion] · [Geometric basis][basis] · [Rationality of the $6$-torsion][rationality]

### `hasStableReductionAt_legendre`

Let $F$ be a number field and let $w$ be a finite place with multiplicative valuation $v_w$. The signature requires `residueChar w ≠ 2`, $l\ne 0$, and $s^2=l$ for $s\in F$. If $v_w(l)\le1$, the proof uses $E_l$. If $v_w(l)>1$, the change $x=lX,\ y=lsY$ gives $E_{l^{-1}}$ with an integral parameter. For the resulting integral parameter $t$, the formulas are

$$
\Delta(E_t)=16t^2(t-1)^2,\qquad c_4(E_t)=16(t^2-t+1).
$$

Here $v_w(2)=1$. If $t$ and $t-1$ are units, the discriminant is a unit and the reduction is good. The other cases give $v_w(\Delta)<1$ and $v_w(c_4)=1$, so the reduction is multiplicative. The specialization `stable_reduction_of_residueChar_ne_two` uses `sqrtLam x.1` in $F_\lambda$. This branch includes residue characteristic $3$. [Integral Legendre model][integral-legendre] · [Change of variables][coordinate-change] · [Odd residue characteristic][odd] · [Specialization to the curve][specialization]

### `hasStableReductionAt_of_three_torsion`

The number field $F$ has `DecidableEq F`. For a Weierstrass curve $E/F$ and a finite place $w$, Raynaud's $n=3$ criterion requires `residueChar w ≠ 3`. It takes $F$-rational points $P,Q$ with the six conditions above. The conditions $Q\ne P$ and $Q\ne -P$ give distinct $x$-coordinates. The proof takes a uniformizer at $w$ and uses $v_w(3)=1$. It chooses an integral model and uses the first flex to put it in normal form. The $x$-coordinate $z$ of the second flex gives the equation below.

$$
y^2+Axy+By=x^3,\qquad
3z^3+A^2z^2+3ABz+3B^2=0,\qquad z\ne 0.
$$

The normal form lemma supplies a good or multiplicative model, which gives `HasStableReductionAt E w`. [Raynaud criterion][raynaud] · [Two flexes][flexes] · [Normal form lemma][normal-form] · [Reduction from a stable model][model-to-reduction]

### `stable_reduction_curveOf`

Given `x`, `h3`, and `h5`, the theorem proves `HasStableReductionAt (curveOf x h3 h5).E w` for each `w : FinitePlace (curveOf x h3 h5).F`. If the residue characteristic is $2$, the proof obtains $P,Q$ over $F_\lambda$ and applies Raynaud's criterion using $2\ne3$. The Legendre branch handles every odd residue characteristic, including all places above $3$. [Stable reduction at every finite place][all-places]

## 日本語

`x : Pt` に対し、$\lambda=x.1$ とする。`curveOf x h3 h5` は幾何的 $3$ 捩れ点と $5$ 捩れ点の集合の有限性を仮定する。`F := fieldOf' x.1`、`Fbar := Qbar`、`E := legendre (gen' x.1)` を用いる。実際の定義体は

$$
F_\lambda=\mathbb Q\bigl(\lambda,\sqrt{-1},\sqrt{\lambda},
       \sqrt{1-\lambda},E_\lambda[3],E_\lambda[5]\bigr)
     \subseteq\overline{\mathbb Q}.
$$

ここで $E_\lambda[3]$ と $E_\lambda[5]$ は該当する捩れ点のアフィン座標を添加することを表す。`HasStableReductionAt E w` は $F_\lambda$ 上で変数変換したモデルが、$w$ での完備体の付値環上で良還元または乗法的還元を持つことを表す。ここでの安定還元は半安定還元である。 [定義体][field] · [Legendre 曲線][curve] · [還元の述語][reduction]

### `independent_three_torsion_curveOf`

定理は実際の $F_\lambda$ 上のアフィン曲線の点 $P,Q$ で、次を満たすものを与える。

$$
3P=3Q=0,\qquad P\ne0,\qquad Q\ne0,\qquad Q\ne P,\qquad Q\ne-P.
$$

$\overline{\mathbb Q}$ 上では `legendre_torsionBasis_three` が `Fin 2 → ZMod 3` との加法同型を与える。証明は $(1,0)$ と $(0,1)$ の逆像を取る。これらの点は $6$ 倍でも零になるため、`six_torsion_rational_curveOf` によって $F_\lambda$ 上の点に持ち上がる。基底変換の単射性から $3P=3Q=0$ を得る。残りの非零性と独立性は幾何的な像から従う。 [有理捩れ点][torsion] · [幾何的な基底][basis] · [$6$ 捩れ点の有理性][rationality]

### `hasStableReductionAt_legendre`

$F$ を数体、$w$ を有限素点とし、$v_w$ を乗法的付値とする。シグネチャの仮定は `residueChar w ≠ 2`、$l\ne0$、および $s\in F$ に対する $s^2=l$ である。$v_w(l)\le1$ のときは $E_l$ を用いる。$v_w(l)>1$ のときは変数変換 $x=lX,\ y=lsY$ により、整なパラメータを持つ $E_{l^{-1}}$ を得る。得られた整なパラメータ $t$ に対して次が成り立つ。

$$
\Delta(E_t)=16t^2(t-1)^2,\qquad c_4(E_t)=16(t^2-t+1).
$$

ここでは $v_w(2)=1$ である。$t$ と $t-1$ が単元なら判別式は単元であり、良還元となる。他の場合は $v_w(\Delta)<1$ かつ $v_w(c_4)=1$ となり、乗法的還元を得る。実際の曲線への特殊化 `stable_reduction_of_residueChar_ne_two` は、$F_\lambda$ に属する `sqrtLam x.1` を用いる。この分岐は剰余標数 $3$ を含む。 [整な Legendre モデル][integral-legendre] · [変数変換][coordinate-change] · [奇剰余標数の定理][odd] · [実際の曲線への特殊化][specialization]

### `hasStableReductionAt_of_three_torsion`

数体 $F$ は `DecidableEq F` を備える。Weierstrass 曲線 $E/F$ と有限素点 $w$ に対し、Raynaud の $n=3$ の判定基準は `residueChar w ≠ 3` と上の六条件を満たす $F$ 有理点 $P,Q$ を仮定する。$Q\ne P$ かつ $Q\ne -P$ なので、二点の $x$ 座標は相異なる。証明は $w$ の素元を取り、$v_w(3)=1$ を使う。整モデルを選び、第一の変曲点を使って標準形に移す。第二の変曲点の $x$ 座標 $z$ は次の式を満たす。

$$
y^2+Axy+By=x^3,\qquad
3z^3+A^2z^2+3ABz+3B^2=0,\qquad z\ne 0.
$$

標準形の補題が良モデルまたは乗法的モデルを与え、`HasStableReductionAt E w` が従う。 [Raynaud の判定基準][raynaud] · [二つの変曲点][flexes] · [標準形の補題][normal-form] · [安定モデルからの還元][model-to-reduction]

### `stable_reduction_curveOf`

`x`、`h3`、`h5` に対し、各 `w : FinitePlace (curveOf x h3 h5).F` で `HasStableReductionAt (curveOf x h3 h5).E w` が成り立つ。剰余標数 $2$ の分岐では、$F_\lambda$ 上の $P,Q$ を取り、$2\ne3$ を使って Raynaud の判定基準を適用する。奇剰余標数の分岐では、$3$ の上にあるすべての素点を含め、Legendre モデルの定理を適用する。 [すべての有限素点での安定還元][all-places]

## Lean 签名 · Lean signatures · Lean シグネチャ

```lean
theorem independent_three_torsion_curveOf (x : Pt) (h3 : TorsionFinite x.1 3)
    (h5 : TorsionFinite x.1 5) :
    ∃ P Q : (curveOf x h3 h5).E.toAffine.Point,
      3 • P = 0 ∧ 3 • Q = 0 ∧ P ≠ 0 ∧ Q ≠ 0 ∧ Q ≠ P ∧ Q ≠ -P
```

[Lean][torsion]

```lean
variable {F : Type*} [Field F] [NumberField F] (w : FinitePlace F)

theorem hasStableReductionAt_legendre (hw : residueChar w ≠ 2) {l : F} (h0 : l ≠ 0) {s : F}
    (hs : s ^ 2 = l) : HasStableReductionAt (legendre l) w
```

[Lean][odd]

```lean
theorem stable_reduction_of_residueChar_ne_two (x : Pt) (h3 : TorsionFinite x.1 3)
    (h5 : TorsionFinite x.1 5) (w : FinitePlace (curveOf x h3 h5).F) (hw : residueChar w ≠ 2) :
    HasStableReductionAt (curveOf x h3 h5).E w
```

[Lean][specialization]

```lean
variable {F : Type*} [Field F] [NumberField F] [DecidableEq F]

theorem hasStableReductionAt_of_three_torsion (E : WeierstrassCurve F) (w : FinitePlace F)
    (hw : residueChar w ≠ 3) (P Q : E.toAffine.Point) (hP : 3 • P = 0) (hQ : 3 • Q = 0)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (hQP : Q ≠ P) (hQP' : Q ≠ -P) : HasStableReductionAt E w
```

[Lean][raynaud]

```lean
theorem stable_reduction_curveOf (x : Pt) (h3 : TorsionFinite x.1 3)
    (h5 : TorsionFinite x.1 5) (w : FinitePlace (curveOf x h3 h5).F) :
    HasStableReductionAt (curveOf x h3 h5).E w
```

[Lean][all-places]

[field]: ../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveOfFieldsData.lean#L64
[curve]: ../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveOf.lean#L25
[reduction]: ../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_GlobalField.lean#L156
[torsion]: ../../../../Solutions/Source_TripodStableTorsionPoints.lean#L23
[basis]: ../../../../Solutions/Source_TripodTorsionBasis.lean#L32
[rationality]: ../../../../Solutions/Source_TripodProviderRationality.lean#L71
[integral-legendre]: ../../../../Solutions/Source_TripodStableOdd.lean#L59
[coordinate-change]: ../../../../Solutions/Source_TripodStableOdd.lean#L91
[odd]: ../../../../Solutions/Source_TripodStableOdd.lean#L114
[specialization]: ../../../../Solutions/Source_TripodStableOdd.lean#L134
[raynaud]: ../../../../Solutions/Source_ReferenceIutStableThreeTorsion.lean#L114
[flexes]: ../../../../Solutions/Source_ReferenceIutStableThreeTorsion.lean#L39
[normal-form]: ../../../../Solutions/Source_ReferenceIutThreeTorsionNormalForm.lean#L217
[model-to-reduction]: ../../../../Solutions/Source_ReferenceIutStableModel.lean#L181
[all-places]: ../../../../Solutions/Source_TripodStableReduction.lean#L22
