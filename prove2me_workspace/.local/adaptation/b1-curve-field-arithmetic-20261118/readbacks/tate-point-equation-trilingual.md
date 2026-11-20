# The affine Tate point equation

Upstream / 上游 / 上流 `lana-agents/tate-curves-theta@ca6c2279d3cea0690cdb01328e727118d5485d68`

## English

Let $k$ have `[NormedField k]`, `[CompleteSpace k]`, and `[IsUltrametricDist k]`, with `(12 : k) ≠ 0`. A Tate parameter `t` gives a unit $q=t.q$ with $\lVert q\rVert<1$. Take $u\in k^\times$ with `∀ n : ℤ, (t.q : k) ^ n * (u : k) ≠ 1`, so $u$ lies outside $q^{\mathbb Z}$. The theorem `tatePoint_equation` proves `t.TatePointEquation`, the assertion that all such units satisfy

$$
Y(u)^2+X(u)Y(u)=X(u)^3+a_4X(u)+a_6.
$$

[Lean theorem](../../../../Solutions/Source_ReferenceIutTatePointEquation.lean#L25) · [Power-orbit equivalence](../../../../Solutions/Source_ReferenceIutTateUniformization.lean#L30) · [Equation predicate](../../../../Solutions/Source_ReferenceIutTateUniformization.lean#L47)

1. Express the Eisenstein series in powers of $q$. Apply Besge's $\sigma_1 * \sigma_1$ identity and the $\sigma_1 * \sigma_3$ identity coefficient by coefficient. The resulting series identities give the weight-$4$ and weight-$6$ brackets `bracketA_eq_zero` and `bracketB_eq`. [Series identities](https://github.com/lana-agents/tate-curves-theta/blob/ca6c2279d3cea0690cdb01328e727118d5485d68/TateCurvesTheta/TateCurve/TatePointOnCurve.lean#L135) · [Brackets](https://github.com/lana-agents/tate-curves-theta/blob/ca6c2279d3cea0690cdb01328e727118d5485d68/TateCurvesTheta/TateCurve/TatePointOnCurve.lean#L269)
2. Identify `pSum` with `eisenstein 1`. In the expansion of the Weierstrass defect, the two brackets cancel the coefficient of the $X$-term orbit sum and the constant term. `tateDefect_eq_zero` proves zero defect for every unit satisfying the orbit condition. [Defect expansion](https://github.com/lana-agents/tate-curves-theta/blob/ca6c2279d3cea0690cdb01328e727118d5485d68/TateCurvesTheta/TateCurve/DefectVanishing.lean#L1050) · [Vanishing](https://github.com/lana-agents/tate-curves-theta/blob/ca6c2279d3cea0690cdb01328e727118d5485d68/TateCurvesTheta/TateCurve/TatePointOnCurve.lean#L309)
3. Use `tatePoint_equation_iff` to turn zero defect into the affine equation. Christian Merten's `tatePoint_mem'` makes this step. The local leaf applies it to the same $q$ and norm bound. [Equation equivalence](https://github.com/lana-agents/tate-curves-theta/blob/ca6c2279d3cea0690cdb01328e727118d5485d68/TateCurvesTheta/TateCurve/WeierstrassIdentity.lean#L87) · [Upstream theorem](https://github.com/lana-agents/tate-curves-theta/blob/ca6c2279d3cea0690cdb01328e727118d5485d68/TateCurvesTheta/TateCurve/TatePointOnCurve.lean#L334)

Locally, `tatePoint` uses the equation in its affine branch to construct a nonsingular point. `TateParameterUniformization.ofTateParameter` passes the equation as `hmem` to `ofTatePoint`, together with additivity and surjectivity. The uniformization uses the additional hypothesis `‖(2 : k)‖ = 1`. It provides the local uniformizations for the P7 Tate family and the Tate ramification argument. [Point map](../../../../Solutions/Source_ReferenceIutTateUniformization.lean#L54) · [Uniformization consumer](../../../../Solutions/Source_ReferenceIutTateUniformizationLaws.lean#L64) · [P7 Tate family](../../../../Solutions/Source_ReferenceIutCurveTateFamily.lean#L37) · [Local ramification](../../../../Solutions/Source_SL2ImageLocalTate.lean#L95)

## 中文

设 $k$ 带有 `[NormedField k]`、`[CompleteSpace k]` 和 `[IsUltrametricDist k]` 实例，并满足 `(12 : k) ≠ 0`。Tate 参数 `t` 给出单位 $q=t.q$，满足 $\lVert q\rVert<1$。取满足 `∀ n : ℤ, (t.q : k) ^ n * (u : k) ≠ 1` 的 $u\in k^\times$，即 $u$ 位于整数幂轨道 $q^{\mathbb Z}$ 之外。定理 `tatePoint_equation` 证明 `t.TatePointEquation`，即所有这类单位都满足

$$
Y(u)^2+X(u)Y(u)=X(u)^3+a_4X(u)+a_6.
$$

[Lean 定理](../../../../Solutions/Source_ReferenceIutTatePointEquation.lean#L25) · [幂轨道等价](../../../../Solutions/Source_ReferenceIutTateUniformization.lean#L30) · [方程谓词](../../../../Solutions/Source_ReferenceIutTateUniformization.lean#L47)

1. 将 Eisenstein 级数写成同一个 $q$ 幂展开，逐系数应用 Besge 的 $\sigma_1 * \sigma_1$ 恒等式与 $\sigma_1 * \sigma_3$ 卷积恒等式。所得级数恒等式给出权 $4$ 和权 $6$ 的括号恒等式 `bracketA_eq_zero` 和 `bracketB_eq`。 [级数恒等式](https://github.com/lana-agents/tate-curves-theta/blob/ca6c2279d3cea0690cdb01328e727118d5485d68/TateCurvesTheta/TateCurve/TatePointOnCurve.lean#L135) · [括号恒等式](https://github.com/lana-agents/tate-curves-theta/blob/ca6c2279d3cea0690cdb01328e727118d5485d68/TateCurvesTheta/TateCurve/TatePointOnCurve.lean#L269)
2. 先将 `pSum` 写为 `eisenstein 1`，再展开 Weierstrass 方程两边之差。用两条括号恒等式消去 $X$ 项轨道和的系数及常数项。`tateDefect_eq_zero` 证明对每个满足轨道条件的单位，两边之差均为零。 [差值展开](https://github.com/lana-agents/tate-curves-theta/blob/ca6c2279d3cea0690cdb01328e727118d5485d68/TateCurvesTheta/TateCurve/DefectVanishing.lean#L1050) · [消失定理](https://github.com/lana-agents/tate-curves-theta/blob/ca6c2279d3cea0690cdb01328e727118d5485d68/TateCurvesTheta/TateCurve/TatePointOnCurve.lean#L309)
3. Christian Merten 的 `tatePoint_mem'` 用 `tatePoint_equation_iff` 把差值为零转为仿射方程成立。本地叶对同一个 $q$ 和范数界应用此定理。 [方程等价](https://github.com/lana-agents/tate-curves-theta/blob/ca6c2279d3cea0690cdb01328e727118d5485d68/TateCurvesTheta/TateCurve/WeierstrassIdentity.lean#L87) · [上游定理](https://github.com/lana-agents/tate-curves-theta/blob/ca6c2279d3cea0690cdb01328e727118d5485d68/TateCurvesTheta/TateCurve/TatePointOnCurve.lean#L334)

本地 `tatePoint` 在仿射分支用该方程构造非奇异点。`TateParameterUniformization.ofTateParameter` 将方程证明作为 `hmem`，连同加法性和满射性传给 `ofTatePoint`。一致化还使用条件 `‖(2 : k)‖ = 1`，并为 P7 的 Tate 族及 Tate 分歧论证提供局部一致化。 [点映射](../../../../Solutions/Source_ReferenceIutTateUniformization.lean#L54) · [一致化调用点](../../../../Solutions/Source_ReferenceIutTateUniformizationLaws.lean#L64) · [P7 的 Tate 族](../../../../Solutions/Source_ReferenceIutCurveTateFamily.lean#L37) · [局部分歧](../../../../Solutions/Source_SL2ImageLocalTate.lean#L95)

## 日本語

$k$ は `[NormedField k]`、`[CompleteSpace k]`、`[IsUltrametricDist k]` を備え、`(12 : k) ≠ 0` を満たすとする。Tate パラメータ `t` は $\lVert q\rVert<1$ を満たす単元 $q=t.q$ を定める。`∀ n : ℤ, (t.q : k) ^ n * (u : k) ≠ 1` を満たす単元 $u\in k^\times$ を取る。これは $u$ が整数べきの軌道 $q^{\mathbb Z}$ の外にある条件である。定理 `tatePoint_equation` は、これらすべての単元について次の方程式が成り立つという命題 `t.TatePointEquation` を証明する。

$$
Y(u)^2+X(u)Y(u)=X(u)^3+a_4X(u)+a_6.
$$

[Lean の定理](../../../../Solutions/Source_ReferenceIutTatePointEquation.lean#L25) · [べき軌道との同値](../../../../Solutions/Source_ReferenceIutTateUniformization.lean#L30) · [方程式の述語](../../../../Solutions/Source_ReferenceIutTateUniformization.lean#L47)

1. Eisenstein 級数を共通の $q$ べき展開にそろえる。Besge の $\sigma_1 * \sigma_1$ の恒等式と $\sigma_1 * \sigma_3$ の畳み込み恒等式を各係数に適用する。得られた級数の恒等式から、重さ $4$ と $6$ の括弧の恒等式 `bracketA_eq_zero` と `bracketB_eq` を導く。 [級数の恒等式](https://github.com/lana-agents/tate-curves-theta/blob/ca6c2279d3cea0690cdb01328e727118d5485d68/TateCurvesTheta/TateCurve/TatePointOnCurve.lean#L135) · [括弧の恒等式](https://github.com/lana-agents/tate-curves-theta/blob/ca6c2279d3cea0690cdb01328e727118d5485d68/TateCurvesTheta/TateCurve/TatePointOnCurve.lean#L269)
2. `pSum` を `eisenstein 1` と同定し、Weierstrass 方程式の両辺の差を展開する。二つの括弧の恒等式により、$X$ の項の軌道和の係数と定数項が消える。`tateDefect_eq_zero` は、軌道条件を満たすすべての単元で両辺の差が零になることを示す。 [差の展開](https://github.com/lana-agents/tate-curves-theta/blob/ca6c2279d3cea0690cdb01328e727118d5485d68/TateCurvesTheta/TateCurve/DefectVanishing.lean#L1050) · [差の消滅](https://github.com/lana-agents/tate-curves-theta/blob/ca6c2279d3cea0690cdb01328e727118d5485d68/TateCurvesTheta/TateCurve/TatePointOnCurve.lean#L309)
3. Christian Merten の `tatePoint_mem'` は `tatePoint_equation_iff` によって、差が零であることからアフィン方程式を得る。ローカルの補題は、同じ $q$ とノルムの上界にこの定理を適用する。 [方程式との同値](https://github.com/lana-agents/tate-curves-theta/blob/ca6c2279d3cea0690cdb01328e727118d5485d68/TateCurvesTheta/TateCurve/WeierstrassIdentity.lean#L87) · [上流の定理](https://github.com/lana-agents/tate-curves-theta/blob/ca6c2279d3cea0690cdb01328e727118d5485d68/TateCurvesTheta/TateCurve/TatePointOnCurve.lean#L334)

ローカルの `tatePoint` はアフィン分岐でこの方程式を使い、非特異点を構成する。`TateParameterUniformization.ofTateParameter` は方程式の証明を `hmem` とし、加法性と全射性とともに `ofTatePoint` に渡す。一意化では追加の条件 `‖(2 : k)‖ = 1` を用いる。この一意化は P7 の Tate 族と Tate 分岐の証明に使われる。 [点の写像](../../../../Solutions/Source_ReferenceIutTateUniformization.lean#L54) · [一意化での利用](../../../../Solutions/Source_ReferenceIutTateUniformizationLaws.lean#L64) · [P7 の Tate 族](../../../../Solutions/Source_ReferenceIutCurveTateFamily.lean#L37) · [局所分岐](../../../../Solutions/Source_SL2ImageLocalTate.lean#L95)
