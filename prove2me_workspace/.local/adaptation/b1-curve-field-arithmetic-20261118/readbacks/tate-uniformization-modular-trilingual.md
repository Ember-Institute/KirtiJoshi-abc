# Tate point map and quotient uniformization

## English

**Shared PointMap.** Let $k$ be a normed field. A Tate parameter $t$ gives $q\in k^\times$ with $\lVert q\rVert<1$. The group $k^\times$ consists of the nonzero elements of $k$. Write $q^{\mathbb Z}=\{q^n:n\in\mathbb Z\}\subseteq k^\times$. For $u\in k^\times$, membership in $q^{\mathbb Z}$ is equivalent to $q^nu=1$ in $k$ for some integer $n$. The formulas below define $E_q$, $X_q$, and $Y_q$.

$\mathrm{TatePointEquation}(t)$ says that $(X_q(u),Y_q(u))$ satisfies the affine equation of $E_q$ for every $u\in k^\times\setminus q^{\mathbb Z}$. Let $h_{\rm mem}$ be a proof of this proposition. Assume that $k$ is complete and ultrametric and that $12\ne0$ in $k$. The point map $P_q:k^\times\to E_q(k)$ takes $u$ to the point at infinity $O$ if $u\in q^{\mathbb Z}$. For all other $u$, it returns $(X_q(u),Y_q(u))$. Here $E_q(k)$ consists of the nonsingular affine $k$-points and $O$. The condition $12\ne0$ ensures the discriminant is nonzero, which makes the affine point nonsingular. Thus $P_q(u)=O$ exactly when $u\in q^{\mathbb Z}$.

- **Equation.** For every Tate parameter over a complete ultrametric normed field with $12\ne0$, `tatePoint_equation` proves $\mathrm{TatePointEquation}(t)$.
- **Multiplication.** Assume the same field conditions, $h_{\rm mem}$, $\lVert (2:k)\rVert=1$, and decidable equality on $k$. Then `tatePoint_mul` gives $P_q(uv)=P_q(u)+P_q(v)$ for every $u,v\in k^\times$. This includes the cases where $u$, $v$, or $uv$ is a power of $q$.
- **Surjectivity.** Assume the same complete ultrametric normed field, $h_{\rm mem}$, $12\ne0$ and $\lVert 2\rVert=1$. Then `tatePoint_surjective` gives, for every $A\in E_q(k)$, a unit $u\in k^\times$ such that $P_q(u)=A$. The proof uses classical equality decisions internally. It uses the equation child for an auxiliary affine point and the multiplication child for translations.
- **Quotient.** Over a complete ultrametric normed field with $12\ne0$ and $\lVert2\rVert=1$, the parent asks for an additive group isomorphism $U:(k^\times/q^{\mathbb Z})_{\rm add}\simeq E_q(k)$ for each Tate parameter. Both coordinate functions on $E_q(k)$ have value zero at $O$. For every $u\in k^\times\setminus q^{\mathbb Z}$, the coordinates of $U([u])$ equal $X_q(u)$ and $Y_q(u)$. The sketch takes $h_{\rm mem}$ from the equation child and uses classical decidable equality for the multiplication child. It uses surjectivity and the kernel $q^{\mathbb Z}$ to obtain $U$ with $U([u])=P_q(u)$ for every $u\in k^\times$.

## 简体中文

**共享点映射。** 设 $k$ 为赋范域，$t$ 为 Tate 参数，由满足 $\lVert q\rVert<1$ 的 $q\in k^\times$ 给出。$k^\times$ 是 $k$ 的非零元素组成的乘法群。记 $q^{\mathbb Z}=\{q^n:n\in\mathbb Z\}\subseteq k^\times$。对 $u\in k^\times$，$u$ 属于 $q^{\mathbb Z}$ 当且仅当存在整数 $n$，使得 $q^nu=1$ 在 $k$ 中成立。$E_q$、$X_q$ 和 $Y_q$ 由下方公式给出。

$\mathrm{TatePointEquation}(t)$ 断言，对每个 $u\in k^\times\setminus q^{\mathbb Z}$，$(X_q(u),Y_q(u))$ 满足 $E_q$ 的仿射方程。给定该命题的证明 $h_{\rm mem}$，再假设 $k$ 完备且超度量，并且 $k$ 中 $12\ne0$。点映射 $P_q:k^\times\to E_q(k)$ 将 $q^{\mathbb Z}$ 中的元素送到无穷远点 $O$，将其余元素送到 $(X_q(u),Y_q(u))$。点集 $E_q(k)$ 由非奇异仿射 $k$ 点和 $O$ 组成。$12\ne0$ 保证判别式非零，故映射给出的仿射点非奇异。因此，$P_q(u)=O$ 当且仅当 $u\in q^{\mathbb Z}$。

- **方程。** 对满足 $12\ne0$ 的完备超度量赋范域上的每个 Tate 参数，`tatePoint_equation` 证明 $\mathrm{TatePointEquation}(t)$。
- **乘法。** 在同样的域条件下，另给定 $h_{\rm mem}$、$k$ 中的 $\lVert 2\rVert=1$，以及 $k$ 上的相等关系可判定。`tatePoint_mul` 断言对所有 $u,v\in k^\times$，$P_q(uv)=P_q(u)+P_q(v)$。该等式也涵盖 $u$、$v$ 或 $uv$ 为 $q$ 的整数次幂的情形。
- **满射。** 设 $k$ 仍为完备超度量赋范域，并给定 $h_{\rm mem}$、$12\ne0$ 和 $\lVert 2\rVert=1$。`tatePoint_surjective` 断言，对每个 $A\in E_q(k)$，存在 $u\in k^\times$ 使 $P_q(u)=A$。证明在内部用经典逻辑判定相等，并调用方程子题构造辅助仿射点，调用乘法子题处理平移。
- **商群。** 对满足 $12\ne0$ 和 $\lVert2\rVert=1$ 的完备超度量赋范域，父题要求每个 Tate 参数都有加法群同构 $U:(k^\times/q^{\mathbb Z})_{\rm add}\simeq E_q(k)$。$E_q(k)$ 的两个坐标函数在 $O$ 处均为零。对每个 $u\in k^\times\setminus q^{\mathbb Z}$，$U([u])$ 的坐标分别等于 $X_q(u)$ 和 $Y_q(u)$。归约从方程子题取得 $h_{\rm mem}$，并为乘法子题提供经典的相等判定。根据满射性与核 $q^{\mathbb Z}$，得到对每个 $u\in k^\times$ 都满足 $U([u])=P_q(u)$ 的 $U$。

## 日本語

**共通の点写像。** $k$ をノルム体とする。テイトパラメータ $t$ は $\lVert q\rVert<1$ を満たす $q\in k^\times$ を与える。$k^\times$ は $k$ の零でない元の乗法群である。$q^{\mathbb Z}=\{q^n:n\in\mathbb Z\}\subseteq k^\times$ とおく。$u\in k^\times$ が $q^{\mathbb Z}$ に属することと、ある整数 $n$ について $q^nu=1$ が $k$ で成り立つことは同値である。$E_q$、$X_q$、$Y_q$ は下の式で定める。

$\mathrm{TatePointEquation}(t)$ は、すべての $u\in k^\times\setminus q^{\mathbb Z}$ に対して $(X_q(u),Y_q(u))$ が $E_q$ のアフィン方程式を満たすという命題である。その証明 $h_{\rm mem}$ を与え、さらに $k$ は完備で超距離的であり、$k$ で $12\ne0$ とする。点写像 $P_q:k^\times\to E_q(k)$ は $q^{\mathbb Z}$ の元を無限遠点 $O$ に送り、それ以外の元 $u$ を $(X_q(u),Y_q(u))$ に送る。$E_q(k)$ は非特異なアフィン $k$ 点と $O$ からなる。$12\ne0$ のもとで判別式は零でないため、このアフィン点は非特異である。したがって $P_q(u)=O$ と $u\in q^{\mathbb Z}$ は同値である。

- **方程式。** $12\ne0$ を満たす完備超距離ノルム体上の各テイトパラメータについて、`tatePoint_equation` は $\mathrm{TatePointEquation}(t)$ を証明する。
- **積。** 同じ体の条件に加え、$h_{\rm mem}$ と $\lVert2\rVert=1$ を与え、$k$ 上の等号が決定可能であるとする。`tatePoint_mul` は、すべての $u,v\in k^\times$ について $P_q(uv)=P_q(u)+P_q(v)$ を与える。$u$、$v$、$uv$ のいずれかが $q$ の整数乗である場合も含む。
- **全射性。** 完備超距離ノルム体 $k$ に対して $h_{\rm mem}$、$12\ne0$、$\lVert2\rVert=1$ を仮定する。`tatePoint_surjective` は、各 $A\in E_q(k)$ に対して $P_q(u)=A$ を満たす $u\in k^\times$ の存在を与える。証明の内部では古典論理で等号を判定する。補助アフィン点には方程式の子命題を、平行移動には積の子命題を用いる。
- **商群。** $12\ne0$ と $\lVert2\rVert=1$ を満たす完備超距離ノルム体上で、親命題は各テイトパラメータに対する加法群同型 $U:(k^\times/q^{\mathbb Z})_{\rm add}\simeq E_q(k)$ を求める。$E_q(k)$ の二つの座標関数は $O$ で零を取る。すべての $u\in k^\times\setminus q^{\mathbb Z}$ について、$U([u])$ の座標はそれぞれ $X_q(u)$ と $Y_q(u)$ である。帰着では方程式の子命題から $h_{\rm mem}$ を得て、積の子命題には古典論理による等号の決定可能性を与える。全射性と核 $q^{\mathbb Z}$ により、すべての $u\in k^\times$ で $U([u])=P_q(u)$ を満たす $U$ を得る。

## Shared formulas · 共用公式 · 共通の式

$$
\begin{aligned}
s_m(q)&=\sum_{j\ge1}\frac{j^m q^j}{1-q^j},
&E_q&\colon y^2+xy=x^3-5s_3(q)x-\frac{5s_3(q)+7s_5(q)}{12},\\
X_q(u)&=\sum_{n\in\mathbb Z}\frac{q^n u}{(1-q^nu)^2}-2s_1(q),
&Y_q(u)&=\sum_{n\in\mathbb Z}\frac{(q^nu)^2}{(1-q^nu)^3}+s_1(q).
\end{aligned}
$$

Here $m$ is a natural number. The series and the integer coefficients take their values in $k$. The Lean definitions use $0^{-1}=0$ and the topological sum, which returns zero for a nonsummable family. The coordinate laws apply off $q^{\mathbb Z}$, where all denominators $1-q^nu$ are nonzero. [Curve coefficients](../../../../Definitions/Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_Weierstrass.lean:95) · [Coordinate series](../../../../Definitions/Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_Parametrization.lean)

这里 $m$ 是自然数。级数及整系数均在 $k$ 中取值。形式定义规定 $0^{-1}=0$，并使用拓扑和，对不可求和的族取值为零。在 $q^{\mathbb Z}$ 之外，所有分母 $1-q^nu$ 均非零，坐标等式在此范围内成立。

ここで $m$ は自然数である。級数と整数係数は $k$ に値を取る。形式定義では $0^{-1}=0$ とし、総和可能でない族に対して零を返す位相的な和を用いる。座標等式は、すべての分母 $1-q^nu$ が零でない $q^{\mathbb Z}$ の外部で成り立つ。

## Source and proof dependencies

The proof source is the Apache-2.0 Tate curves library of the Tate curves contributors, revision `ca6c2279d3cea0690cdb01328e727118d5485d68`. The modular source manifests give Lean 4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` as the adaptation environment. They record declaration extraction from graph job `ci-012771-ee109b3e`, whose compiler was Lean 4.35.0-rc3. [Pinned library](https://github.com/lana-agents/tate-curves-theta/tree/ca6c2279d3cea0690cdb01328e727118d5485d68)

| Node | Lean statement or sketch | Source |
| --- | --- | --- |
| PointMap | [Definition](../../../../Definitions/Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_PointMap.lean:28) | [PointMap.lean](https://github.com/lana-agents/tate-curves-theta/blob/ca6c2279d3cea0690cdb01328e727118d5485d68/TateCurvesTheta/TateCurve/PointMap.lean#L76) |
| Equation | [Statement](../../../../Theorems/Thm_AbcAdaptation_Reference_TateCurvesTheta_TateParameter_tatePoint_equation.lean:14) | [TatePointOnCurve.lean](https://github.com/lana-agents/tate-curves-theta/blob/ca6c2279d3cea0690cdb01328e727118d5485d68/TateCurvesTheta/TateCurve/TatePointOnCurve.lean#L334) · [Manifest](../platform-sl2/modular-tate/tatePoint_equation-source-manifest.json) |
| Multiplication | [Statement](../../../../Theorems/Thm_AbcAdaptation_Reference_TateCurvesTheta_TateParameter_tatePoint_mul.lean:14) | [GroupLaw.lean](https://github.com/lana-agents/tate-curves-theta/blob/ca6c2279d3cea0690cdb01328e727118d5485d68/TateCurvesTheta/TateCurve/GroupLaw.lean#L242) · [Manifest](../platform-sl2/modular-tate/tatePoint_mul-source-manifest.json) |
| Surjectivity | [Statement](../../../../Theorems/Thm_AbcAdaptation_Reference_TateCurvesTheta_TateParameter_tatePoint_surjective.lean:14) | [TateUniformization.lean](https://github.com/lana-agents/tate-curves-theta/blob/ca6c2279d3cea0690cdb01328e727118d5485d68/TateCurvesTheta/TateCurve/TateUniformization.lean#L55) · [Manifest](../platform-sl2/modular-tate/tatePoint_surjective-source-manifest.json) |
| Quotient | [Parent sketch](../platform-sl2/Sketch_exists_tateUniformization.lean:129) | [Upstream quotient](https://github.com/lana-agents/tate-curves-theta/blob/ca6c2279d3cea0690cdb01328e727118d5485d68/TateCurvesTheta/TateCurve/TateUniformization.lean#L105) · [Local quotient constructor](../../../../Solutions/Source_ReferenceIutTateUniformization.lean:103) |

The three child statement modules import PointMap and contain statement placeholders. The surjectivity *solution* imports the equation and multiplication theorem modules. It calls the equation through `tatePoint_mem'` in the large-point proof. It calls multiplication through `tatePoint_mul` in the annulus and unit-sphere proofs. The parent sketch imports and uses all three children. [Surjectivity imports](../platform-sl2/Sol_tatePoint_surjective.lean:23) · [Equation use](../platform-sl2/Sol_tatePoint_surjective.lean) · [Annulus multiplication](../platform-sl2/Sol_tatePoint_surjective.lean) · [Unit-sphere multiplication](../platform-sl2/Sol_tatePoint_surjective.lean)
