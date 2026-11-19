# Source_TripodProviderRationality.lean

Upstream revision `10e40d2e52a8e7220c2a90ff1595f5b385f987ef`. Adapted source SHA-256 `93e7831eeba39e19a350d64d2c2ff804d5f715c85a16d0256ea92a189232175b`. MCP-CI leaf check `ci-022749-b4f34e16` passed with exit code 0 and no diagnostics. [Source](../../../../Solutions/Source_TripodProviderRationality.lean#L6) · [Receipt](../receipts/round-ci-022749-b4f34e16-result.json)

## English

Fix a tripod point with parameter $\lambda\in\overline{\mathbb Q}\setminus\{0,1\}$. Both theorems take finiteness proofs for the geometric $3$- and $5$-torsion of the Legendre curve. The curve `curveOf` has base field $F_\lambda$, the subfield of $\overline{\mathbb Q}$ generated over $\mathbb Q$ by $\lambda$, the chosen square roots of $-1$, $\lambda$, and $1-\lambda$, and both coordinates of every geometric affine point killed by $3$ or $5$. [Field of definition](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveOfFieldsData.lean#L64) · [Legendre curve](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveOf.lean#L25)

The theorem `sqrt_neg_one_curveOf` proves that $-1$ is a square in $F_\lambda$. The chosen element `sqrtNegOne` belongs to $F_\lambda$ by the defining set of generators. Its square is $-1$ in $\overline{\mathbb Q}$, so the same identity holds in $F_\lambda$. [Adapted theorem](../../../../Solutions/Source_TripodProviderRationality.lean#L21) · [Reference theorem](https://github.com/lana-agents/iut/blob/10e40d2e52a8e7220c2a90ff1595f5b385f987ef/Iut/Tripod/CurveFacts.lean#L87)

The theorem `six_torsion_rational_curveOf` proves that every point of $E_\lambda(\overline{\mathbb Q})$ killed by $6$ comes from an $F_\lambda$-point under base change. For a geometric affine point $(a,b)$ killed by $2$, the Legendre doubling condition gives $b=0$, and the equation gives $a\in\{0,1,\lambda\}$. For an affine point killed by $3$, the two coordinates belong to $F_\lambda$ by its defining generators. In each case, injectivity of $F_\lambda\hookrightarrow\overline{\mathbb Q}$ lets the proof transport nonsingularity to the point with these coordinates over $F_\lambda$. The origin comes from the origin. Thus the geometric $2$- and $3$-torsion both lie in the image of the base-change homomorphism. [Coordinates and descent of points](../../../../Solutions/Source_TripodProviderRationality.lean#L30) · [Rationality predicate](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_GlobalField.lean#L206)

For a point $Q$ with $[6]Q=O$, the point $[3]Q$ is killed by $2$ and the point $[2]Q$ is killed by $3$. Both lie in the same subgroup that is the image of base change. Closure under subtraction and the identity $[3]Q-[2]Q=Q$ put $Q$ in that image. [Adapted theorem](../../../../Solutions/Source_TripodProviderRationality.lean#L71) · [Reference theorem](https://github.com/lana-agents/iut/blob/10e40d2e52a8e7220c2a90ff1595f5b385f987ef/Iut/Tripod/CurveFacts.lean#L150)

## 中文

固定一个 tripod 点，其参数为 $\lambda\in\overline{\mathbb Q}\setminus\{0,1\}$。两个定理都接收 Legendre 曲线的几何 $3$-挠点和 $5$-挠点的有限性证明。`curveOf` 的底域 $F_\lambda$ 是 $\overline{\mathbb Q}$ 中由 $\lambda$、选定的 $-1$、$\lambda$ 和 $1-\lambda$ 的平方根，以及所有被 $3$ 或 $5$ 消去的几何仿射点的两个坐标在 $\mathbb Q$ 上生成的子域。 [定义域](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveOfFieldsData.lean#L64) · [Legendre 曲线](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveOf.lean#L25)

定理 `sqrt_neg_one_curveOf` 证明 $-1$ 在 $F_\lambda$ 中是平方。选定的元素 `sqrtNegOne` 是 $F_\lambda$ 定义中的生成元。它在 $\overline{\mathbb Q}$ 中的平方为 $-1$，所以同一等式在 $F_\lambda$ 中成立。 [适配定理](../../../../Solutions/Source_TripodProviderRationality.lean#L21) · [参考定理](https://github.com/lana-agents/iut/blob/10e40d2e52a8e7220c2a90ff1595f5b385f987ef/Iut/Tripod/CurveFacts.lean#L87)

定理 `six_torsion_rational_curveOf` 证明 $E_\lambda(\overline{\mathbb Q})$ 中每个被 $6$ 消去的点都是某个 $F_\lambda$-点的扩域像。若几何仿射点 $(a,b)$ 被 $2$ 消去，则由 Legendre 曲线的倍点条件得到 $b=0$，再由曲线方程得到 $a\in\{0,1,\lambda\}$。对被 $3$ 消去的仿射点，两个坐标都属于 $F_\lambda$ 的定义生成集。两种情形都用 $F_\lambda\hookrightarrow\overline{\mathbb Q}$ 的单射性，把非奇异性传回具有这些坐标的 $F_\lambda$-点。原点是原点的像。因此几何 $2$-挠点与 $3$-挠点均属于扩域同态的像。 [坐标与点的下降](../../../../Solutions/Source_TripodProviderRationality.lean#L30) · [有理性定义](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_GlobalField.lean#L206)

若 $[6]Q=O$，则 $[3]Q$ 被 $2$ 消去，$[2]Q$ 被 $3$ 消去。两点同属扩域同态的像子群。子群对减法封闭，且 $[3]Q-[2]Q=Q$，故 $Q$ 也属于该像。 [适配定理](../../../../Solutions/Source_TripodProviderRationality.lean#L71) · [参考定理](https://github.com/lana-agents/iut/blob/10e40d2e52a8e7220c2a90ff1595f5b385f987ef/Iut/Tripod/CurveFacts.lean#L150)

## 日本語

パラメータが $\lambda\in\overline{\mathbb Q}\setminus\{0,1\}$ である tripod の点を固定する。二つの定理はいずれも、Legendre 曲線の幾何的な $3$ 等分点と $5$ 等分点の有限性の証明を取る。`curveOf` の基礎体 $F_\lambda$ は、$\lambda$、選んだ $-1$、$\lambda$、$1-\lambda$ の平方根、および$3$ または $5$ 倍で消えるすべての幾何的なアフィン点の二つの座標を $\mathbb Q$ に添加して得る $\overline{\mathbb Q}$ の部分体である。 [定義体](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveOfFieldsData.lean#L64) · [Legendre 曲線](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveOf.lean#L25)

定理 `sqrt_neg_one_curveOf` は、$-1$ が $F_\lambda$ で平方であることを示す。選んだ元 `sqrtNegOne` は $F_\lambda$ の定義に用いる生成元の一つである。その平方は $\overline{\mathbb Q}$ で $-1$ なので、同じ等式が $F_\lambda$ でも成り立つ。 [適応版の定理](../../../../Solutions/Source_TripodProviderRationality.lean#L21) · [参照元の定理](https://github.com/lana-agents/iut/blob/10e40d2e52a8e7220c2a90ff1595f5b385f987ef/Iut/Tripod/CurveFacts.lean#L87)

定理 `six_torsion_rational_curveOf` は、$6$ 倍で消えるすべての $E_\lambda(\overline{\mathbb Q})$ の点が、ある $F_\lambda$ 有理点の基底変換で得られることを示す。$2$ 倍で消える幾何的なアフィン点 $(a,b)$ について、Legendre 曲線の倍点条件から $b=0$ となり、曲線の方程式から $a\in\{0,1,\lambda\}$ となる。$3$ 倍で消えるアフィン点の二つの座標は、$F_\lambda$ の定義に用いる生成元に含まれる。どちらの場合も、$F_\lambda\hookrightarrow\overline{\mathbb Q}$ の単射性により、同じ座標を持つ $F_\lambda$ 上の点の非特異性が従う。原点は原点の像である。したがって、幾何的な $2$ 等分点と $3$ 等分点はいずれも基底変換の準同型の像に属する。 [座標と点の降下](../../../../Solutions/Source_TripodProviderRationality.lean#L30) · [有理性の定義](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_GlobalField.lean#L206)

$[6]Q=O$ ならば、$[3]Q$ は $2$ 倍で消え、$[2]Q$ は $3$ 倍で消える。両点は基底変換の準同型の像である同じ部分群に属する。その部分群は差を取る操作で閉じており、$[3]Q-[2]Q=Q$ なので、$Q$ もこの像に属する。 [適応版の定理](../../../../Solutions/Source_TripodProviderRationality.lean#L71) · [参照元の定理](https://github.com/lana-agents/iut/blob/10e40d2e52a8e7220c2a90ff1595f5b385f987ef/Iut/Tripod/CurveFacts.lean#L150)
