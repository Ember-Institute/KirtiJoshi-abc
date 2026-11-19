# The designated points for the cyclic Vélu construction

## English

Let $E_\lambda/F$ be the Legendre curve `P.curve x`. Its equation is $Y^2=X(X-1)(X-\lambda)$ with $\lambda\ne0,1$. Write $i,a,b\in F$ for the chosen roots with $i^2=-1$, $a^2=\lambda$, and $b^2=1-\lambda$. The pairs defined over $F$ are

$$
\begin{aligned}
T_{1,\mathrm{base}}&=(0,0), & R_{1,\mathrm{base}}&=(a,ia(a-1)),\\
T_{2,\mathrm{base}}&=(1,0), & R_{2,\mathrm{base}}&=(1+b,b(1+b)).
\end{aligned}
$$

The two $T_{j,\mathrm{base}}$ are distinct nonzero points of order two. The two halves have order four. Doubling the halves uses the tangent slopes $i(a-1)$ and $1+b$, respectively. Write $O$ for the group identity.

$$
[2]T_{j,\mathrm{base}}=O,\qquad [2]R_{j,\mathrm{base}}=T_{j,\mathrm{base}}\qquad(j=1,2).
$$

[Base points](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:168) · [First tangent calculation](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:86) · [Second tangent calculation](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:121) · [Doubling over $F$](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:187)

For a prime $\ell$, let $L$ be the torsion field of `P.modRep x ℓ hℓ` and let $j_L\colon F\hookrightarrow L$ be the field embedding. The injective additive map `baseChangeToL` sends these pairs to $(T_1,R_1)$ and $(T_2,R_2)$. It preserves their orders and the doubling equalities. It applies $j_L$ to the coordinates. In particular, the two differences in `xCoordinate_T₁_sub_R₁` and `xCoordinate_T₂_sub_R₂` are

$$
X(T_1)-X(R_1)=-j_L(a),\qquad X(T_2)-X(R_2)=-j_L(b).
$$

[Base change](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:218) · [Points over $L$](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:233) · [Doubling over $L$](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:252) · [Distinctness](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:264) · [Coordinate transport](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:272) · [First coordinate difference](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:282) · [Second coordinate difference](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:292)

MCP-CI leaf check `ci-022232-d1190d06` passed with exit code 0. Project and axiom review passed. [MCP-CI](../receipts/round-ci-022264-0b6cd23c-result.json) [MCP-CI receipt](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-022232-d1190d06-result.json)

## 中文

设 $E_\lambda/F$ 为 `P.curve x` 对应的 Legendre 曲线，方程为 $Y^2=X(X-1)(X-\lambda)$，其中 $\lambda\ne0,1$。记选定的平方根为 $i,a,b\in F$，满足 $i^2=-1$、$a^2=\lambda$、$b^2=1-\lambda$。在 $F$ 上定义的两对点为

$$
\begin{aligned}
T_{1,\mathrm{base}}&=(0,0), & R_{1,\mathrm{base}}&=(a,ia(a-1)),\\
T_{2,\mathrm{base}}&=(1,0), & R_{2,\mathrm{base}}&=(1+b,b(1+b)).
\end{aligned}
$$

两个 $T_{j,\mathrm{base}}$ 互异，均为非零的二阶点。两个二分点的阶均为四。计算两个二分点的倍点时，切线斜率分别为 $i(a-1)$ 与 $1+b$。记点群的零元为 $O$。

$$
[2]T_{j,\mathrm{base}}=O,\qquad [2]R_{j,\mathrm{base}}=T_{j,\mathrm{base}}\qquad(j=1,2).
$$

[基域上的点](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:168) · [第一条切线计算](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:86) · [第二条切线计算](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:121) · [$F$ 上的倍点等式](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:187)

取素数 $\ell$，设 $L$ 为 `P.modRep x ℓ hℓ` 的挠点域，$j_L\colon F\hookrightarrow L$ 为域嵌入。单射加法同态 `baseChangeToL` 把两对点分别映到 $(T_1,R_1)$ 与 $(T_2,R_2)$，保持点的阶与倍点等式。它在坐标上作用为 $j_L$。因此 `xCoordinate_T₁_sub_R₁` 与 `xCoordinate_T₂_sub_R₂` 给出

$$
X(T_1)-X(R_1)=-j_L(a),\qquad X(T_2)-X(R_2)=-j_L(b).
$$

[基变换](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:218) · [$L$ 上的点](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:233) · [$L$ 上的倍点等式](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:252) · [两挠点互异](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:264) · [基变换的坐标公式](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:272) · [第一组横坐标差](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:282) · [第二组横坐标差](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:292)

MCP-CI 叶检查 `ci-022232-d1190d06` 通过，退出码为 0。项目与公理审查通过。 [MCP-CI](../receipts/round-ci-022264-0b6cd23c-result.json) [MCP-CI 回执](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-022232-d1190d06-result.json)

## 日本語

`P.curve x` を Legendre 曲線 $E_\lambda/F$ とする。その方程式は $Y^2=X(X-1)(X-\lambda)$ で、$\lambda\ne0,1$ である。選んだ平方根を $i,a,b\in F$ とし、$i^2=-1$、$a^2=\lambda$、$b^2=1-\lambda$ とする。$F$ 上で指定する二組の点は次のとおりである。

$$
\begin{aligned}
T_{1,\mathrm{base}}&=(0,0), & R_{1,\mathrm{base}}&=(a,ia(a-1)),\\
T_{2,\mathrm{base}}&=(1,0), & R_{2,\mathrm{base}}&=(1+b,b(1+b)).
\end{aligned}
$$

二つの $T_{j,\mathrm{base}}$ は相異なる非零点で、位数は 2 である。二つの二等分点の位数は 4 である。二等分点の倍点の計算で用いる接線の傾きは、それぞれ $i(a-1)$ と $1+b$ である。点の加法群の零元を $O$ とする。

$$
[2]T_{j,\mathrm{base}}=O,\qquad [2]R_{j,\mathrm{base}}=T_{j,\mathrm{base}}\qquad(j=1,2).
$$

[基礎体上の点](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:168) · [第一の接線の計算](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:86) · [第二の接線の計算](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:121) · [$F$ 上の倍点の等式](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:187)

素数 $\ell$ に対し、$L$ を `P.modRep x ℓ hℓ` のねじれ点体、$j_L\colon F\hookrightarrow L$ を体の埋め込みとする。単射な加法準同型 `baseChangeToL` は二組の点を $(T_1,R_1)$ と $(T_2,R_2)$ に移し、位数と倍点の等式を保つ。座標には $j_L$ が作用する。従って `xCoordinate_T₁_sub_R₁` と `xCoordinate_T₂_sub_R₂` により、次の等式を得る。

$$
X(T_1)-X(R_1)=-j_L(a),\qquad X(T_2)-X(R_2)=-j_L(b).
$$

[基底変換](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:218) · [$L$ 上の点](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:233) · [$L$ 上の倍点の等式](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:252) · [二点の相異性](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:264) · [基底変換の座標公式](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:272) · [第一の座標差](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:282) · [第二の座標差](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:292)

MCP-CI の葉モジュール検査 `ci-022232-d1190d06` は終了コード 0 で通過した。プロジェクトの検査と公理の監査に合格した。 [MCP-CI](../receipts/round-ci-022264-0b6cd23c-result.json) [MCP-CI の結果](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-022232-d1190d06-result.json)
