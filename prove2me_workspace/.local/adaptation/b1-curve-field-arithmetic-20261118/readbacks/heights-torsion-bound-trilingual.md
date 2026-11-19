# Complex torsion coordinates, the Legendre bound, and the cyclic subgroup bound

## Formulas / 公式 / 式

```text
(1) ‖x + b₂(W)/12‖⁶
      ≤ A ‖Δ(W)‖ max(‖j(W)‖, 1) [2N² + B (log(max(‖j(W)‖, exp(1))) + 1)²]⁶

(2) ‖a‖ ≤ C N²

    h(x)  = P.h x
    h₂(x) = (P.localData x).heightEq 2
    C₀    = torsionConst K.c (legendre_torsion_x_le_from_source K.c)
    T_K   = cyclicConst K C₀ = [2 log(32 C₀) + 6 K.c + 4 log 4]/6

(3) (ℓ − 1)/4  · (h(x) − h₂(x)) ≤ 10 log ℓ + 2 log(32 C₀) + 6 K.c + 4 log 4
(4) (ℓ − 2)/24 · (h(x) − h₂(x)) ≤  2 log ℓ + T_K
```

## English

- `exists_torsion_x_bound_from_source` proves that two real constants `A, B ≥ 0` work uniformly in (1). The bound applies to every elliptic Weierstrass curve `W` over `ℂ`. It applies to each natural number `N ≥ 1` and each nonsingular affine point `(x, y)` with `N • (x, y) = 0`. Here `b₂(W)`, `Δ(W)`, and `j(W)` are the usual Weierstrass invariants. The proof uses the surjectivity of the modular `j`-function and the additive uniformization of the lattice curve. It then uses two logarithmic comparisons on the standard fundamental domain. The comparisons control the scale of the change of variables and the norm of the lattice parameter. [Exact statement](../../../../Solutions/Source_TripodCyclicArch.lean#L25) · [Proof](../../../../Solutions/Source_ReferenceHeightsTorsionBound.lean#L12) · [Change of variables](../../../../Solutions/Source_ReferenceHeightsTorsionArchimedean.lean#L60)
- For each real `c`, `legendre_torsion_x_le_from_source` gives a real `C ≥ 0` that works uniformly in (2). The bound applies to complex parameters `λ` with `|log ‖λ‖| ≤ c` and `|log ‖λ − 1‖| ≤ c`. For each such parameter, use an elliptic Weierstrass curve `W = legendre λ`. Then (2) holds for each nonsingular affine point `(a, b)` on `W` with `N • (a, b) = 0` and `N ≥ 1`. The specialization bounds the discriminant, `j`-invariant, and coordinate shift using `exp(c)`. [Legendre predicate](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound.lean#L23) · [Specialization](../../../../Solutions/Source_TripodCyclicArch.lean#L86) · [Existence theorem](../../../../Solutions/Source_ReferenceHeightsTorsionBound.lean#L22)
- `cyclicBoundOdd_of_mainBound` takes the explicit Vélu hypothesis `hmain`. For any real `C ≥ 1` that satisfies `LegendreTorsionXBound K.c C`, this hypothesis supplies `CyclicMainBoundHyp P K C`. At the chosen `C₀`, that predicate gives (3) for `x ∈ K.set`, an odd prime `ℓ`, and a Galois-stable geometric subgroup of order `ℓ`. It requires the subgroup to pull back to the Tate graph line at every finite place of the `ℓ`-torsion field above `VBadOdd`. The theorem chooses a witness from the Legendre theorem at `c = K.c`. It sets `C₀` to the maximum of `1` and that witness. [Vélu predicate](../../../../Solutions/Source_TripodCyclicBoundOdd.lean#L177) · [Graph-line predicate](../../../../Solutions/Source_TripodCyclicBoundOdd.lean#L145) · [Choice of constant](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound.lean#L30)
- The conclusion (4) applies to `x ∈ K.set ∩ ptLE d` and primes `ℓ ≥ 7`. It assumes that the curve has a Galois-stable geometric subgroup of order `ℓ`. At every `w ∈ (P.localData x).bad`, it also assumes `ℓ ∤ (P.localData x).hv w`. The proof uses the local theorem and the nondivisibility condition to obtain the required graph-line equalities. The proof divides (3) by six. It uses `h(x) − h₂(x) ≥ 0` and `log ℓ ≥ 0` to compare the coefficients. [Cyclic predicate](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts.lean#L24) · [Local proof](../../../../Solutions/Source_TripodCyclicLocal.lean#L256) · [Cyclic theorem](../../../../Solutions/Source_TripodCyclicBoundFromSource.lean#L28)

## 中文

- `exists_torsion_x_bound_from_source` 证明存在统一的实常数 `A, B ≥ 0` 使 (1) 成立。它适用于每条复椭圆 Weierstrass 曲线 `W`、每个自然数 `N ≥ 1`，以及满足 `N • (x, y) = 0` 的每个非奇异仿射点 `(x, y)`。`b₂(W)`、`Δ(W)` 和 `j(W)` 是通常的 Weierstrass 不变量。证明使用模 `j` 函数的满射性、格子曲线的加法一致化，以及标准基本域上的两个对数比较。两个比较分别控制变量代换的缩放和格子参数的范数。[原陈述](../../../../Solutions/Source_TripodCyclicArch.lean#L25) · [证明](../../../../Solutions/Source_ReferenceHeightsTorsionBound.lean#L12) · [变量代换](../../../../Solutions/Source_ReferenceHeightsTorsionArchimedean.lean#L60)
- 对每个实数 `c`，`legendre_torsion_x_le_from_source` 给出使 (2) 统一成立的实数 `C ≥ 0`。取复数 `λ` 满足 `|log ‖λ‖| ≤ c` 和 `|log ‖λ − 1‖| ≤ c`，以及椭圆模型 `W = legendre λ`。对 `W` 上每个被自然数 `N ≥ 1` 消去的非奇异仿射点 `(a, b)`，都有 (2)。特化证明用 `exp(c)` 控制判别式、`j` 不变量和坐标平移量。[Legendre 谓词](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound.lean#L23) · [特化证明](../../../../Solutions/Source_TripodCyclicArch.lean#L86) · [存在定理](../../../../Solutions/Source_ReferenceHeightsTorsionBound.lean#L22)
- `cyclicBoundOdd_of_mainBound` 显式接收 Vélu 假设 `hmain`。对每个满足 `LegendreTorsionXBound K.c C` 的实数 `C ≥ 1`，它提供 `CyclicMainBoundHyp P K C`。在所选 `C₀` 处，该谓词给出 (3)，适用于 `x ∈ K.set`、奇素数 `ℓ` 和阶为 `ℓ` 的 Galois 稳定几何子群。它要求在 `ℓ`-挠点域中每个处于 `VBadOdd` 上方的有限位点，子群的拉回等于 Tate 图线。定理在 `c = K.c` 处，从 Legendre 存在定理选择见证，再取它与 `1` 的最大值作为 `C₀`。该常数满足使用 `hmain` 所需的两个条件。[Vélu 谓词](../../../../Solutions/Source_TripodCyclicBoundOdd.lean#L177) · [图线谓词](../../../../Solutions/Source_TripodCyclicBoundOdd.lean#L145) · [常数选取](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound.lean#L30)
- 结论 (4) 适用于 `x ∈ K.set ∩ ptLE d` 和素数 `ℓ ≥ 7`。它假设曲线有阶为 `ℓ` 的 Galois 稳定几何子群，并且对每个 `w ∈ (P.localData x).bad`，都有 `ℓ ∤ (P.localData x).hv w`。局部定理由这个不整除条件给出所需的图线等式。证明将 (3) 除以六，再用 `h(x) − h₂(x) ≥ 0` 和 `log ℓ ≥ 0` 比较系数。[循环子群谓词](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts.lean#L24) · [局部证明](../../../../Solutions/Source_TripodCyclicLocal.lean#L256) · [循环子群定理](../../../../Solutions/Source_TripodCyclicBoundFromSource.lean#L28)

## 日本語

- `exists_torsion_x_bound_from_source` は、(1) を一様に満たす実定数 `A, B ≥ 0` の存在を示す。対象は任意の複素楕円 Weierstrass 曲線 `W`、自然数 `N ≥ 1`、および `N • (x, y) = 0` を満たす非特異なアフィン点 `(x, y)` である。`b₂(W)`、`Δ(W)`、`j(W)` は通常の Weierstrass 不変量である。証明はモジュラー `j` 関数の全射性、格子曲線の加法群としての一意化、標準基本領域上の二つの対数比較を用いる。二つの比較は変数変換の倍率と格子パラメータのノルムを評価する。[定理の型](../../../../Solutions/Source_TripodCyclicArch.lean#L25) · [証明](../../../../Solutions/Source_ReferenceHeightsTorsionBound.lean#L12) · [変数変換](../../../../Solutions/Source_ReferenceHeightsTorsionArchimedean.lean#L60)
- 任意の実数 `c` に対し、`legendre_torsion_x_le_from_source` は (2) を一様に満たす実数 `C ≥ 0` を与える。`|log ‖λ‖| ≤ c` と `|log ‖λ − 1‖| ≤ c` を満たす複素数 `λ` と、楕円曲線 `W = legendre λ` をとる。`W` 上の非特異なアフィン点 `(a, b)` の `N ≥ 1` 倍が零点なら、(2) が成り立つ。証明は `exp(c)` を用いて判別式、`j` 不変量、座標の平行移動量を上から評価する。[Legendre の述語](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound.lean#L23) · [特殊化の証明](../../../../Solutions/Source_TripodCyclicArch.lean#L86) · [存在定理](../../../../Solutions/Source_ReferenceHeightsTorsionBound.lean#L22)
- `cyclicBoundOdd_of_mainBound` は Vélu の評価を明示的な仮定 `hmain` として受け取る。`LegendreTorsionXBound K.c C` を満たすすべての実数 `C ≥ 1` に対し、この仮定は `CyclicMainBoundHyp P K C` を与える。選んだ `C₀` でこの述語を適用すると、`x ∈ K.set`、奇素数 `ℓ`、位数 `ℓ` の Galois 安定な幾何学的部分群に対して (3) を得る。この述語は、`ℓ`-捩れ点体の `VBadOdd` 上の各素点で、部分群の引き戻しが Tate のグラフ直線に等しいと仮定する。定理は `c = K.c` で Legendre の存在定理から値を選び、その値と `1` の最大値を `C₀` とする。この `C₀` は `hmain` の適用に必要な二つの条件を満たす。[Vélu の述語](../../../../Solutions/Source_TripodCyclicBoundOdd.lean#L177) · [グラフ直線の述語](../../../../Solutions/Source_TripodCyclicBoundOdd.lean#L145) · [定数の選択](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound.lean#L30)
- 結論 (4) は `x ∈ K.set ∩ ptLE d` と素数 `ℓ ≥ 7` に対して成り立つ。曲線が位数 `ℓ` の Galois 安定な幾何学的部分群をもち、すべての `w ∈ (P.localData x).bad` で `ℓ ∤ (P.localData x).hv w` であると仮定する。局所定理はこの割り切れないという条件から、必要なグラフ直線との一致を与える。証明は (3) を 6 で割り、`h(x) − h₂(x) ≥ 0` および `log ℓ ≥ 0` を用いて係数を比較する。[巡回部分群の述語](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CurveFacts.lean#L24) · [局所定理の証明](../../../../Solutions/Source_TripodCyclicLocal.lean#L256) · [巡回部分群の定理](../../../../Solutions/Source_TripodCyclicBoundFromSource.lean#L28)

## MCP-CI review / 审查 / 監査

`ci-021929-7709d914` completed in exclusive mode with exit code 0 and an empty diagnostics list. The review listed exactly `propext`, `Classical.choice`, and `Quot.sound` for each of the three theorems above. It reported the same axioms for `latticePointMap_add` and `latticePointUniformization`. [Review source](../../../../.local/adaptation/b1-curve-field-arithmetic-20261118/ReviewHeightsTorsionBound.lean#L9) · [Receipt](../../../../.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-021929-7709d914-result.json)

审查任务 `ci-021929-7709d914` 以独占模式完成，退出码为 0，诊断列表为空。以上三个定理和格点映射的加法及一致化定理的全部公理依赖均为 `propext`、`Classical.choice` 和 `Quot.sound`。

監査ジョブ `ci-021929-7709d914` は排他モードで終了し、終了コードは 0、診断一覧は空である。上記の三定理と、格子点写像の加法性および一意化の定理の公理依存は、いずれも `propext`、`Classical.choice`、`Quot.sound` である。
