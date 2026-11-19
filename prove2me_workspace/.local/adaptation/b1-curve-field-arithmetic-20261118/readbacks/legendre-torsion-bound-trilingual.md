# `legendre_torsion_x_le_of_complex`

```text
‖x + b₂(W)/12‖⁶
  ≤ A · ‖Δ(W)‖ · max(‖j(W)‖, 1)
      · (2N² + B · (log(max(‖j(W)‖, exp(1))) + 1)²)⁶

E   = exp(c)
J   = 256 · (E² + E + 1)³ · E⁴
M   = A · 16 · E⁴ · max(J, 1)
Bⱼ  = B · (log(max(J, exp(1))) + 1)²
C₀  = max(1, M) · (2 + Bⱼ) + (1 + E)/3
```

## English

- `ComplexTorsionXBound` states that there are real constants `A, B ≥ 0` that work uniformly in the first inequality. It quantifies over all elliptic Weierstrass curves `W/ℂ`, all natural `N ≥ 1`, and all nonsingular affine points `(x,y)` with `N • (x,y) = 0`. The pinned statement is `Heights.exists_torsion_x_bound` in `Heights/TorsionArchimedean.lean` at `721496ca4c158e511d25d8ccf6bfe8503eda73c1`. The Legendre specialization comes from `Iut/Tripod/CyclicArch.lean` at `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`.
- `legendre_torsion_x_le_of_complex` constructs the displayed `C₀ ≥ 0` from `A, B` and any real `c`. For every `λ ∈ ℂ` with `|log ‖λ‖| ≤ c` and `|log ‖λ − 1‖| ≤ c`, take `W = legendre λ` with an ellipticity instance. This gives `λ ≠ 0, 1`. The logarithm bounds put both norms between `1/E` and `E`. The proof bounds `‖W.j‖` by `J`, `‖W.Δ‖` by `16E⁴`, and `‖W.b₂/12‖` by `(1 + E)/3`. It uses `M ≤ max(1, M)⁶` to remove the sixth power. It then uses the triangle inequality and `N² ≥ 1` to obtain `‖x‖ ≤ C₀ N²`.
- The parent sketch for `legendre_torsion_x_le` directly applies `legendre_torsion_x_le_of_complex` to `Reference.Heights.exists_torsion_x_bound`. The cyclic bound calls `torsionConst K.c (legendre_torsion_x_le K.c)`. With `harch := legendre_torsion_x_le K.c`, the chosen constant is `max(1, Classical.choose harch)`. The lower bound `1` and the Legendre torsion bound both apply to this constant, which also goes into `cyclicConst`. The theorem declarations of `exists_torsion_x_bound` and `legendre_torsion_x_le` currently have `sorry` bodies. The specialization in `Source_TripodCyclicArch.lean` takes `ComplexTorsionXBound` as an explicit input.

## 中文

- `ComplexTorsionXBound` 表述实常数的存在性，要求 `A, B ≥ 0` 统一满足第一式。它遍历所有复椭圆 Weierstrass 曲线 `W/ℂ`、所有自然数 `N ≥ 1`，以及满足 `N • (x,y) = 0` 的所有非奇异仿射点 `(x,y)`。一般界固定为 `Heights/TorsionArchimedean.lean` 在版本 `721496ca4c158e511d25d8ccf6bfe8503eda73c1` 的 `Heights.exists_torsion_x_bound`。Legendre 特化对应 `Iut/Tripod/CyclicArch.lean` 的版本 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`。
- `legendre_torsion_x_le_of_complex` 对任意实数 `c`，从 `A, B` 构造上式中的 `C₀ ≥ 0`。对满足 `|log ‖λ‖| ≤ c` 和 `|log ‖λ − 1‖| ≤ c` 的每个复数 `λ`，取椭圆曲线 `W = legendre λ`。椭圆性给出 `λ ≠ 0, 1`，两个对数条件将对应范数限制在 `1/E` 和 `E` 之间。证明分别用 `J`、`16E⁴` 和 `(1 + E)/3` 控制 `‖W.j‖`、`‖W.Δ‖` 和 `‖W.b₂/12‖`。由 `M ≤ max(1, M)⁶` 去掉六次方，再用三角不等式和 `N² ≥ 1` 得到 `‖x‖ ≤ C₀ N²`。
- 父定理 `legendre_torsion_x_le` 的草图直接将 `legendre_torsion_x_le_of_complex` 应用于 `Reference.Heights.exists_torsion_x_bound`。循环界调用 `torsionConst K.c (legendre_torsion_x_le K.c)`，令 `harch := legendre_torsion_x_le K.c`，则所选常数为 `max(1, Classical.choose harch)`。同一常数满足下界 `1` 和 Legendre 挠点界，并用于 `cyclicConst`。`exists_torsion_x_bound` 和 `legendre_torsion_x_le` 的定理声明目前均以 `sorry` 为证明体。`Source_TripodCyclicArch.lean` 的特化定理显式接收 `ComplexTorsionXBound`。

## 日本語

- `ComplexTorsionXBound` は、第1式を一様に満たす実定数 `A, B ≥ 0` の存在を述べる。すべての複素楕円 Weierstrass 曲線 `W/ℂ`、すべての自然数 `N ≥ 1`、および `N • (x,y) = 0` を満たすすべての非特異なアフィン点 `(x,y)` が対象である。一般の評価は、改訂 `721496ca4c158e511d25d8ccf6bfe8503eda73c1` の `Heights/TorsionArchimedean.lean` にある `Heights.exists_torsion_x_bound` に対応する。Legendre 族への特殊化は、改訂 `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8` の `Iut/Tripod/CyclicArch.lean` に対応する。
- `legendre_torsion_x_le_of_complex` は、`A, B` と任意の実数 `c` から上の `C₀ ≥ 0` を構成する。`|log ‖λ‖| ≤ c` と `|log ‖λ − 1‖| ≤ c` を満たす各複素数 `λ` に対し、楕円曲線 `W = legendre λ` をとる。楕円曲線であることから `λ ≠ 0, 1` を得る。二つの対数の条件から、対応するノルムは `1/E` 以上 `E` 以下である。証明は `‖W.j‖`、`‖W.Δ‖`、`‖W.b₂/12‖` をそれぞれ `J`、`16E⁴`、`(1 + E)/3` で上から抑える。`M ≤ max(1, M)⁶` を使って6乗を外し、三角不等式と `N² ≥ 1` から `‖x‖ ≤ C₀ N²` を得る。
- 親定理 `legendre_torsion_x_le` のスケッチは、`legendre_torsion_x_le_of_complex` を `Reference.Heights.exists_torsion_x_bound` に直接適用する。巡回部分群の評価では `torsionConst K.c (legendre_torsion_x_le K.c)` を用いる。`harch := legendre_torsion_x_le K.c` とすると、選ぶ定数は `max(1, Classical.choose harch)` である。同じ定数が下限 `1` と Legendre 族の捩れ点の評価を満たし、`cyclicConst` にも入る。`exists_torsion_x_bound` と `legendre_torsion_x_le` の定理宣言の証明本体は、現在 `sorry` である。`Source_TripodCyclicArch.lean` の特殊化は `ComplexTorsionXBound` を明示的な入力とする。

[General bound and its pinned reference](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicArch.lean:23) · [Legendre witness](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicArch.lean:86) · [Parent sketch](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Sketch_Tripod_legendre_torsion_x_le.lean:8) · [General theorem target](/home/admin-wsl/Coq/abc/prove2me_workspace/Theorems/Thm_AbcAdaptation_Reference_Heights_exists_torsion_x_bound.lean:9) · [Legendre theorem target](/home/admin-wsl/Coq/abc/prove2me_workspace/Theorems/Thm_AbcAdaptation_Tripod_legendre_torsion_x_le.lean:16) · [Constant choice](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound.lean:29) · [Cyclic consumer](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Sketch_Tripod_cyclicBoundOdd.lean:19)
