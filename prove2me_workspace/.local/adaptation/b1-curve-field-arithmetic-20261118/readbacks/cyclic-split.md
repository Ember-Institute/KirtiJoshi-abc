# The cyclic bound away from `2`

## Formulas / 公式 / 式

`h(x) = P.h x`, `h₂(x) = (P.localData x).heightEq 2`.

```text
(ℓ − 1)/4  · (h(x) − h₂(x)) ≤ 10 log ℓ + 2 log(32 C₀) + 6 K.c + 4 log 4
(ℓ − 2)/24 · (h(x) − h₂(x)) ≤  2 log ℓ + cyclicConst K (torsionConst K.c harch)

cyclicConst K C₀ = (2 log(32 C₀) + 6 K.c + 4 log 4)/6
```

## English

- `legendre_torsion_x_le c` asks for a real `C₀ ≥ 0` that satisfies `LegendreTorsionXBound c C₀`. For any complex `λ` with `|log ‖λ‖| ≤ c` and `|log ‖λ − 1‖| ≤ c`, consider an elliptic Weierstrass curve `W = legendre λ`. If `N ≥ 1` annihilates a nonsingular affine point `(a,b)` on `W`, then `‖a‖ ≤ C₀ N²`. The definition `torsionConst c harch` takes the maximum of `1` and the witness chosen from `harch`. The lemmas `one_le_torsionConst` and `torsionConst_spec` give the lower bound `1` and preserve the torsion-coordinate estimate.
- `cyclicLocalGraphLine P` asks for `CyclicLocalGraphLineHyp P`. Fix a point `x`, an odd prime `ℓ`, and a Galois-stable subgroup `H` of order `ℓ` on the geometric points of the curve. Use the mod-`ℓ` representation data `R = P.modRep x ℓ hℓ`. Let `w` be a finite place of `R.torsionField` over `VBadOdd`. Let `v` be the place below `w` in the curve's base field. If `ℓ ∤ ordᵥ(qᵥ)`, the predicate identifies the pullback `H.comap R.bcK` with the odd Tate family's graph line at `w`. The places in `VBadOdd` have odd residue characteristic. At least one base-field place lies over each of them. The curve has multiplicative reduction at all those base-field places.
- `Cyclic.main_bound` asks for the Vélu estimate in the first formula. It takes `x ∈ K.set` and the same odd-prime and subgroup conditions. It requires the graph-line equality at every `w` over `VBadOdd`, packaged as `IsGraphLineOdd`. Its archimedean inputs are `1 ≤ C₀` and `LegendreTorsionXBound K.c C₀`.
- `cyclicBoundOdd_of_source` takes `harch` at `c = K.c`, the local predicate `hlocal`, and `hmain` giving `CyclicMainBoundHyp P K C₀` for each constant with the two archimedean properties. It applies `hmain` at `torsionConst K.c harch` and combines it with `hlocal` through `cyclicBoundOdd_of_isogeny`. The result is `CyclicBoundOddHyp P K d` with the constant in the second formula. It applies for `x ∈ K.set ∩ ptLE d`, prime `ℓ ≥ 7`, and existence of a Galois-stable subgroup of order `ℓ`. It also assumes that `ℓ` divides none of the `(P.localData x).hv` values on `(P.localData x).bad`. The composition uses this condition to obtain the graph-line equality at each selected place. It divides the Vélu estimate by six and compares the coefficients using the nonnegativity of the height away from `2` and of `log ℓ`.
- `cyclicBoundOdd` states that same result with `harch` specialized to `legendre_torsion_x_le K.c`. The four declarations `legendre_torsion_x_le`, `cyclicLocalGraphLine`, `Cyclic.main_bound`, and `cyclicBoundOdd` each have a `sorry` body. The solution `cyclicBoundOdd_of_source` composes its explicit hypotheses.

## 中文

- `legendre_torsion_x_le c` 要求存在实数 `C₀ ≥ 0` 满足 `LegendreTorsionXBound c C₀`。对满足 `|log ‖λ‖| ≤ c` 和 `|log ‖λ − 1‖| ≤ c` 的复数 `λ`，取椭圆 Weierstrass 曲线 `W = legendre λ`。若 `N ≥ 1` 且 `W` 上的非奇异仿射点 `(a,b)` 被 `N` 消去，则有 `‖a‖ ≤ C₀ N²`。`torsionConst c harch` 取 `1` 与从 `harch` 选出见证的较大者。`one_le_torsionConst` 和 `torsionConst_spec` 分别给出下界 `1` 和挠点坐标估计。
- `cyclicLocalGraphLine P` 的目标是 `CyclicLocalGraphLineHyp P`。固定点 `x`、奇素数 `ℓ` 和曲线几何点上阶为 `ℓ` 的 Galois 稳定子群 `H`。设 `w` 为 `ℓ`-挠点域中位于 `VBadOdd` 上方的位点，`v` 为下方的曲线基域位点。若 `ℓ ∤ ordᵥ(qᵥ)`，该谓词给出拉回 `H.comap R.bcK` 等于奇位点 Tate 族在 `w` 处的图线。`VBadOdd` 由剩余特征为奇数的模域位点组成，每个位点上方至少有一个基域位点，且曲线在上方所有基域位点均有乘法约化。
- `Cyclic.main_bound` 的目标是第一式的 Vélu 估计。它要求 `x ∈ K.set`，同样要求奇素数 `ℓ` 和上述子群 `H`。`IsGraphLineOdd` 要求 `VBadOdd` 上方所有 `w` 都满足图线等式。阿基米德输入为 `1 ≤ C₀` 和 `LegendreTorsionXBound K.c C₀`。
- `cyclicBoundOdd_of_source` 接收 `c = K.c` 处的 `harch`、局部谓词 `hlocal`，以及对满足两个阿基米德条件的每个常数给出 `CyclicMainBoundHyp P K C₀` 的 `hmain`。它将 `hmain` 用于 `torsionConst K.c harch`，再经 `cyclicBoundOdd_of_isogeny` 与 `hlocal` 合用。所得 `CyclicBoundOddHyp P K d` 使用第二式中的常数，适用于 `x ∈ K.set ∩ ptLE d`、素数 `ℓ ≥ 7`，且存在阶为 `ℓ` 的 Galois 稳定子群。它还要求 `ℓ` 不整除 `(P.localData x).bad` 中任一位点的 `(P.localData x).hv`。证明用该条件得到各所选位点的图线等式，再将 Vélu 估计除以六，利用除去 `2` 处贡献的高度和 `log ℓ` 的非负性比较系数。
- `cyclicBoundOdd` 把结果中的 `harch` 取为 `legendre_torsion_x_le K.c`。`legendre_torsion_x_le`、`cyclicLocalGraphLine`、`Cyclic.main_bound` 和 `cyclicBoundOdd` 这四个声明的证明体均为 `sorry`。`cyclicBoundOdd_of_source` 组合其显式假设。

## 日本語

- `legendre_torsion_x_le c` の目標は、`LegendreTorsionXBound c C₀` を満たす実数 `C₀ ≥ 0` の存在を示すことである。`|log ‖λ‖| ≤ c` と `|log ‖λ − 1‖| ≤ c` を満たす複素数 `λ` に対し、楕円 Weierstrass 曲線 `W = legendre λ` をとる。`N ≥ 1` とし、`W` 上の非特異なアフィン点 `(a,b)` の `N` 倍が零点なら、`‖a‖ ≤ C₀ N²` を得る。`torsionConst c harch` は `1` と `harch` から選んだ値の最大値をとる。`one_le_torsionConst` と `torsionConst_spec` は、それぞれ下限 `1` と捩れ点の座標の評価を与える。
- `cyclicLocalGraphLine P` の目標は `CyclicLocalGraphLineHyp P` である。点 `x`、奇素数 `ℓ`、曲線の幾何学的点の群における Galois 安定部分群 `H` をとり、その位数を `ℓ` とする。`w` を `ℓ`-捩れ点体の `VBadOdd` 上の素点、`v` をその下にある曲線の基礎体の素点とする。`ℓ ∤ ordᵥ(qᵥ)` なら、引き戻し `H.comap R.bcK` は `w` における奇素点の Tate 族のグラフ直線に等しい。`VBadOdd` は剰余標数が奇数のモジュライ体の素点からなる。各素点の上には基礎体の素点が少なくとも一つあり、曲線はそのすべてで乗法的還元をもつ。
- `Cyclic.main_bound` の目標は第1式の Vélu 評価である。`x ∈ K.set` と同じ奇素数の条件および部分群 `H` の条件を仮定する。`IsGraphLineOdd` により、`VBadOdd` 上のすべての `w` でグラフ直線との一致を要求する。アルキメデス的な入力は `1 ≤ C₀` と `LegendreTorsionXBound K.c C₀` である。
- `cyclicBoundOdd_of_source` は、`c = K.c` における `harch`、局所述語 `hlocal`、および二つのアルキメデス的条件を満たす各定数について `CyclicMainBoundHyp P K C₀` を与える `hmain` を受け取る。`hmain` を `torsionConst K.c harch` で適用し、`cyclicBoundOdd_of_isogeny` で `hlocal` と組み合わせる。得られる `CyclicBoundOddHyp P K d` は第2式の定数を用いる。第2式は `x ∈ K.set ∩ ptLE d`、素数 `ℓ ≥ 7`、位数 `ℓ` の Galois 安定部分群の存在のもとで成り立つ。さらに `(P.localData x).bad` の各素点で `(P.localData x).hv` が `ℓ` で割り切れないことを仮定する。この条件から各素点でグラフ直線との一致を得る。Vélu 評価を 6 で割り、`2` での寄与を除いた高さと `log ℓ` の非負性を用いて係数を比較する。
- `cyclicBoundOdd` は、結果の `harch` を `legendre_torsion_x_le K.c` に特殊化したものである。`legendre_torsion_x_le`、`cyclicLocalGraphLine`、`Cyclic.main_bound`、`cyclicBoundOdd` の四つの宣言の証明本体は `sorry` である。`cyclicBoundOdd_of_source` は明示した仮定を組み合わせる。

[Legendre torsion predicate and choice](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_CyclicTorsionBound.lean:23) · [Archimedean obligation](/home/admin-wsl/Coq/abc/prove2me_workspace/Theorems/Thm_AbcAdaptation_Tripod_legendre_torsion_x_le.lean:16) · [Local obligation](/home/admin-wsl/Coq/abc/prove2me_workspace/Theorems/Thm_AbcAdaptation_Tripod_cyclicLocalGraphLine.lean:17) · [Vélu obligation](/home/admin-wsl/Coq/abc/prove2me_workspace/Theorems/Thm_AbcAdaptation_Tripod_Cyclic_main_bound.lean:20) · [Final obligation](/home/admin-wsl/Coq/abc/prove2me_workspace/Theorems/Thm_AbcAdaptation_Tripod_cyclicBoundOdd.lean:17) · [Conditional composition](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicBoundFromSource.lean:18)
