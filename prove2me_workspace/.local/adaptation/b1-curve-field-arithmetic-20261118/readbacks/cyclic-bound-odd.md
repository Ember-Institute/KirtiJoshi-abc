# `cyclicBoundOdd_of_isogeny`

## Formulas / 公式 / 式

`h(x) = P.h x`, `h₂(x) = (P.localData x).heightEq 2`.

```text
(ℓ − 1)/4  · (h(x) − h₂(x)) ≤ 10 log ℓ + 6 cyclicConst K C₀
(ℓ − 2)/24 · (h(x) − h₂(x)) ≤  2 log ℓ +   cyclicConst K C₀
cyclicConst K C₀ = (2 log(32 C₀) + 6 K.c + 4 log 4)/6
```

## English

- `CyclicLocalGraphLineHyp P` assumes the following for each point `x`, odd prime `ℓ`, and Galois-stable subgroup `H` of order `ℓ`. Let `w` be a finite place of the `ℓ`-torsion field over `VBadOdd`. Let `v` be the place below it in the curve's base field. If `ℓ` does not divide the Tate parameter order at `v`, the pullback `H.comap R.bcK` is the Tate graph line at `w`. The set `VBadOdd` consists of finite places of the field of moduli with odd residue characteristic. At least one base-field place lies above each member. The curve has multiplicative reduction at every base-field place above a member.
- `CyclicMainBoundHyp P K C₀` assumes the Vélu estimate in the first formula for `x ∈ K.set`, an odd prime `ℓ`, and such a subgroup `H`. It requires the graph-line equality at every `w` over `VBadOdd` through `IsGraphLineOdd`. The estimate uses the fixed archimedean torsion constant `C₀`.
- Given both inputs, `cyclicBoundOdd_of_isogeny` proves `CyclicBoundOddHyp`, the second bound, for `x ∈ K.set ∩ ptLE d` and prime `ℓ ≥ 7`. It assumes a Galois-stable subgroup of order `ℓ` and nondivisibility of the local height exponent by `ℓ` at every place in `(P.localData x).bad`. The condition `ptLE d` bounds the degree of the point by `d`. The proof transfers nondivisibility to the Tate parameter order at the place below each selected `w`. This gives the graph-line equality. It then divides the Vélu estimate by six and compares the coefficients using the nonnegativity of the height away from 2 and of `log ℓ`.

## 中文

- `CyclicLocalGraphLineHyp P` 对每个点 `x`、奇素数 `ℓ` 和阶为 `ℓ` 的 Galois 稳定子群 `H` 作如下假设。设 `w` 是 `ℓ`-挠点域中位于 `VBadOdd` 上方的有限位点，`v` 是曲线基域中位于 `w` 下方的位点。若 `ℓ` 不整除 `v` 处 Tate 参数的阶，则拉回 `H.comap R.bcK` 等于 `w` 处的 Tate 图线。`VBadOdd` 由剩余特征为奇数的模域有限位点组成，每个位点上方至少有一个基域位点，且曲线在上方所有基域位点均为乘法约化。
- `CyclicMainBoundHyp P K C₀` 对 `x ∈ K.set`、奇素数 `ℓ` 和上述子群 `H` 假设第一式的 Vélu 估计。它通过 `IsGraphLineOdd` 要求 `VBadOdd` 上方每个 `w` 都满足图线等式，并使用固定的阿基米德挠点常数 `C₀`。
- 在这两个输入下，`cyclicBoundOdd_of_isogeny` 对 `x ∈ K.set ∩ ptLE d` 和素数 `ℓ ≥ 7` 证明第二式所给出的界 `CyclicBoundOddHyp`。它要求存在一个阶为 `ℓ` 的 Galois 稳定子群，且 `ℓ` 不整除 `(P.localData x).bad` 中任一位点的局部高度指数。`ptLE d` 表示点的次数至多为 `d`。证明将不可整除条件用于每个所选 `w` 下方位点的 Tate 参数阶，从而得到图线等式。然后将 Vélu 估计除以六，利用除去 `2` 处贡献后的高度和 `log ℓ` 的非负性比较系数。

## 日本語

- `CyclicLocalGraphLineHyp P` は、各点 `x`、奇素数 `ℓ`、位数 `ℓ` の Galois 安定部分群 `H` について、次を仮定する。`w` を `ℓ`-捩れ点体の `VBadOdd` 上の有限素点とし、`v` を `w` の下にある曲線の基礎体の素点とする。`v` における Tate パラメータの位数が `ℓ` で割り切れなければ、引き戻し `H.comap R.bcK` は `w` における Tate のグラフ直線に等しい。`VBadOdd` は剰余標数が奇数のモジュライ体の有限素点からなり、各素点の上には基礎体の素点が少なくとも一つあり、そのすべてで曲線が乗法的還元をもつ。
- `CyclicMainBoundHyp P K C₀` は、`x ∈ K.set`、奇素数 `ℓ`、および上記の部分群 `H` に対し、第1式の Vélu 評価を仮定する。`IsGraphLineOdd` は `VBadOdd` 上のすべての `w` におけるグラフ直線との一致を要求する。評価には固定したアルキメデス的な捩れ点定数 `C₀` を用いる。
- 二つの入力のもとで、`cyclicBoundOdd_of_isogeny` は `x ∈ K.set ∩ ptLE d` と素数 `ℓ ≥ 7` に対し、第2式の評価 `CyclicBoundOddHyp` を証明する。位数 `ℓ` の Galois 安定部分群が存在し、`(P.localData x).bad` の各素点の局所高さの指数が `ℓ` で割り切れないと仮定する。`ptLE d` は点の次数が `d` 以下であることを表す。証明では、各 `w` の下の素点で Tate パラメータの位数が `ℓ` で割り切れないことを示し、グラフ直線との一致を得る。その後、Vélu 評価を 6 で割り、2 での寄与を除いた高さと `log ℓ` の非負性を用いて係数を比較する。

## Verification / 验收 / 検証

Artifact `ci-020947-cd31bcd2` and axiom review `ci-020957-a44be081` passed. The axiom review reports `propext`, `Classical.choice`, and `Quot.sound` for the conditional theorem. [Source](../../../../Solutions/Source_TripodCyclicBoundOdd.lean#L188) · [Artifact receipt](../receipts/continued-ci-020947-cd31bcd2-result.json) · [Review receipt](../receipts/continued-ci-020957-a44be081-result.json)
