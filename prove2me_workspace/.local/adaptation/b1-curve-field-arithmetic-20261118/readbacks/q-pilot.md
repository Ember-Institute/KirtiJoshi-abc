# `EllipticCurveData.logQ_eq`

```lean
let D := C.thetaData CA TI hℓ h7 R hsl hP2 hP5 TF anab hcore

(C.qPilotInputs CA TI hℓ h7 R hsl hP2 hP5 TF anab hcore).qPilot.logQ =
  (C.localHeightData CA TI).heightOther 2 ℓ
```

```text
F = C.F
p_w = residueChar w
f_w = inertDeg F w
S = {w ∈ C.badAll | p_w ≠ 2 ∧ p_w ≠ ℓ}

weight(w) = f_w / [F : ℚ]
logQ = (∑_{w ∈ S} ord_w(q_w) · f_w · log p_w) / [F : ℚ]
```

## English

- For initial Θ-data `D`, `QPilotInputs D` requires finiteness of `badPlacesOver D.F D.E D.VBad` and positive residue degree at every finite place of `D.F`. The construction enumerates exactly that set as `badFinset`. Its real-valued weight is `(inertDeg D.F w : ℝ) / Module.finrank ℚ D.F`. The numerator `f_w` is the residue-field degree over the field with `p_w` elements. Positivity follows from the positive residue degree and the positive absolute field degree.
- For `D` assembled from `C`, `D.VBad = C.VBadOf ℓ`. The lemma `badPlacesOver_VBadOf` identifies the resulting set `S` with exactly the finite places of multiplicative reduction whose residue characteristic differs from both `2` and `ℓ`. The proof of `qPilotInputs` uses `CA.badAll_finite` for finiteness and `CA.inertDeg_pos` for positivity.
- At each `w ∈ S`, `D.prime.qOrder` reduces to the normalized Tate parameter order `TI.qOrder w hw`, where `hw : w ∈ C.badAll`. This is also the value of `(C.localHeightData CA TI).hv w`. The proof matches the two finite sums term by term and moves division by `[F : ℚ]` inside the sum. This gives `logQ_eq` as the height component supported away from residue characteristics `2` and `ℓ`.

## 中文

- 对初始 Θ 数据 `D`，`QPilotInputs D` 要求 `badPlacesOver D.F D.E D.VBad` 有限，且 `D.F` 的每个有限位点的剩余次数为正。构造所得 `badFinset` 恰好枚举这个集合。实数权重为 `(inertDeg D.F w : ℝ) / Module.finrank ℚ D.F`。分子 `f_w` 是位点剩余域在 `p_w` 元域上的次数。剩余次数和基域的绝对次数均为正，故权重为正。
- 对由 `C` 组装的 `D`，有 `D.VBad = C.VBadOf ℓ`。`badPlacesOver_VBadOf` 表明所得集合 `S` 恰好由满足乘法约化且剩余特征既不等于 `2` 也不等于 `ℓ` 的有限位点组成。`qPilotInputs` 由 `CA.badAll_finite` 得到有限性，并由 `CA.inertDeg_pos` 得到剩余次数的正性。
- 对 `w ∈ S`，`D.prime.qOrder` 展开为归一化 Tate 参数阶 `TI.qOrder w hw`，其中 `hw : w ∈ C.badAll`。这也是 `(C.localHeightData CA TI).hv w` 的值。证明对齐两个有限求和集合，并把分母 `[F : ℚ]` 分配到各项，从而得到 `logQ_eq`。右端是去掉剩余特征 `2` 和 `ℓ` 两处贡献后的高度分量。

## 日本語

- 初期 Θ データ `D` に対し、`QPilotInputs D` は `badPlacesOver D.F D.E D.VBad` の有限性と、`D.F` のすべての有限素点における剰余次数の正値性を要求する。`badFinset` はこの集合を過不足なく列挙する。実数値の重みは `(inertDeg D.F w : ℝ) / Module.finrank ℚ D.F` である。分子 `f_w` は剰余体の `p_w` 元体上の次数である。剰余次数と基礎体の絶対次数がともに正であるため、重みも正になる。
- `C` から構成した `D` では `D.VBad = C.VBadOf ℓ` である。`badPlacesOver_VBadOf` により、集合 `S` は曲線が乗法的還元をもち、剰余標数が `2` と `ℓ` のいずれとも異なる有限素点全体に等しい。`qPilotInputs` は有限性に `CA.badAll_finite` を、剰余次数の正値性に `CA.inertDeg_pos` を用いる。
- `w ∈ S` では、`D.prime.qOrder` を展開すると、正規化された Tate パラメータの位数 `TI.qOrder w hw` になる。ここで `hw : w ∈ C.badAll` である。これは `(C.localHeightData CA TI).hv w` の値にも等しい。証明は二つの有限和の添字集合を一致させ、分母 `[F : ℚ]` を各項に分配する。こうして `logQ_eq` は、剰余標数 `2` と `ℓ` の寄与を除いた高さ成分との等式を与える。

[q-pilot construction and proofs](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutQPilot.lean:28) · [Definition of logQ](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_LeftHandSide.lean:110) · [Bad-set cutoff](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_SL2ImageLocalTate.lean:33) · [Local height inputs](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalHeightDataAssembly.lean:39) · [Height component](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Implication_PrimeSelection_HeightParts.lean:31)
