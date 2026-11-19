# `ModEllRepData.tateFamily` and `TateFamily.ofStructures`

## English

- For a prime `ℓ ≠ 2`, `R.tateFamily` constructs `TateFamily C.E R.torsionField ℓ (C.VBadOf ℓ)`. Its field `K = R.torsionField` is the fixed field of `R.rep.ker` in `C.Fbar`. Each local structure is on the base change of `C.E` to `K_w`. The index `w` ranges over finite places of `K` above a member of `C.VBadOf ℓ`. These finite places of the field of moduli have residue characteristic different from `2` and `ℓ`. Each has a `C.F`-place above it, and the curve has multiplicative reduction at all such places.
- At each `w`, the construction gives `exists_sq_eq_neg_c₄_mul_c₆` the place conditions and the `ℓ`-torsion subgroup `R.TK` of `E(K)`. Its cardinality is `ℓ²` by `R.card_torsionBy_EK`. The resulting square root of the image of `−c₄(E)c₆(E)` in `K_w` supplies the split condition for `tateStructureOfBadPlace`. The constructor also uses `TateParameterUniformization.ofTateParameter` to give the uniformization on the local curve.
- `TateStructure.toJoshi` builds the main-library parameter from `S.t.q` and `S.t.norm_lt_one`. It copies the variable change `C`, its model equality `hC`, the additive equivalence `iso`, and the coordinate proofs `iso_x` and `iso_y`. `TateFamily.ofStructures` passes the converted structures to `JoshiTeich.ReferenceIut.TateFamily.ofStructures` and stores the input family in its own `S` field.
- The bridge takes `graphLine_galPlace` and `isCanonical_galPlace` from the main-library family. For each `σ ∈ Gal(K/C.F)`, the graph line at `σw`, pulled back to `E(K)`, is the image under `σ` of the pullback at `w`. Also, `σ(P)` is canonical at `σw` if and only if `P ∈ E(K)` is canonical at `w`. Both canonical predicates use the point map to the corresponding completion.

## 中文

- 对奇素数 `ℓ`，`R.tateFamily` 构造 `TateFamily C.E R.torsionField ℓ (C.VBadOf ℓ)`。其中 `K = R.torsionField` 是 `C.Fbar` 中 `R.rep.ker` 的不动域。局部结构位于 `C.E` 到 `K_w` 的基变换上。指标 `w` 遍历 `K` 中位于 `C.VBadOf ℓ` 某成员上方的有限位点。该集合中的模域有限位点具有既非 `2` 也非 `ℓ` 的剩余特征，每个位点上方均有 `C.F` 的位点，且曲线在上方所有 `C.F` 位点均有乘法约化。
- 在每个 `w`，构造把位点条件和 `E(K)` 的 `ℓ`-挠子群 `R.TK` 传给 `exists_sq_eq_neg_c₄_mul_c₆`。`R.card_torsionBy_EK` 给出该子群的基数 `ℓ²`。所得 `−c₄(E)c₆(E)` 在 `K_w` 中像的平方根为 `tateStructureOfBadPlace` 提供分裂条件。构造还用 `TateParameterUniformization.ofTateParameter` 给出局部曲线的一致化。
- `TateStructure.toJoshi` 用 `S.t.q` 和 `S.t.norm_lt_one` 构造主库的 Tate 参数，并沿用坐标变换 `C`、模型等式 `hC`、加法等价 `iso` 及坐标证明 `iso_x` 和 `iso_y`。`TateFamily.ofStructures` 将转换后的结构传给 `JoshiTeich.ReferenceIut.TateFamily.ofStructures`，并将输入族存入结果的 `S` 字段。
- 转换由主库的族提供 `graphLine_galPlace` 和 `isCanonical_galPlace`。对每个 `σ ∈ Gal(K/C.F)`，`σw` 处图线拉回 `E(K)` 后，等于 `w` 处图线的拉回在 `σ` 下的像。对 `P ∈ E(K)`，`σ(P)` 在 `σw` 处满足典范生成元条件，当且仅当 `P` 在 `w` 处满足该条件。两处条件均经点映射在相应的完备化中读取。

## 日本語

- 奇素数 `ℓ` に対して、`R.tateFamily` は `TateFamily C.E R.torsionField ℓ (C.VBadOf ℓ)` を構成する。`K = R.torsionField` は `C.Fbar` 内の `R.rep.ker` の固定体である。各局所構造は `C.E` を `K_w` に基底変換した曲線上にある。添字 `w` は `C.VBadOf ℓ` の元の上にある `K` の有限素点を走る。この集合の各モジュライ体の素点は剰余標数が `2` と `ℓ` のいずれとも異なり、その上に `C.F` の素点が少なくとも一つある。曲線はその上の `C.F` のすべての素点で乗法的還元をもつ。
- 各 `w` で、素点の条件と `E(K)` の `ℓ`-捩れ部分群 `R.TK` を `exists_sq_eq_neg_c₄_mul_c₆` に渡す。`R.card_torsionBy_EK` によってこの部分群の濃度は `ℓ²` である。こうして得られる `−c₄(E)c₆(E)` の `K_w` における像の平方根が、`tateStructureOfBadPlace` に必要な分裂条件を与える。局所曲線の一様化には `TateParameterUniformization.ofTateParameter` を用いる。
- `TateStructure.toJoshi` は `S.t.q` と `S.t.norm_lt_one` から主ライブラリの Tate パラメータを構成する。変数変換 `C`、モデルの等式 `hC`、加法同型 `iso`、座標の証明 `iso_x` と `iso_y` を引き継ぐ。`TateFamily.ofStructures` は変換した構造を `JoshiTeich.ReferenceIut.TateFamily.ofStructures` に渡し、入力の族を結果の `S` フィールドに格納する。
- 変換には主ライブラリの族の `graphLine_galPlace` と `isCanonical_galPlace` を用いる。各 `σ ∈ Gal(K/C.F)` に対し、`σw` におけるグラフ直線の `E(K)` への引き戻しは、`w` における引き戻しの `σ` による像に等しい。また、`P ∈ E(K)` に対し、`σ(P)` が `σw` で標準生成元の条件を満たすことと、`P` が `w` でその条件を満たすことは同値である。各条件は点の写像を通じて対応する完備化で判定する。

[Curve Tate family](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCurveTateFamily.lean:29) · [Tate family bridge](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTateFamilyBridge.lean:22) · [Fixed field](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_ModEllRepTorsionField.lean:24) · [Selected places](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean:55) · [Equivariance in the main library](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutCompat/Cor312/ThetaData/TateFamilyGalois.lean:236)
