# `EllipticCurveData.thetaData`

## English

- `thetaData` returns `InitialThetaData AG TG` for the input curve `C.E/C.F`, its chosen algebraic closure `C.Fbar`, and the moduli-field places `C.VBadOf ℓ`. These places have residue characteristic different from `2` and `ℓ`. Each has at least one place above it in `C.F`, and the curve has multiplicative reduction at every such place. It takes curve arithmetic `CA`, Tate inputs `TI`, and mod-`ℓ` representation data `R` for a prime `ℓ ≥ 7`. It assumes that the image of `R.rep` contains `SL₂(𝔽_ℓ)`, that `ℓ` divides none of the `TI.qOrder` values on `C.badAll`, and that some place of `C.badAll` has residue characteristic different from both `2` and `ℓ`. It also takes the Tate family `TF` over `R.torsionField`, the existence hypothesis `anab : AnabelianExistence AG TG`, and the core hypothesis `hcore`. The core hypothesis identifies the base change of `X_F/{±1}` as the core of the base change of `X_F` over each characteristic-zero extension of `F`.
- The constructor sets `global := C.globalData CA hP5` and `prime := C.primeData CA TI hℓ h7 R hsl hP2`. The latter preserves `ℓ` and `R.rep`, so the result’s torsion field `K` is definitionally the fixed field of `R.rep.ker` in `C.Fbar`. The `numberFieldK` field comes from `R.numberField_torsionField`. The `algebraModK` field is the canonical inclusion of `F_mod = ℚ(j(C.E))` into `K`. The `towerModK` field proves that this inclusion is the composition through `C.F`.
- The call to `anab.exists_data` passes the admissible prime data, the supplied `TF`, the global data, and `hcore`. Under the canonical algebra, it gives a witness `O : OrbicurveData ...` and `Nonempty (LocalThetaData ... O)` for that same `O`. The orbicurve data include `CKu`, `XKu`, their covering diagram, and the distinguished cusp `epsilon`. The local data include the valuation section and local conditions for `O`. The constructor chooses `orb := h.choose` and `localData := h.choose_spec.some`. It stores the same supplied family in `tate := TF`.
- For the assembled record `D`, `qPilotInputs` proves `QPilotInputs D`. It uses `CA` for finiteness of the selected bad places and positivity of residue degrees. The arithmetic uses `D.F`, `D.E`, `D.VBad`, and `D.prime.qOrder`. With weights `inertDeg D.F w / [D.F : ℚ]`, `logQ_eq` identifies the resulting `logQ` with the local height away from `2` and `ℓ`.

## 中文

- `thetaData` 为输入曲线 `C.E/C.F`、所选代数闭包 `C.Fbar` 及模域位点集 `C.VBadOf ℓ` 构造 `InitialThetaData AG TG`。所选模域位点的剩余特征既不等于 `2` 也不等于 `ℓ`。每个位点上方至少有一个 `C.F` 的位点，且曲线在上方各位点均有乘法约化。它接收曲线算术数据 `CA`、Tate 输入 `TI`，以及素数 `ℓ ≥ 7` 对应的模 `ℓ` 表示数据 `R`。它要求 `R.rep` 的像包含 `SL₂(𝔽_ℓ)`，`ℓ` 不整除 `C.badAll` 中任一位点的 `TI.qOrder`，且 `C.badAll` 中有一个位点的剩余特征既不等于 `2` 也不等于 `ℓ`。它还接收 `R.torsionField` 上的 Tate 族 `TF`、存在性假设 `anab : AnabelianExistence AG TG` 和核心条件 `hcore`。该核心条件要求在 `F` 的任意特征零扩域上，`X_F/{±1}` 的基变换是 `X_F` 的基变换的核心。
- 构造取 `global := C.globalData CA hP5` 和 `prime := C.primeData CA TI hℓ h7 R hsl hP2`。后者沿用 `ℓ` 与 `R.rep`，所以结果的挠点域 `K` 按定义等于 `C.Fbar` 中 `R.rep.ker` 的不动域。`numberFieldK` 来自 `R.numberField_torsionField`。`algebraModK` 取模域 `F_mod = ℚ(j(C.E))` 到 `K` 的典范嵌入。`towerModK` 证明该嵌入等于经过 `C.F` 的复合。
- 调用 `anab.exists_data` 时传入容许素数数据、给定的 `TF`、全局数据和 `hcore`。在典范代数结构下，它给出轨形曲线数据 `O : OrbicurveData ...`，并保证对应同一个 `O` 的 `LocalThetaData ... O` 非空。轨形曲线数据包含 `CKu`、`XKu`、覆盖图和指定尖点 `epsilon`。局部数据包含位点截面及关于 `O` 的局部条件。构造选择 `orb := h.choose` 和 `localData := h.choose_spec.some`，并把传入的同一个 `TF` 存为 `tate`。
- 对组装后的记录 `D`，`qPilotInputs` 证明 `QPilotInputs D`。它从 `CA` 得到所选坏位点的有限性和剩余次数的正性。计算使用 `D.F`、`D.E`、`D.VBad` 和 `D.prime.qOrder`。以 `inertDeg D.F w / [D.F : ℚ]` 为权重时，`logQ_eq` 证明所得 `logQ` 等于去掉 `2` 和 `ℓ` 处贡献的局部高度。

## 日本語

- `thetaData` は、入力の楕円曲線 `C.E/C.F`、選んだ代数閉包 `C.Fbar`、モジュライ体の素点集合 `C.VBadOf ℓ` から `InitialThetaData AG TG` を構成する。この集合の各素点の剰余標数は `2` と `ℓ` のいずれとも異なる。各素点の上には `C.F` の素点が少なくとも一つあり、曲線はそのすべてで乗法的還元をもつ。曲線の算術データ `CA`、Tate 入力 `TI`、素数 `ℓ ≥ 7` に対する mod `ℓ` 表現データ `R` を受け取る。`R.rep` の像が `SL₂(𝔽_ℓ)` を含み、`C.badAll` の各素点の `TI.qOrder` が `ℓ` で割り切れず、`C.badAll` に剰余標数が `2` と `ℓ` のいずれとも異なる素点があることを仮定する。さらに、`R.torsionField` 上の Tate 族 `TF`、存在仮定 `anab : AnabelianExistence AG TG`、コア条件 `hcore` を受け取る。このコア条件は、`F` の任意の標数 0 の拡大上で `X_F/{±1}` の基底変換が `X_F` の基底変換のコアになることを要求する。
- 構成では `global := C.globalData CA hP5` と `prime := C.primeData CA TI hℓ h7 R hsl hP2` を用いる。後者は `ℓ` と `R.rep` をそのまま用いるため、結果の捩れ点体 `K` は定義上、`C.Fbar` 内の `R.rep.ker` の固定体に等しい。`numberFieldK` には `R.numberField_torsionField` を用いる。`algebraModK` はモジュライ体 `F_mod = ℚ(j(C.E))` から `K` への標準的な埋め込みである。`towerModK` はこの埋め込みが `C.F` を経由する合成に等しいことを示す。
- `anab.exists_data` に許容素数データ、与えられた `TF`、大域データ、`hcore` を渡す。標準的な代数構造のもとで、オービ曲線データ `O : OrbicurveData ...` と、同じ `O` に対する `Nonempty (LocalThetaData ... O)` を得る。オービ曲線データには `CKu`、`XKu`、被覆図式、指定カスプ `epsilon` が入る。局所データには素点の切断と `O` に対する局所条件が入る。構成は `orb := h.choose` と `localData := h.choose_spec.some` を選び、入力と同じ `TF` を `tate` に格納する。
- 組み立てたレコード `D` に対し、`qPilotInputs` は `QPilotInputs D` を証明する。選んだ悪い素点の有限性と剰余次数の正値性には `CA` を用いる。計算には `D.F`、`D.E`、`D.VBad`、`D.prime.qOrder` を用いる。重みを `inertDeg D.F w / [D.F : ℚ]` とすると、`logQ_eq` は得られる `logQ` が `2` と `ℓ` での寄与を除いた局所高さに等しいことを示す。

## Lean

```lean
let P := C.primeData CA TI hℓ h7 R hsl hP2
have hmap : algebraMap ↥(fieldOfModuli C.F C.E) ↥P.torsionField =
    (algebraMap C.F ↥P.torsionField).comp (algebraMap ↥(fieldOfModuli C.F C.E) C.F) :=
  RingHom.ext fun _ => rfl
let G := C.globalData CA hP5
let h := anab.exists_data C.F C.E C.Fbar (C.VBadOf ℓ) P TF G hcore

-- Fields of the assembled InitialThetaData
prime := P
global := G
numberFieldK := R.numberField_torsionField
algebraModK := (fieldOfModuli C.F C.E).instAlgebraSubtypeMem
towerModK := IsScalarTower.of_algebraMap_eq' hmap
tate := TF
orb := h.choose
localData := h.choose_spec.some
```

[Constructor and existence interface](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutInitialThetaData.lean:26) · [InitialThetaData fields](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_Basic.lean:106) · [Admissible prime construction](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCurveThetaInputs.lean:50) · [q-pilot consumer](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutQPilot.lean:53) · [logQ definition](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_LeftHandSide.lean:110)
