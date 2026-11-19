# Source_ReferenceIutTowerLocalFacts.lean

## `wildConst` and `wildConst_eq_zero`

**English** — For natural numbers `ℓ` and `p`, let the base value be 12 when `p = 2`, 2 when `p = 3`, 1 when `p = 5`, and 0 otherwise. The natural number `wildConst ℓ p` is this base value plus 1 if `p = ℓ`, plus 0 otherwise. For every `ℓ, p : ℕ`, if `p ∉ {2, 3, 5, ℓ}`, then `wildConst ℓ p = 0`.

**中文** — 对任意自然数 `ℓ`、`p`，当 `p` 分别为 2、3、5 时，基础值分别为 12、2、1，其余情形为 0。自然数 `wildConst ℓ p` 等于基础值再加上 `p = ℓ` 时的 1，其余情形加 0。对任意 `ℓ, p : ℕ`，若 `p ∉ {2, 3, 5, ℓ}`，则 `wildConst ℓ p = 0`。

**日本語** — 任意の自然数 `ℓ` と `p` について、`p` が 2、3、5 のときの基準値をそれぞれ 12、2、1 とし、それ以外のときは 0 とする。自然数 `wildConst ℓ p` はこの基準値に、`p = ℓ` のときは 1、それ以外のときは 0 を加えた値である。任意の `ℓ, p : ℕ` について、`p ∉ {2, 3, 5, ℓ}` ならば `wildConst ℓ p = 0` である。

## The fields

**English** — Let `F` be a number field and `E` a Weierstrass curve over `F` with `E.IsElliptic`. Write `F_mod` for the subfield `ℚ(j(E))` of `F` and `F_tpd` for the subfield of `F` generated over `ℚ` by `j(E)` and the x-coordinates of the affine `F`-rational points of `E` killed by 2.

**中文** — 设 `F` 为数域，`E` 为 `F` 上满足 `E.IsElliptic` 的魏尔斯特拉斯曲线。记 `F_mod` 为 `F` 的子域 `ℚ(j(E))`，记 `F_tpd` 为 `F` 中由 `j(E)` 与 `E` 上被 2 消去的仿射 `F`-有理点的横坐标在 `ℚ` 上生成的子域。

**日本語** — `F` を数体とし、`E` を `E.IsElliptic` を満たす `F` 上のワイエルシュトラス曲線とする。`F_mod` を `F` の部分体 `ℚ(j(E))` とする。`F_tpd` を、`j(E)` と、2 倍が零になる `E` のアフィンな `F`-有理点の x 座標によって `ℚ` 上生成される `F` の部分体とする。

### `fieldOfModuli_le_tripodalFieldOf` and `instAlgebraFieldOfModuliTripodal`

**English** — The inclusion `F_mod ⊆ F_tpd` holds inside `F`. That inclusion equips `F_tpd` with an `F_mod`-algebra structure.

**中文** — 在 `F` 中有包含关系 `F_mod ⊆ F_tpd`。这个包含映射给出 `F_tpd` 的 `F_mod`-代数结构。

**日本語** — `F` の中で `F_mod ⊆ F_tpd` が成り立つ。この包含写像により、`F_tpd` に `F_mod`-代数構造が入る。

### `algebraMap_fieldOfModuli_tripodal_apply`

**English** — For every `x ∈ F_mod`, the image of `x` under the algebra map from `F_mod` to `F_tpd`, viewed in `F`, equals the image of `x` in `F`.

**中文** — 对每个 `x ∈ F_mod`，它经由从 `F_mod` 到 `F_tpd` 的代数映射所得的元素，视为 `F` 中的元素时，等于 `x` 在 `F` 中的像。

**日本語** — 任意の `x ∈ F_mod` について、`F_mod` から `F_tpd` への代数写像による `x` の像を `F` の元とみなすと、`F` における `x` の像に等しい。

### `instIsScalarTowerFieldOfModuliTripodal` and `instIsScalarTowerRatFieldOfModuliTripodal`

**English** — The algebra maps form scalar towers `F_mod ⊆ F_tpd ⊆ F` and `ℚ ⊆ F_mod ⊆ F_tpd`. In each tower the direct algebra map equals the composite through the middle field.

**中文** — 代数映射给出两个标量塔 `F_mod ⊆ F_tpd ⊆ F` 和 `ℚ ⊆ F_mod ⊆ F_tpd`。在每个塔中，从底域到顶域的代数映射等于经由中间域的复合映射。

**日本語** — 代数写像は二つのスカラー塔 `F_mod ⊆ F_tpd ⊆ F` と `ℚ ⊆ F_mod ⊆ F_tpd` をなす。各塔で、底の体から最上段の体への代数写像は、中間の体を経由する合成写像に等しい。

### `instFiniteDimensionalFieldOfModuliTripodal` and `finrank_tripodal_eq_mul`

**English** — The extension `F_tpd/F_mod` is finite-dimensional. Its degrees satisfy `[F_tpd : ℚ] = [F_mod : ℚ] * [F_tpd : F_mod]`, where each degree denotes the corresponding `Module.finrank`.

**中文** — `F_tpd` 在 `F_mod` 上是有限维的。次数满足 `[F_tpd : ℚ] = [F_mod : ℚ] * [F_tpd : F_mod]`，其中每个次数都是相应的 `Module.finrank`。

**日本語** — `F_tpd` は `F_mod` 上有限次元である。体拡大の次数は `[F_tpd : ℚ] = [F_mod : ℚ] * [F_tpd : F_mod]` を満たし、各次数は対応する `Module.finrank` を表す。

## Finite places of `L`

**English** — Let `Fbar` be a field with an `F`-algebra structure. Let `L` be an intermediate field of `Fbar/F` whose carrier has a `NumberField` instance. For a finite place `w`, write `p(w)` for its residue characteristic, `e_w` for its absolute ramification index, and `f_w` for its absolute residue degree. Write `e(v/u)` and `f(v/u)` for `Tripod.relRamIdx v u` and `Tripod.relInertDeg v u`.

**中文** — 设 `Fbar` 为带有 `F`-代数结构的域，`L` 为 `Fbar/F` 的中间域，并给定其载体上的 `NumberField` 实例。对有限位 `w`，记其剩余特征为 `p(w)`、绝对分歧指数为 `e_w`、绝对剩余次数为 `f_w`。用 `e(v/u)` 和 `f(v/u)` 分别表示 `Tripod.relRamIdx v u` 和 `Tripod.relInertDeg v u`。

**日本語** — `Fbar` を `F`-代数構造を持つ体とし、`L` を `Fbar/F` の中間体とする。`L` の台となる型に `NumberField` インスタンスを仮定する。有限素点 `w` の剰余標数、絶対分岐指数、絶対剰余次数をそれぞれ `p(w)`、`e_w`、`f_w` と書く。`Tripod.relRamIdx v u` と `Tripod.relInertDeg v u` をそれぞれ `e(v/u)` と `f(v/u)` と書く。

### `placeTpd` and `liesOver_placeTpd`

**English** — For each finite place `v` of `L`, the abbreviation `placeTpd F E L v` returns the finite place `u` of `F_tpd` below `v`, using `Tripod.placeUnder`. Every such `v` lies over its associated `u`.

**中文** — 对 `L` 的每个有限位 `v`，缩写 `placeTpd F E L v` 使用 `Tripod.placeUnder` 给出 `F_tpd` 中位于 `v` 下方的有限位 `u`。每个这样的 `v` 都位于与其对应的 `u` 上方。

**日本語** — `L` の各有限素点 `v` に対し、略記 `placeTpd F E L v` は `Tripod.placeUnder` により、`v` の下にある `F_tpd` の有限素点 `u` を与える。各 `v` は対応する `u` の上にある。

### `residueChar_placeTpd`, `ramIdx_eq_ramIdx_placeTpd_mul`, and `inertDeg_eq_inertDeg_placeTpd_mul`

**English** — For every finite place `v` of `L`, let `u = placeTpd F E L v`. The three conclusions are `p(u) = p(v)`, `e_v = e_u * e(v/u)`, and `f_v = f_u * f(v/u)`, respectively.

**中文** — 对 `L` 的每个有限位 `v`，令 `u = placeTpd F E L v`。三个结论依次为 `p(u) = p(v)`、`e_v = e_u * e(v/u)` 和 `f_v = f_u * f(v/u)`。

**日本語** — `L` の各有限素点 `v` に対し、`u = placeTpd F E L v` とおく。三つの結論はそれぞれ `p(u) = p(v)`、`e_v = e_u * e(v/u)`、`f_v = f_u * f(v/u)` である。

## `RelRamIdxModLeTwo`

**English** — Let `VBad` be a given set of finite places of `F_mod`. The proposition `RelRamIdxModLeTwo (F := F) E VBad` says that for every finite place `u` of `F_tpd` and every finite place `u₀` of `F_mod`, if `u₀ ∈ VBad` and `u` lies over `u₀`, then `e(u/u₀) ≤ 2`.

**中文** — 给定 `F_mod` 的有限位集合 `VBad`。命题 `RelRamIdxModLeTwo (F := F) E VBad` 断言，对 `F_tpd` 的任意有限位 `u` 和 `F_mod` 的任意有限位 `u₀`，若 `u₀ ∈ VBad` 且 `u` 位于 `u₀` 上方，则 `e(u/u₀) ≤ 2`。

**日本語** — `VBad` を `F_mod` の有限素点の集合とする。命題 `RelRamIdxModLeTwo (F := F) E VBad` は、`F_tpd` の任意の有限素点 `u` と `F_mod` の任意の有限素点 `u₀` について、`u₀ ∈ VBad` であり、かつ `u` が `u₀` の上にあるならば、`e(u/u₀) ≤ 2` であると述べる。

## `TowerLocalFacts`

**English** — Given `F`, `E`, `Fbar`, and `VBad` as above, take `Pr : AdmissiblePrimeData F E Fbar VBad` and a `NumberField` instance on the carrier of `Pr.torsionField`. Set `ℓ = Pr.ℓ` and `K = ↥Pr.torsionField`, where `Pr.torsionField` is the fixed field of `Pr.rep.ker` in `Fbar`. For each finite place `v` of `K`, set `u = placeTpd F E Pr.torsionField v` and `p = residueChar v`. The proposition `TowerLocalFacts E VBad Pr` is a structure with the following three proof fields.

**中文** — 给定上述 `F`、`E`、`Fbar` 和 `VBad`，取 `Pr : AdmissiblePrimeData F E Fbar VBad`，并给定 `Pr.torsionField` 载体上的 `NumberField` 实例。令 `ℓ = Pr.ℓ`、`K = ↥Pr.torsionField`，其中 `Pr.torsionField` 为 `Fbar` 中 `Pr.rep.ker` 的不动域。对 `K` 的每个有限位 `v`，令 `u = placeTpd F E Pr.torsionField v`，`p = residueChar v`。命题 `TowerLocalFacts E VBad Pr` 是含以下三个证明字段的结构。

**日本語** — 上記の `F`、`E`、`Fbar`、`VBad` に対し、`Pr : AdmissiblePrimeData F E Fbar VBad` と、`Pr.torsionField` の台となる型の `NumberField` インスタンスを仮定する。`ℓ = Pr.ℓ`、`K = ↥Pr.torsionField` とおく。`Pr.torsionField` は `Fbar` 内の `Pr.rep.ker` の固定体である。`K` の各有限素点 `v` に対し、`u = placeTpd F E Pr.torsionField v`、`p = residueChar v` とおく。命題 `TowerLocalFacts E VBad Pr` は次の三つの証明フィールドを持つ構造体である。

### `padicValNat_relRamIdx_le`

**English** — For every finite place `v` of `K`, the `p`-adic valuation of the natural number `e(v/u)` is at most `wildConst ℓ p`. In symbols, `padicValNat p (e(v/u)) ≤ wildConst ℓ p`.

**中文** — 对 `K` 的每个有限位 `v`，自然数 `e(v/u)` 的 `p` 进赋值至多为 `wildConst ℓ p`，即 `padicValNat p (e(v/u)) ≤ wildConst ℓ p`。

**日本語** — `K` の各有限素点 `v` に対し、自然数 `e(v/u)` の `p` 進付値は `wildConst ℓ p` 以下である。すなわち、`padicValNat p (e(v/u)) ≤ wildConst ℓ p` が成り立つ。

### `relRamIdx_eq_one`

**English** — For every finite place `v` of `K`, if `p ∉ {2, 3, 5, ℓ}` and `¬ IsBadTpdOf F E VBad u`, then `e(v/u) = 1`. The second condition means that no finite place of `F` lies over both `u` and some member of `VBad`.

**中文** — 对 `K` 的每个有限位 `v`，若 `p ∉ {2, 3, 5, ℓ}` 且 `¬ IsBadTpdOf F E VBad u`，则 `e(v/u) = 1`。第二个条件表示，`F` 中不存在同时位于 `u` 与某个 `VBad` 成员上方的有限位。

**日本語** — `K` の各有限素点 `v` に対し、`p ∉ {2, 3, 5, ℓ}` であり、かつ `¬ IsBadTpdOf F E VBad u` が成り立つならば、`e(v/u) = 1` である。二つ目の条件は、`u` と `VBad` のいずれかの元の両方の上にある `F` の有限素点が存在しないことを表す。

### `relRamIdx_le`

**English** — For every finite place `v` of `K`, if `p ∉ {2, 3, 5, ℓ}`, then `e(v/u) ≤ 30 * ℓ`.

**中文** — 对 `K` 的每个有限位 `v`，若 `p ∉ {2, 3, 5, ℓ}`，则 `e(v/u) ≤ 30 * ℓ`。

**日本語** — `K` の各有限素点 `v` に対し、`p ∉ {2, 3, 5, ℓ}` ならば `e(v/u) ≤ 30 * ℓ` である。
