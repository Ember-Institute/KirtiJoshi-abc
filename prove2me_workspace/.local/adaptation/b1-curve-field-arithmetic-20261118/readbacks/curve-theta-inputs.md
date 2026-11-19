# `globalData` and `primeData`

## English

- `globalData` takes `CA` and a witness `hP5` of a multiplicative finite place of `F` whose residue characteristic differs from both `2` and `ℓ`. It proves `IsInitialThetaGlobalData` for `C.VBadOf ℓ`, the selected places of the field of moduli. It uses `CA` for the square root of `−1`, stable reduction over `F`, and rationality of the `6`-torsion. The place below the witness gives nonemptiness: it has the same residue characteristic, and `CA.mult_invariant` gives multiplicative reduction at every place above it. Membership in `C.VBadOf ℓ` gives odd residue characteristic and multiplicative reduction at all places above each selected place.
- `primeData` takes `CA`, the Tate inputs `TI`, a prime `ℓ ≥ 7`, and the mod-`ℓ` representation data `R`. The hypotheses `hsl` and `hP2` respectively give containment of `SL₂(𝔽_ℓ)` in the image and nondivisibility of every `TI.qOrder` on `C.badAll` by `ℓ`. The result `AdmissiblePrimeData` stores `ℓ` with the required bound `5 ≤ ℓ`, the basis and representation with its action formula and open kernel, and the supplied image containment. It gives the Galois condition on `F/F_mod` with degree coprime to `ℓ`, coprimality with the residue characteristics of the selected places, and the Tate data for places above them. There `q_order_coprime` says that `ℓ` is coprime to the normalized order `ord_w(q_w)`.
- At each such place `w`, `tateJ_eq` is the equation between the Tate curve's `j`-invariant and the image of `j(E)` in `F_w`. The construction uses the same Tate parameter, uniformizer, and equality proof from `TI` at `w`.

## 中文

- `globalData` 接收曲线算术数据 `CA` 和见证 `hP5`。该见证给出 `F` 的一个乘法约化有限位点，其剩余特征既不等于 `2`，也不等于 `ℓ`。结论是关于模域所选位点集 `C.VBadOf ℓ` 的 `IsInitialThetaGlobalData`。平方根 `√−1`、`F` 上每个有限位点的稳定约化以及 `6`-挠点在 `F` 上的有理性来自 `CA`。见证位点下方的模域位点具有相同的剩余特征，`CA.mult_invariant` 给出其上方所有位点的乘法约化，从而证明所选位点集非空。由入集条件又可得每个所选位点的剩余特征为奇数，且其上方所有位点均为乘法约化。
- `primeData` 接收 `CA`、Tate 输入 `TI`、素数 `ℓ ≥ 7` 和模 `ℓ` 表示数据 `R`。`hsl` 给出表示的像包含 `SL₂(𝔽_ℓ)`，`hP2` 给出 `ℓ` 不整除 `C.badAll` 上任一 `TI.qOrder`。所得 `AdmissiblePrimeData` 记录 `ℓ`、所要求的下界 `5 ≤ ℓ`、基与表示、Galois 作用公式、核的开放性及像包含条件。它还给出 Galois 扩张 `F/F_mod` 的次数与 `ℓ` 互素、所选位点的剩余特征与 `ℓ` 互素，以及这些位点上方的 Tate 数据。其中 `q_order_coprime` 表示 `ℓ` 与归一化阶 `ord_w(q_w)` 互素。
- 在每个这样的位点 `w`，`tateJ_eq` 表示 Tate 曲线的 `j` 不变量等于 `j(E)` 在 `F_w` 中的像。构造沿用 `TI` 在 `w` 处的 Tate 参数、一致化元和等式证明。

## 日本語

- `globalData` は曲線の算術データ `CA` と、`F` 上で乗法的還元をもつ有限素点の存在を与える `hP5` を受け取る。その素点の剰余標数は `2` と `ℓ` のいずれとも異なる。結論はモジュライ体の選定素点集合 `C.VBadOf ℓ` に対する `IsInitialThetaGlobalData` である。`√−1` の存在、`F` のすべての有限素点での安定還元、および `6`-捩れ点の `F` 上の有理性には `CA` を用いる。与えられた素点の下にある素点は剰余標数が同じであり、`CA.mult_invariant` によりその上のすべての素点で乗法的還元を得る。したがって選定素点集合は空でなく、その定義により、各選定素点の剰余標数は奇数で、その上のすべての素点で乗法的還元をもつ。
- `primeData` は `CA`、Tate 入力 `TI`、素数 `ℓ ≥ 7`、および mod `ℓ` 表現データ `R` を受け取る。`hsl` は表現の像が `SL₂(𝔽_ℓ)` を含むことを、`hP2` は `C.badAll` 上のどの `TI.qOrder` も `ℓ` で割り切れないことを与える。得られる `AdmissiblePrimeData` には `ℓ` と下限 `5 ≤ ℓ`、基底と表現、Galois 作用の公式、核の開性、および像の包含条件が入る。また、Galois 拡大 `F/F_mod` の次数と `ℓ` の互いに素性、選定素点の剰余標数と `ℓ` の互いに素性、およびそれらの素点の上の Tate データを与える。`q_order_coprime` は `ℓ` と正規化位数 `ord_w(q_w)` が互いに素であることを表す。
- そのような各素点 `w` で、`tateJ_eq` は Tate 曲線の `j` 不変量が `j(E)` の `F_w` における像と等しいことを表す。この構成は `w` における `TI` の Tate パラメータ、一様化元、および等式の証明をそのまま用いる。

## Lean

Let `P` denote `C.primeData CA TI hℓ h7 R hsl hP2`. For `hw : w ∈ badPlacesOver C.F C.E (C.VBadOf ℓ)`, write `hw′ := C.mem_badAll_of_mem_badPlacesOver hw`.

```lean
P.ℓ = ℓ
P.torsionBasis = R.torsionBasis
P.rep = R.rep
P.tate w hw = TI.tate w hw′
P.unif w hw = TI.unif w hw′
(P.tate w hw).tateJ = FinitePlace.embedding w.maximalIdeal C.E.j
```

The first five equalities follow by unfolding `primeData`. The last is the proposition proved by `P.tateJ_eq w hw`, which uses `TI.tateJ_eq w hw′`. `P.q_order_coprime w hw` has the unfolded type `Nat.Coprime ℓ (TI.qOrder w hw′)`.

## Terminology to confirm

| English | 中文 | 日本語 |
| --- | --- | --- |
| field of moduli (`fieldOfModuli`) | 模域 | モジュライ体 |
| admissible prime (`AdmissiblePrimeData`) | 容许素数 | 許容素数 |
| uniformizer (`unif`) | 一致化元 | 一様化元 |
| normalized order of `q_w` (`qOrder`) | 归一化阶，即归一化加性赋值 | 正規化位数、すなわち正規化された加法付値 |
