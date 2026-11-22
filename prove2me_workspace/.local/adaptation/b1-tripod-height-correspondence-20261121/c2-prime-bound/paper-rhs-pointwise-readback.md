# Paper RHS supply at a point and at a common prime bound

## 简体中文

### `PaperRHSSupplyAtPoint`

固定 `K : T.CBS`、`d : ℕ`、`I : Corollary22Inputs T K d`，以及变体数据上的谓词 `Paper`。对 tripod 上的点 `x` 及证明 `hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d`，将该定义的阈值参数 `minimum` 在此处记为 `pointMinimum`。令 `L := I.localData x hx`。它适用于每个满足下列 P7 条件的 $\ell$。

- `ℓ.Prime` 且 `7 ≤ ℓ`。
- 对每个 `w ∈ L.bad`，有 `¬ ℓ ∣ L.hv w`。
- 对每个 `w ∈ L.bad`，若 `L.p w = ℓ`，则 `(L.hv w : ℝ) < Real.sqrt (I.h x)`。
- 存在 `w ∈ L.bad`，使 `L.p w ≠ 2 ∧ L.p w ≠ ℓ`。
- `I.SL2Image x ℓ`。 [逐点定义][point]

命题对每组初始数据 `D`、局部理论 `LT`、局部数据 `TL : ThetaLocalData D LT`、`QI : QPilotInputs D` 及 `TA : TowerArithmetic D LT TL` 量化。令 `X := concreteVariantData D LT TL QI`、`inv := TL.invariants QI`。该组 P7 数据须满足

```lean
X.ℓ = ℓ
pointMinimum ≤ X.ℓ
X.dmod ≤ d
X.qPilot.logQ = (I.localData x hx).heightOther 2 ℓ
T.logDiff T.tripod x = inv.logDtpd
inv.logFtpd ≤ T.logCond T.tripod x
T.logCond T.tripod x ≤ inv.logFtpd + Real.log (2 * ℓ)
```

逐点供给须给出 `R : RHSData D`、论文谓词 `Paper (X.withRHSData R)` 的证明，以及同一 `R` 上的 `Nonempty (inv.withRHSData R).LocalEstimate`。 [算术前提与供给结论][witness]

### `PaperRHSSupplyAtLeast.of_pointwise`

固定同一组 `K`、`d`、`I`、`Paper`，并一次选定自然数 $N=\mathrm{minimum}$。对每个带有 `hx` 且满足 `x ∉ I.excCore` 的点，前提须同时给出逐点供给和阈值见证 $n_x$ 的上界。

$$
\exists n_x:\mathbb N,\quad n_x\le N
  \ \land\ \operatorname{PaperRHSSupplyAtPoint}(n_x,\mathrm{Paper},I,x,hx).
$$

同一个 $N$ 覆盖固定 $(K,d)$ 内所有这些点的阈值见证。结论 `PaperRHSSupplyAtLeast minimum Paper I` 在每个上述点给出以 $N$ 为阈值的 `PaperRHSSupplyAtPoint`。证明用 `hBound.trans hMinimum` 从 $n_x\le N\le X.\ell$ 得到 $n_x\le X.\ell$。它将此不等式与当前的素数、P7 假设、`D LT TL QI TA` 和 `hPrime` 一并传给该点的供给。该供给接受其余算术前提，返回论文 RHS、`Paper` 的证明和局部估计存在性的证明。 [族供给定义][family] · [提升定理][promotion] · [提升证明][forwarding]

下游适配器从 `ex x hx hxe ℓ hℓp hℓ7 hP2 hP3 hP5 hP6` 取得实际 P7 数据，用 `hPrime` 把所选素数的下界传到 `D.ℓ`，再将数据与全部算术前提传给族供给。它把返回的 `R`、`hPaper`、`est` 与由 `TA` 得到的证书交给 `exists_p7_witness_withRHSData`。 [P7 实参传递][consumer]

## English

### `PaperRHSSupplyAtPoint`

Fix `K : T.CBS`, `d : ℕ`, `I : Corollary22Inputs T K d`, and a predicate `Paper` on variant data. Take a tripod point `x` with `hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d`. Write `pointMinimum` for the natural-number parameter `minimum` at this point. Put `L := I.localData x hx`. It applies to every $\ell$ with these P7 premises.

- `ℓ.Prime` and `7 ≤ ℓ`.
- For every `w ∈ L.bad`, `¬ ℓ ∣ L.hv w`.
- For every `w ∈ L.bad` with `L.p w = ℓ`, `(L.hv w : ℝ) < Real.sqrt (I.h x)`.
- Some `w ∈ L.bad` satisfies `L.p w ≠ 2 ∧ L.p w ≠ ℓ`.
- `I.SL2Image x ℓ`. [Pointwise definition][point]

The proposition quantifies over each initial datum `D`, local theory `LT`, local data `TL : ThetaLocalData D LT`, and `QI : QPilotInputs D`. It also quantifies over `TA : TowerArithmetic D LT TL`. Put `X := concreteVariantData D LT TL QI` and `inv := TL.invariants QI`. This P7 data must satisfy

```lean
X.ℓ = ℓ
pointMinimum ≤ X.ℓ
X.dmod ≤ d
X.qPilot.logQ = (I.localData x hx).heightOther 2 ℓ
T.logDiff T.tripod x = inv.logDtpd
inv.logFtpd ≤ T.logCond T.tripod x
T.logCond T.tripod x ≤ inv.logFtpd + Real.log (2 * ℓ)
```

The pointwise supplier must give `R : RHSData D` and a proof of the paper predicate `Paper (X.withRHSData R)`. It must also give `Nonempty (inv.withRHSData R).LocalEstimate` for that `R`. [Arithmetic premises and output][witness]

### `PaperRHSSupplyAtLeast.of_pointwise`

Fix the same `K`, `d`, `I`, and `Paper`, and fix one natural number $N=\mathrm{minimum}$. For each point with `hx` and `x ∉ I.excCore`, the hypothesis supplies a threshold witness $n_x$ and its bound together with the pointwise supply.

$$
\exists n_x:\mathbb N,\quad n_x\le N
  \ \land\ \operatorname{PaperRHSSupplyAtPoint}(n_x,\mathrm{Paper},I,x,hx).
$$

The single $N$ bounds the chosen threshold witnesses across the fixed $(K,d)$ family. The conclusion `PaperRHSSupplyAtLeast minimum Paper I` gives `PaperRHSSupplyAtPoint` with threshold $N$ at every such point. The proof uses `hBound.trans hMinimum` to derive $n_x\le X.\ell$ from $n_x\le N\le X.\ell$. It passes this bound, the prime, the P7 premises, `D LT TL QI TA`, and `hPrime` to the supplier at that point. The supplier takes the remaining arithmetic premises. It returns the RHS with proofs of `Paper` and existence of a local estimate. [Family definition][family] · [Promotion theorem][promotion] · [Argument passing][forwarding]

The downstream adapter takes its P7 data from `ex x hx hxe ℓ hℓp hℓ7 hP2 hP3 hP5 hP6`. It uses `hPrime` to transfer the selected prime bound to `D.ℓ`. It gives that data and all the arithmetic premises to the family supplier. It passes the resulting `R`, `hPaper`, and `est` with the certificate from `TA` to `exists_p7_witness_withRHSData`. [P7 consumer][consumer]

## 日本語

### `PaperRHSSupplyAtPoint`

`K : T.CBS`、`d : ℕ`、`I : Corollary22Inputs T K d`、および変形データ上の述語 `Paper` を固定する。tripod 上の点 `x` と `hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d` を取る。この点に対する自然数の閾値引数 `minimum` を `pointMinimum` と書く。`L := I.localData x hx` とおく。P7 の次の条件を満たすすべての $\ell$ に適用する。

- `ℓ.Prime` かつ `7 ≤ ℓ`。
- すべての `w ∈ L.bad` について `¬ ℓ ∣ L.hv w`。
- `L.p w = ℓ` を満たすすべての `w ∈ L.bad` について `(L.hv w : ℝ) < Real.sqrt (I.h x)`。
- `L.p w ≠ 2 ∧ L.p w ≠ ℓ` を満たす `w ∈ L.bad` が存在する。
- `I.SL2Image x ℓ`。 [点ごとの定義][point]

この命題は、初期データ `D`、局所理論 `LT`、局所データ `TL : ThetaLocalData D LT`、`QI : QPilotInputs D`、および `TA : TowerArithmetic D LT TL` のそれぞれの組について量化する。`X := concreteVariantData D LT TL QI`、`inv := TL.invariants QI` とおく。この P7 データには次の条件を課す。

```lean
X.ℓ = ℓ
pointMinimum ≤ X.ℓ
X.dmod ≤ d
X.qPilot.logQ = (I.localData x hx).heightOther 2 ℓ
T.logDiff T.tripod x = inv.logDtpd
inv.logFtpd ≤ T.logCond T.tripod x
T.logCond T.tripod x ≤ inv.logFtpd + Real.log (2 * ℓ)
```

点ごとの供給は `R : RHSData D` と、論文の述語 `Paper (X.withRHSData R)` の証明を与える。同じ `R` に対する `Nonempty (inv.withRHSData R).LocalEstimate` も与える。 [算術の仮定と結論][witness]

### `PaperRHSSupplyAtLeast.of_pointwise`

同じ `K`、`d`、`I`、`Paper` を固定し、自然数 $N=\mathrm{minimum}$ を一つ固定する。`hx` を持ち `x ∉ I.excCore` を満たす各点について、仮定は閾値の証人 $n_x$、その上界、点ごとの供給を与える。

$$
\exists n_x:\mathbb N,\quad n_x\le N
  \ \land\ \operatorname{PaperRHSSupplyAtPoint}(n_x,\mathrm{Paper},I,x,hx).
$$

一つの $N$ が、固定した $(K,d)$ の族における各点の閾値の証人を上から抑える。結論 `PaperRHSSupplyAtLeast minimum Paper I` は、該当する各点で閾値 $N$ の `PaperRHSSupplyAtPoint` を与える。証明は `hBound.trans hMinimum` を使って、$n_x\le N\le X.\ell$ から $n_x\le X.\ell$ を得る。この不等式とともに、選んだ素数、P7 の仮定、`D LT TL QI TA`、`hPrime` をその点の供給に渡す。その供給は残りの算術の仮定を受け取り、論文の右辺、`Paper` の証明、および局所評価の存在証明を返す。 [族の定義][family] · [持ち上げ定理][promotion] · [引数の受け渡し][forwarding]

後続の定理は `ex x hx hxe ℓ hℓp hℓ7 hP2 hP3 hP5 hP6` から実際の P7 データを得る。`hPrime` を使い、選んだ素数の下界を `D.ℓ` の下界に移す。そのデータと算術の仮定をすべて族の供給に渡す。返された `R`、`hPaper`、`est` と `TA` から得た証明書を `exists_p7_witness_withRHSData` に渡す。 [P7 データの利用][consumer]

## Lean 签名 · Lean signatures · Lean シグネチャ

```lean
def PaperRHSSupplyAtPoint {K : T.CBS} {d : ℕ} (minimum : ℕ)
    (Paper : Corollary312VariantData.{u, v} AG TG → Prop) (I : Corollary22Inputs T K d)
    (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d) : Prop :=
    ∀ ℓ : ℕ, ℓ.Prime → 7 ≤ ℓ →
    (∀ w ∈ (I.localData x hx).bad, ¬ ℓ ∣ (I.localData x hx).hv w) →
    (∀ w ∈ (I.localData x hx).bad, (I.localData x hx).p w = ℓ →
      ((I.localData x hx).hv w : ℝ) < Real.sqrt (I.h x)) →
    (∃ w ∈ (I.localData x hx).bad,
      (I.localData x hx).p w ≠ 2 ∧ (I.localData x hx).p w ≠ ℓ) →
    I.SL2Image x ℓ →
    ∀ (D : InitialThetaData.{u} AG TG) (LT : LocalTheory.{u, v} D.Kt)
      (TL : ThetaLocalData D LT) (QI : QPilotInputs D), TowerArithmetic D LT TL →
      let X := concreteVariantData D LT TL QI
      let inv := TL.invariants QI
      X.ℓ = ℓ → minimum ≤ X.ℓ → X.dmod ≤ d →
      X.qPilot.logQ = (I.localData x hx).heightOther 2 ℓ →
      T.logDiff T.tripod x = inv.logDtpd →
      inv.logFtpd ≤ T.logCond T.tripod x →
      T.logCond T.tripod x ≤ inv.logFtpd + Real.log (2 * ℓ) →
      ∃ R : RHSData.{u, v} D, Paper (X.withRHSData R) ∧
        Nonempty (inv.withRHSData R).LocalEstimate
```

[Lean][point]

```lean
def PaperRHSSupplyAtLeast {K : T.CBS} {d : ℕ} (minimum : ℕ)
    (Paper : Corollary312VariantData.{u, v} AG TG → Prop) (I : Corollary22Inputs T K d) : Prop :=
  ∀ (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d), x ∉ I.excCore →
    PaperRHSSupplyAtPoint minimum Paper I x hx
```

[Lean][family]

```lean
theorem PaperRHSSupplyAtLeast.of_pointwise {K : T.CBS} {d : ℕ}
    {minimum : ℕ} {Paper : Corollary312VariantData.{u, v} AG TG → Prop}
    {I : Corollary22Inputs T K d}
    (supply : ∀ (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d),
      x ∉ I.excCore → ∃ pointMinimum : ℕ, pointMinimum ≤ minimum ∧
        PaperRHSSupplyAtPoint pointMinimum Paper I x hx) :
    PaperRHSSupplyAtLeast minimum Paper I
```

[Lean][promotion]

[ci-026800-0077539e][receipt]

[point]: Source_TripodCanonicalCorollary22PaperRHS.lean#L15
[witness]: Source_TripodCanonicalCorollary22PaperRHS.lean#L25
[family]: Source_TripodCanonicalCorollary22PaperRHS.lean#L38
[promotion]: Source_TripodCanonicalCorollary22PaperRHS.lean#L44
[forwarding]: Source_TripodCanonicalCorollary22PaperRHS.lean#L51
[consumer]: Source_TripodCanonicalCorollary22PaperRHS.lean#L60
[receipt]: ci-026800-0077539e.result.json
