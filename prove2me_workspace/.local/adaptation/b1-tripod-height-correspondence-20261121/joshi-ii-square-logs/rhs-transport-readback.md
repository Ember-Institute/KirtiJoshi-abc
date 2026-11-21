# Source_ReferenceIutPaperRHSTransport

## English

### Attaching RHS data

`Corollary312VariantData.withRHSData` takes `R : RHSData X.data` and forms `X.withRHSData R`. It assigns `data := X.data`, `qPilot := X.qPilot`, and `rhsData := R`. [Bundle definition][bundle]

`Theorem110Invariants.withRHSData` copies every arithmetic invariant and proof field into the invariant record for `X.withRHSData R`. `Theorem110Certificate.withRHSData` then carries the four proof fields `seven_le`, `bad_mem_dst`, `step_ii`, and `step_iii` into the certificate for `inv.withRHSData R`. [Invariant transport][invariants] · [Certificate transport][certificate]

### Substituting the theta-pilot

`RHSData.withThetaPilot` sets `thetaPilot := theta` in the existing container, volume, and hull systems. For each capsule `i`, the input `theta i` has type `R.container.AdmissibleRegion i`. The caller proves `R.hull.IsAdmissible (theta i)` and `theta i ≤ R.container.logShellAdmissible i`. [Theta-pilot definition][theta]

For `R = X.rhsData`, `Theorem110Invariants.LocalEstimate.withThetaPilot` takes `est : inv.LocalEstimate`, the new family, and those two admissibility and containment proofs. It also requires `(theta i).region vQ ⊆ est.cont i vQ` for every capsule `i` and rational place `vQ`. The new local estimate uses that containment for `thetaPilot_subset`. It copies `cont`, `cont_mem_hullRegions`, `cont_eq_integral`, `vol_finite`, `vol_infinite`, and `packetVol_mono` from `est`. [Local estimate transport][local-estimate]

### P7 witness

`exists_p7_witness_withRHSData` uses `I : Corollary22Inputs T K d`, a tripod point `x`, and `hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d`. It takes `R : RHSData X.data`, `inv : Theorem110Invariants X`, and `cert : Theorem110Certificate inv`. For an arbitrary predicate `Paper` on variants, it also takes a proof of `Paper (X.withRHSData R)`. The caller supplies `Nonempty (inv.withRHSData R).LocalEstimate`. [P7 theorem statement][p7]

The proof chooses `Y := X.withRHSData R` and `arith := inv.withRHSData R`. It uses `cert.withRHSData R` for the certificate and the supplied proofs for `Paper Y` and `Nonempty arith.LocalEstimate`. [P7 witness construction][p7-construction]

| Input hypothesis | Witness clause |
| --- | --- |
| `X.ℓ = ℓ` | `Y.ℓ = ℓ` |
| `X.dmod ≤ d` | `Y.dmod ≤ d` |
| `X.qPilot.logQ = (I.localData x hx).heightOther 2 ℓ` | `Y.qPilot.logQ = (I.localData x hx).heightOther 2 ℓ` |
| `T.logDiff T.tripod x = inv.logDtpd` | `T.logDiff T.tripod x = arith.logDtpd` |
| `inv.logFtpd ≤ T.logCond T.tripod x` | `arith.logFtpd ≤ T.logCond T.tripod x` |
| `T.logCond T.tripod x ≤ inv.logFtpd + Real.log (2 * ℓ)` | `T.logCond T.tripod x ≤ arith.logFtpd + Real.log (2 * ℓ)` |

## 简体中文

### 附加右端数据

`Corollary312VariantData.withRHSData` 接受 `R : RHSData X.data` 并构造 `X.withRHSData R`。它设置 `data := X.data`、`qPilot := X.qPilot` 和 `rhsData := R`。 [数据定义][bundle]

`Theorem110Invariants.withRHSData` 将所有算术不变量及证明字段复制到 `X.withRHSData R` 对应的记录中。`Theorem110Certificate.withRHSData` 将 `seven_le`、`bad_mem_dst`、`step_ii`、`step_iii` 四个证明字段传递到 `inv.withRHSData R` 对应的证书中。 [不变量传递][invariants] · [证书传递][certificate]

### 替换 theta-pilot

`RHSData.withThetaPilot` 在原容器、体积与包络系统中设置 `thetaPilot := theta`。对每个胶囊 `i`，输入 `theta i` 的类型为 `R.container.AdmissibleRegion i`。调用者须证明包络可容许性 `R.hull.IsAdmissible (theta i)` 和对数壳包含关系 `theta i ≤ R.container.logShellAdmissible i`。 [theta-pilot 定义][theta]

取 `R = X.rhsData` 时，`Theorem110Invariants.LocalEstimate.withThetaPilot` 接受 `est : inv.LocalEstimate`、新的区域族及上述可容许性与包含关系的证明。它还要求每个胶囊 `i` 和每个有理位 `vQ` 都满足 `(theta i).region vQ ⊆ est.cont i vQ`。新的局部估计以此作为 `thetaPilot_subset` 的证明，并从 `est` 复制 `cont`、`cont_mem_hullRegions`、`cont_eq_integral`、`vol_finite`、`vol_infinite` 和 `packetVol_mono`。 [局部估计传递][local-estimate]

### P7 的存在见证

`exists_p7_witness_withRHSData` 使用 `I : Corollary22Inputs T K d`、tripod 上的点 `x` 及 `hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d`。它接受 `R : RHSData X.data`、`inv : Theorem110Invariants X` 和 `cert : Theorem110Certificate inv`。对变体数据上的任意谓词 `Paper`，调用者还要提供 `Paper (X.withRHSData R)` 和 `Nonempty (inv.withRHSData R).LocalEstimate` 的证明。 [P7 定理陈述][p7]

证明选取 `Y := X.withRHSData R` 和 `arith := inv.withRHSData R`。证书由 `cert.withRHSData R` 给出，`Paper Y` 与 `Nonempty arith.LocalEstimate` 由调用者提供的两个证明给出。 [P7 见证构造][p7-construction]

| 输入假设 | 见证中的条件 |
| --- | --- |
| `X.ℓ = ℓ` | `Y.ℓ = ℓ` |
| `X.dmod ≤ d` | `Y.dmod ≤ d` |
| `X.qPilot.logQ = (I.localData x hx).heightOther 2 ℓ` | `Y.qPilot.logQ = (I.localData x hx).heightOther 2 ℓ` |
| `T.logDiff T.tripod x = inv.logDtpd` | `T.logDiff T.tripod x = arith.logDtpd` |
| `inv.logFtpd ≤ T.logCond T.tripod x` | `arith.logFtpd ≤ T.logCond T.tripod x` |
| `T.logCond T.tripod x ≤ inv.logFtpd + Real.log (2 * ℓ)` | `T.logCond T.tripod x ≤ arith.logFtpd + Real.log (2 * ℓ)` |

## 日本語

### 右辺データの付与

`Corollary312VariantData.withRHSData` は `R : RHSData X.data` を受け取り、`X.withRHSData R` を構成する。各フィールドには `data := X.data`、`qPilot := X.qPilot`、`rhsData := R` を設定する。 [データの定義][bundle]

`Theorem110Invariants.withRHSData` は算術不変量と証明の全フィールドを `X.withRHSData R` に対応するレコードへコピーする。`Theorem110Certificate.withRHSData` は `seven_le`、`bad_mem_dst`、`step_ii`、`step_iii` の四つの証明フィールドを `inv.withRHSData R` に対応する証明書へ移す。 [不変量の移送][invariants] · [証明書の移送][certificate]

### theta-pilot の置換

`RHSData.withThetaPilot` は既存の容器、体積、包絡系の中で `thetaPilot := theta` とする。各カプセル `i` に対する入力 `theta i` の型は `R.container.AdmissibleRegion i` である。呼び出し側は、包絡系での許容性 `R.hull.IsAdmissible (theta i)` と対数シェルへの包含 `theta i ≤ R.container.logShellAdmissible i` を証明する。 [theta-pilot の定義][theta]

`R = X.rhsData` とすると、`Theorem110Invariants.LocalEstimate.withThetaPilot` は `est : inv.LocalEstimate`、新しい領域族、上記の許容性と包含の証明を受け取る。さらに、すべてのカプセル `i` と有理数体の素点 `vQ` に対して `(theta i).region vQ ⊆ est.cont i vQ` を仮定する。新しい局所評価は、この包含の証明を `thetaPilot_subset` に使う。`cont`、`cont_mem_hullRegions`、`cont_eq_integral`、`vol_finite`、`vol_infinite`、`packetVol_mono` は `est` からコピーする。 [局所評価の移送][local-estimate]

### P7 の存在証人

`exists_p7_witness_withRHSData` は `I : Corollary22Inputs T K d`、tripod 上の点 `x`、および `hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d` を用いる。入力には `R : RHSData X.data`、`inv : Theorem110Invariants X`、`cert : Theorem110Certificate inv` がある。変形データ上の任意の述語 `Paper` に対し、呼び出し側は `Paper (X.withRHSData R)` と `Nonempty (inv.withRHSData R).LocalEstimate` の証明も与える。 [P7 の定理][p7]

証明は `Y := X.withRHSData R` と `arith := inv.withRHSData R` を選ぶ。証明書には `cert.withRHSData R` を使い、`Paper Y` と `Nonempty arith.LocalEstimate` には入力の二つの証明を使う。 [P7 の証人の構成][p7-construction]

| 入力の仮定 | 証人が満たす条件 |
| --- | --- |
| `X.ℓ = ℓ` | `Y.ℓ = ℓ` |
| `X.dmod ≤ d` | `Y.dmod ≤ d` |
| `X.qPilot.logQ = (I.localData x hx).heightOther 2 ℓ` | `Y.qPilot.logQ = (I.localData x hx).heightOther 2 ℓ` |
| `T.logDiff T.tripod x = inv.logDtpd` | `T.logDiff T.tripod x = arith.logDtpd` |
| `inv.logFtpd ≤ T.logCond T.tripod x` | `arith.logFtpd ≤ T.logCond T.tripod x` |
| `T.logCond T.tripod x ≤ inv.logFtpd + Real.log (2 * ℓ)` | `T.logCond T.tripod x ≤ arith.logFtpd + Real.log (2 * ℓ)` |

[bundle]: /home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-tripod-height-correspondence-20261121/joshi-ii-square-logs/Source_ReferenceIutPaperRHSTransport.lean:13
[invariants]: /home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-tripod-height-correspondence-20261121/joshi-ii-square-logs/Source_ReferenceIutPaperRHSTransport.lean:20
[certificate]: /home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-tripod-height-correspondence-20261121/joshi-ii-square-logs/Source_ReferenceIutPaperRHSTransport.lean:36
[theta]: /home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-tripod-height-correspondence-20261121/joshi-ii-square-logs/Source_ReferenceIutPaperRHSTransport.lean:45
[local-estimate]: /home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-tripod-height-correspondence-20261121/joshi-ii-square-logs/Source_ReferenceIutPaperRHSTransport.lean:55
[p7]: /home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-tripod-height-correspondence-20261121/joshi-ii-square-logs/Source_ReferenceIutPaperRHSTransport.lean:70
[p7-construction]: /home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-tripod-height-correspondence-20261121/joshi-ii-square-logs/Source_ReferenceIutPaperRHSTransport.lean:88
