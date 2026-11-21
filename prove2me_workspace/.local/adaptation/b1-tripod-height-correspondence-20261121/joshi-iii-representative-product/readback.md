# Source_ReferenceIutCor312RepresentativeProduct

## English

### Product and signed q-pilot

Let $M=\mathbb{Q}(j(D.E))$ be the moduli field. For each bad finite place $w$ in `QI.badModuliFinset`, the section selects $s(w)=D.\mathrm{localData.sect.sectFin}(w)$ in the torsion field $K_t=D.\mathrm{Kt}$. For a real exponent $a$, `sectionQRootProduct TL QI a` defines

$$
P(a)=\prod_{w\in\mathrm{QI.badModuliFinset}}
  \left\lVert\operatorname{qroot}(s(w))\right\rVert^{
    a/(d_{s(w)/w}[M:\mathbb{Q}])}.
$$

Here `qroot` is the chosen Tate root from `TL`. The denominator uses the relative local degree $d_{s(w)/w}$ and the absolute degree $[M:\mathbb{Q}]$. Each root is nonzero, so the factors and the product are positive. [Product definition][product] · [Positivity][positive] · [Moduli field][moduli-field]

The hypothesis `hModuli` identifies the specified algebra map $M\to K_t$ with the composite $M\to D.F\to K_t$. For any local theory `LT`, put `X := concreteVariantData D LT TL QI`. The theorem `log_sectionQRootProduct` gives

$$
\log P(a)=a\,X.\mathrm{qPilot.lhs}
  =-\frac{a\,X.\mathrm{qPilot.logQ}}{2\ell},
\qquad \ell=D.\ell.
$$

[Map compatibility][moduli-map] · [Logarithm identity][log-product] · [Sign of the q-pilot][qp-sign]

### Finite packet volumes

Use `LocalConstruct.concreteLocalTheory (K := D.Kt)` for `LT`. Let $m=(D.\ell-1)/2$ in $\mathbb N$, and let $i\in\mathrm{Fin}(m)$. Write $k_i=i.\mathrm{val}+1$. For a prime $p\in\mathrm{TL.badChars}$, let $q_p$ be `RationalPlace.finite` at $p$. Put `R = TL.rhsData`. Let $V_{i,p}$ be `R.vol.packetVol` of `(R.thetaHull i).region qₚ` at capsule $i$ and place $q_p$. The local formula is

$$
V_{i,p}=-\frac{k_i^2\,X.\operatorname{logQAt}(p)}{2\ell}.
$$

With `hModuli`, `sum_finite_packetVol_eq_log_sectionQRootProduct` groups the q-pilot contributions by residue characteristic and gives

$$
\sum_{p\in\mathrm{TL.badChars}} V_{i,p}=\log P(k_i^2).
$$

[Local volume formula][local-volume] · [Capsule sum][packet-sum]

With the same `hModuli`, `log_normalized_sectionQRootProduct_eq_sum_finite_packetVol` forms each exponent $(k_i/m)^2$ using real division and gives

$$
\log\!\left(\prod_{i\in\mathrm{Fin}(m)} P\!\left((k_i/m)^2\right)\right)
 = \frac{\displaystyle\sum_{i\in\mathrm{Fin}(m)}
             \sum_{p\in\mathrm{TL.badChars}} V_{i,p}}{m^2}.
$$

[Normalized product identity][normalized-product]

### Source P7 specialization

`sourceP7_normalized_sectionQRootProduct_eq_finite_packetVol` starts from `IsSourceP7Variant CI anab X`. The proof extracts the selected point and prime and constructs `P := CI.pointThetaData …`. It uses `P.data`, `(P.localThetaData htwo).withBadChars P.qPilotInputs`, and `P.qPilotInputs` for `D`, `TL`, and `QI`. It obtains `hModuli` from `pointThetaData_algebraMap_moduli_torsion`. The result gives these data, the equality `X = concreteVariantData D _ TL QI`, and the normalized product identity. [Source P7 predicate][p7-predicate] · [Specialization][p7-product]

## 简体中文

### 乘积与带符号的 q-pilot

设 $M=\mathbb{Q}(j(D.E))$ 为模域。对 `QI.badModuliFinset` 中每个坏有限位 $w$，截面在扭点域 $K_t=D.\mathrm{Kt}$ 中选取 $s(w)=D.\mathrm{localData.sect.sectFin}(w)$。对实数指数 $a$，`sectionQRootProduct TL QI a` 定义

$$
P(a)=\prod_{w\in\mathrm{QI.badModuliFinset}}
  \left\lVert\operatorname{qroot}(s(w))\right\rVert^{
    a/(d_{s(w)/w}[M:\mathbb{Q}])}.
$$

其中 `qroot` 是 `TL` 选定的 Tate 根，指数的分母是相对局部次数 $d_{s(w)/w}$ 与绝对次数 $[M:\mathbb{Q}]$ 的乘积。各根非零，因此各因子及其乘积均为正。 [乘积定义][product] · [正性][positive] · [模域][moduli-field]

假设 `hModuli` 表示指定的代数映射 $M\to K_t$ 等于复合映射 $M\to D.F\to K_t$。对任意局部理论 `LT` 和 `X = concreteVariantData D LT TL QI`，`log_sectionQRootProduct` 给出

$$
\log P(a)=a\,X.\mathrm{qPilot.lhs}
  =-\frac{a\,X.\mathrm{qPilot.logQ}}{2\ell},
\qquad \ell=D.\ell.
$$

[映射相容性][moduli-map] · [对数恒等式][log-product] · [q-pilot 的符号][qp-sign]

### 有限位上的包体积

取 `LT` 为 `LocalConstruct.concreteLocalTheory (K := D.Kt)`。令 $m=(D.\ell-1)/2$ 在自然数中计算。对胶囊 $i\in\mathrm{Fin}(m)$，记 $k_i=i.\mathrm{val}+1$。对素数 $p\in\mathrm{TL.badChars}$，记 $q_p$ 为 `RationalPlace.finite` 在 $p$ 处给出的有理有限位。令 `R = TL.rhsData`，并记 $V_{i,p}$ 为胶囊 $i$ 在 $q_p$ 处对 `(R.thetaHull i).region qₚ` 取 `R.vol.packetVol` 得到的包对数体积。局部公式为

$$
V_{i,p}=-\frac{k_i^2\,X.\operatorname{logQAt}(p)}{2\ell}.
$$

在 `hModuli` 下，`sum_finite_packetVol_eq_log_sectionQRootProduct` 按剩余特征汇总 q-pilot 的各项贡献，得到

$$
\sum_{p\in\mathrm{TL.badChars}} V_{i,p}=\log P(k_i^2).
$$

[局部体积公式][local-volume] · [胶囊求和][packet-sum]

在同一 `hModuli` 下，`log_normalized_sectionQRootProduct_eq_sum_finite_packetVol` 在实数中计算各因子的指数 $(k_i/m)^2$，得到

$$
\log\!\left(\prod_{i\in\mathrm{Fin}(m)} P\!\left((k_i/m)^2\right)\right)
 = \frac{\displaystyle\sum_{i\in\mathrm{Fin}(m)}
             \sum_{p\in\mathrm{TL.badChars}} V_{i,p}}{m^2}.
$$

[归一化乘积恒等式][normalized-product]

### 源 P7 的特化

`sourceP7_normalized_sectionQRootProduct_eq_finite_packetVol` 的前提是 `IsSourceP7Variant CI anab X`。证明取出选定的点与素数，构造 `P := CI.pointThetaData …`，并以 `P.data`、`(P.localThetaData htwo).withBadChars P.qPilotInputs` 和 `P.qPilotInputs` 分别作为 `D`、`TL` 和 `QI`。证明由 `pointThetaData_algebraMap_moduli_torsion` 得到 `hModuli`。结论给出这些数据、等式 `X = concreteVariantData D _ TL QI` 和归一化乘积恒等式。 [源 P7 谓词][p7-predicate] · [特化定理][p7-product]

## 日本語

### 積と符号付き q-pilot

$M=\mathbb{Q}(j(D.E))$ をモジュライ体とする。`QI.badModuliFinset` に属する各悪い有限素点 $w$ に対し、切断はねじれ点体 $K_t=D.\mathrm{Kt}$ の素点 $s(w)=D.\mathrm{localData.sect.sectFin}(w)$ を選ぶ。実数の指数 $a$ に対し、`sectionQRootProduct TL QI a` は次の積を定義する。

$$
P(a)=\prod_{w\in\mathrm{QI.badModuliFinset}}
  \left\lVert\operatorname{qroot}(s(w))\right\rVert^{
    a/(d_{s(w)/w}[M:\mathbb{Q}])}.
$$

`qroot` は `TL` が選んだ Tate 根である。指数の分母は相対局所次数 $d_{s(w)/w}$ と絶対次数 $[M:\mathbb{Q}]$ の積である。各根が非零なので、各因子と積はいずれも正である。 [積の定義][product] · [正値性][positive] · [モジュライ体][moduli-field]

仮定 `hModuli` は、指定された代数写像 $M\to K_t$ が合成 $M\to D.F\to K_t$ に等しいことを表す。任意の局所理論 `LT` と `X = concreteVariantData D LT TL QI` に対し、`log_sectionQRootProduct` は次の等式を与える。

$$
\log P(a)=a\,X.\mathrm{qPilot.lhs}
  =-\frac{a\,X.\mathrm{qPilot.logQ}}{2\ell},
\qquad \ell=D.\ell.
$$

[写像の整合性][moduli-map] · [対数の等式][log-product] · [q-pilot の符号][qp-sign]

### 有限素点でのパケット体積

`LT` を `LocalConstruct.concreteLocalTheory (K := D.Kt)` とする。自然数で $m=(D.\ell-1)/2$ とおき、カプセル $i\in\mathrm{Fin}(m)$ に対して $k_i=i.\mathrm{val}+1$ とする。素数 $p\in\mathrm{TL.badChars}$ に対応する有理数体の有限素点を $q_p$ とし、`RationalPlace.finite` で表す。`R = TL.rhsData` とし、カプセル $i$ と素点 $q_p$ における `(R.thetaHull i).region qₚ` のパケット対数体積を $V_{i,p}$ とおく。これは `R.vol.packetVol` で与えられ、局所公式は次のとおりである。

$$
V_{i,p}=-\frac{k_i^2\,X.\operatorname{logQAt}(p)}{2\ell}.
$$

`hModuli` の下で、`sum_finite_packetVol_eq_log_sectionQRootProduct` は q-pilot の寄与を剰余標数ごとにまとめ、次の等式を与える。

$$
\sum_{p\in\mathrm{TL.badChars}} V_{i,p}=\log P(k_i^2).
$$

[局所体積の公式][local-volume] · [カプセルごとの和][packet-sum]

同じ `hModuli` の下で、`log_normalized_sectionQRootProduct_eq_sum_finite_packetVol` は各因子の指数 $(k_i/m)^2$ を実数の除法で計算し、次の等式を与える。

$$
\log\!\left(\prod_{i\in\mathrm{Fin}(m)} P\!\left((k_i/m)^2\right)\right)
 = \frac{\displaystyle\sum_{i\in\mathrm{Fin}(m)}
             \sum_{p\in\mathrm{TL.badChars}} V_{i,p}}{m^2}.
$$

[正規化した積の等式][normalized-product]

### ソース P7 への特殊化

`sourceP7_normalized_sectionQRootProduct_eq_finite_packetVol` は `IsSourceP7Variant CI anab X` を仮定する。証明は選ばれた点と素数を取り出し、`P := CI.pointThetaData …` を構成する。`D`、`TL`、`QI` には、それぞれ `P.data`、`(P.localThetaData htwo).withBadChars P.qPilotInputs`、`P.qPilotInputs` を用いる。`hModuli` は `pointThetaData_algebraMap_moduli_torsion` から得られる。結論はこれらのデータ、等式 `X = concreteVariantData D _ TL QI`、および正規化した積の等式を与える。 [ソース P7 の述語][p7-predicate] · [特殊化の定理][p7-product]

[product]: /home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCor312RepresentativeProduct.lean:22
[positive]: /home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCor312RepresentativeProduct.lean:31
[moduli-field]: /home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_ThetaData_GlobalField.lean:169
[moduli-map]: /home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCor312RepresentativeProduct.lean:39
[log-product]: /home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCor312RepresentativeProduct.lean:46
[qp-sign]: /home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_LeftHandSide.lean:117
[local-volume]: /home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCor312FiniteThetaHullVolume.lean:222
[packet-sum]: /home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCor312RepresentativeProduct.lean:61
[normalized-product]: /home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCor312RepresentativeProduct.lean:88
[p7-predicate]: /home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodP7.lean:27
[p7-product]: /home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCor312RepresentativeProduct.lean:117
