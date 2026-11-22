# Corollary 3.12 · Standard $\mathbb C_p$ norms

## 简体中文

### 1. `sectionQRootProduct`

令 $M=\mathbb Q(j(D.E))$ 为模域，$K_t=D.\mathrm{Kt}$ 为扭点域，$B=\mathrm{QI.badModuliFinset}$。对 $w\in B$，记 $s(w)=D.\mathrm{localData.sect.sectFin}(w)$ 为截面选出的上方有限位，$r_w=\operatorname{relLocalDeg}(s(w),w)$ 为相对局部次数。对任意局部理论 `LT`、相应的 `TL : ThetaLocalData D LT` 和 `QI : QPilotInputs D`，此定义用选定 Tate 根 `TL.qroot` 在 $K_{t,s(w)}$ 中的范数构成下式，其中 $a$ 为实数。

$$
P(a)=\prod_{w\in B}\|\operatorname{qroot}(s(w))\|^{a/(r_w[M:\mathbb Q])}.
$$

各根非零，故各因子及乘积均为正。 [乘积定义][product] · [正性][positive]

### 2. `log_sectionQRootProduct`

`hModuli` 要求 `D.algebraModK` 给出的 $M\to K_t$ 与复合 $M\to D.F\to K_t$ 相等。对一般的 `LT`，令 `X := concreteVariantData D LT TL QI`，则

$$
\log P(a)=a\,X.\mathrm{qPilot.lhs}
   =-\frac{a\,X.\mathrm{qPilot.logQ}}{2D.\ell}.
$$

[映射假设][moduli-map] · [对数恒等式][signed] · [q-pilot 的符号][sign-definition]

### 3. `sum_finite_packetVol_eq_log_sectionQRootProduct`

在同一 `hModuli` 下，取 `LT := LocalConstruct.concreteLocalTheory (K := D.Kt)`。令 $m=(D.\ell-1)/2$ 在自然数中计算，$i\in\mathrm{Fin}(m)$，$k_i=i.\mathrm{val}+1$。设 `R := TL.rhsData`。对 $p\in\mathrm{TL.badChars}$，以 $q_p$ 表示 `RationalPlace.finite` 在 $p$ 处的有限位，记 $V_{i,p}$ 为 `R.vol.packetVol` 对 `(R.thetaHull i).region qₚ` 给出的包对数体积。局部公式及按剩余特征汇总后的等式为

$$
V_{i,p}=-\frac{k_i^2\,X.\operatorname{logQAt}(p)}{2D.\ell},
  \qquad
  \sum_{p\in\mathrm{TL.badChars}}V_{i,p}=\log P(k_i^2).
$$

[有限包对数体积][packet]

### 4. `log_normalized_sectionQRootProduct_eq_sum_finite_packetVol`

在同一 `hModuli` 与具体局部理论下，按标签 $m$ 归一化。$k_i/m$ 按实数除法计算，右端为有限包对数体积的双重和除以 $m^2$。

$$
\log\!\left(\prod_{i\in\mathrm{Fin}(m)}P\!\left((k_i/m)^2\right)\right)
   =\frac{\displaystyle\sum_{i\in\mathrm{Fin}(m)}\sum_{p\in\mathrm{TL.badChars}}V_{i,p}}{m^2}.
$$

[归一化恒等式][normalized]

### 5. `sourceP7_normalized_sectionQRootProduct_eq_finite_packetVol`

输入为 `CI : CurveInputs tripodTheory AG K d`、`anab : AnabelianExistence AG TG` 和 `hX : IsSourceP7Variant CI anab X`。证明取出 P7 选定的点与素数，用 `CI.pointThetaData` 构造 `P`。取 `D := P.data`、`QI := P.qPilotInputs`、`TL := (P.localThetaData htwo).withBadChars P.qPilotInputs`，其中 `htwo` 来自 `hX`。`CI.pointThetaData_algebraMap_moduli_torsion` 给出 `hModuli`。结论存在 `D`、具体局部理论上的 `TL` 与 `QI`，使 `X = concreteVariantData D _ TL QI` 成立，并给出第 4 条的完备化范数乘积等式。 [P7 特化][p7]

### 6. `sectionQRootProduct_eq_padicComplexProduct`

令 $p(w)=\operatorname{residueChar}(s(w))$，$z_w=\operatorname{qrootInPadicComplex}(s(w))$。`qrootInPadicComplex` 先把根映入其有限完备化的代数闭包，再用 `padicAlgClEquiv` 映到 `PadicAlgCl`，最后嵌入 `PadicComplex p(w)`。第一步和最后一步分别保持范数，中间一步使用 `padicAlgClEquiv_norm_pow`。设 $d_{K_t}(s(w))$ 与 $d_M(w)$ 为相应的绝对局部次数。由截面的 `sectFin_liesOver`，有局部次数的乘法公式与相对局部次数的非零性。

$$
\|z_w\|_{\mathbb C_{p(w)}}^{d_{K_t}(s(w))}
   =\|\operatorname{qroot}(s(w))\|,
\qquad d_{K_t}(s(w))=d_M(w)r_w,\qquad r_w\ne 0.
$$

因此原指数乘上 $d_{K_t}(s(w))$ 后可约去 $r_w$，得到模域有限位的算术权重。

$$
\frac{a\,d_{K_t}(s(w))}{r_w[M:\mathbb Q]}
   =a\,\frac{d_M(w)}{[M:\mathbb Q]}
   =a\,\operatorname{placeWeight}(M,w).
$$

定理对任意 `LT`、相应的 `TL`、`QI` 和实指数 $a$ 给出

$$
P(a)=\prod_{w\in B}\|z_w\|_{\mathbb C_{p(w)}}^{a\,\operatorname{placeWeight}(M,w)}.
$$

[根的映射][root-map] · [范数幂公式][root-norm] · [局部次数][tower] · [算术权重][weight] · [标准范数乘积][converted]

### 7. `log_normalized_sectionPadicComplexProduct_eq_sum_finite_packetVol`

定理要求 `hModuli`、具体局部理论的 `TL` 与 `QI`。它用第 6 条改写第 4 条中每个胶囊的乘积。下式的求和覆盖 `TL.badChars.attach` 中素数对应的有限有理位。

$$
\log\!\left(\prod_{i\in\mathrm{Fin}(m)}
            \prod_{w\in B}
            \|z_w\|_{\mathbb C_{p(w)}}^{(k_i/m)^2\operatorname{placeWeight}(M,w)}\right)
  =\frac{\displaystyle\sum_{i\in\mathrm{Fin}(m)}\sum_{p\in\mathrm{TL.badChars}}V_{i,p}}{m^2}.
$$

[标准范数与有限包对数体积的等式][converted-normalized]

既有 MCP-CI 回执 `ci-026751-a2c6295a` 的退出码为 0。七个声明的公理输出均为 `propext`、`Classical.choice`、`Quot.sound`。 [审查回执][receipt]

## English

### 1. `sectionQRootProduct`

Let $M=\mathbb Q(j(D.E))$ be the field of moduli, $K_t=D.\mathrm{Kt}$ the torsion field, and $B=\mathrm{QI.badModuliFinset}$. For $w\in B$, let $s(w)=D.\mathrm{localData.sect.sectFin}(w)$ be the place chosen by the section. Let $r_w=\operatorname{relLocalDeg}(s(w),w)$ be its relative local degree over $w$. The definition takes any local theory `LT`, data `TL : ThetaLocalData D LT` and `QI : QPilotInputs D`, and a real exponent $a$. It uses the norm of the chosen Tate root `TL.qroot` in the completion $K_{t,s(w)}$.

$$
P(a)=\prod_{w\in B}\|\operatorname{qroot}(s(w))\|^{a/(r_w[M:\mathbb Q])}.
$$

The roots are nonzero, so each factor and the product are positive. [Product definition][product] · [Positivity][positive]

### 2. `log_sectionQRootProduct`

The hypothesis `hModuli` equates the map $M\to K_t$ from `D.algebraModK` with the composite $M\to D.F\to K_t$. For any `LT`, put `X := concreteVariantData D LT TL QI`. The theorem gives

$$
\log P(a)=a\,X.\mathrm{qPilot.lhs}
   =-\frac{a\,X.\mathrm{qPilot.logQ}}{2D.\ell}.
$$

[Map hypothesis][moduli-map] · [Logarithm identity][signed] · [Sign of the q-pilot][sign-definition]

### 3. `sum_finite_packetVol_eq_log_sectionQRootProduct`

Use the same `hModuli` and take `LT := LocalConstruct.concreteLocalTheory (K := D.Kt)`. Compute $m=(D.\ell-1)/2$ in the natural numbers. For $i\in\mathrm{Fin}(m)$, put $k_i=i.\mathrm{val}+1$. Put `R := TL.rhsData`. For $p\in\mathrm{TL.badChars}$, let $q_p$ be the rational finite place `RationalPlace.finite` at $p$. Let $V_{i,p}$ be `R.vol.packetVol` of `(R.thetaHull i).region qₚ` at capsule $i$ and place $q_p$. The proof applies the local formula and groups the q-pilot terms by residue characteristic.

$$
V_{i,p}=-\frac{k_i^2\,X.\operatorname{logQAt}(p)}{2D.\ell},
  \qquad
  \sum_{p\in\mathrm{TL.badChars}}V_{i,p}=\log P(k_i^2).
$$

[Finite packet log-volumes][packet]

### 4. `log_normalized_sectionQRootProduct_eq_sum_finite_packetVol`

The theorem uses the same `hModuli` and concrete local theory. It forms the squared label ratio using real division. The right side divides the sum of finite packet log-volumes by $m^2$.

$$
\log\!\left(\prod_{i\in\mathrm{Fin}(m)}P\!\left((k_i/m)^2\right)\right)
   =\frac{\displaystyle\sum_{i\in\mathrm{Fin}(m)}\sum_{p\in\mathrm{TL.badChars}}V_{i,p}}{m^2}.
$$

[Normalized product identity][normalized]

### 5. `sourceP7_normalized_sectionQRootProduct_eq_finite_packetVol`

The inputs include `CI : CurveInputs tripodTheory AG K d`, `anab : AnabelianExistence AG TG`, and `hX : IsSourceP7Variant CI anab X`. The proof obtains the chosen point and prime from `hX`. It constructs `P` using `CI.pointThetaData` and takes `D := P.data` and `QI := P.qPilotInputs`. It sets `TL := (P.localThetaData htwo).withBadChars P.qPilotInputs` using `htwo` from `hX`. The theorem `CI.pointThetaData_algebraMap_moduli_torsion` supplies `hModuli`. The conclusion gives `D`, concrete `TL`, and `QI` with `X = concreteVariantData D _ TL QI` and the completion-norm identity in item 4. [P7 specialization][p7]

### 6. `sectionQRootProduct_eq_padicComplexProduct`

Put $p(w)=\operatorname{residueChar}(s(w))$ and $z_w=\operatorname{qrootInPadicComplex}(s(w))$. This definition maps the root into the algebraic closure of its finite completion. It applies `padicAlgClEquiv` and then includes the resulting element of `PadicAlgCl` in `PadicComplex p(w)`. The first and last maps preserve norms. The middle map satisfies `padicAlgClEquiv_norm_pow`. Let $d_{K_t}(s(w))$ and $d_M(w)$ be the absolute local degrees. The section's `sectFin_liesOver` gives the tower identity and nonzero relative degree.

$$
\|z_w\|_{\mathbb C_{p(w)}}^{d_{K_t}(s(w))}
   =\|\operatorname{qroot}(s(w))\|,
\qquad d_{K_t}(s(w))=d_M(w)r_w,\qquad r_w\ne 0.
$$

The norm power multiplies the original exponent by $d_{K_t}(s(w))$. The tower identity cancels $r_w$ and gives the arithmetic weight of the moduli place.

$$
\frac{a\,d_{K_t}(s(w))}{r_w[M:\mathbb Q]}
   =a\,\frac{d_M(w)}{[M:\mathbb Q]}
   =a\,\operatorname{placeWeight}(M,w).
$$

For any `LT`, corresponding `TL`, `QI`, and real $a$, the theorem gives

$$
P(a)=\prod_{w\in B}\|z_w\|_{\mathbb C_{p(w)}}^{a\,\operatorname{placeWeight}(M,w)}.
$$

[Image of the root][root-map] · [Norm power][root-norm] · [Local degrees][tower] · [Arithmetic weight][weight] · [Standard-norm product][converted]

### 7. `log_normalized_sectionPadicComplexProduct_eq_sum_finite_packetVol`

The theorem takes `hModuli`, `TL` for the concrete local theory, and `QI`. It rewrites the product for each capsule in item 4 using item 6. The sum ranges over the finite rational places indexed by `TL.badChars.attach`.

$$
\log\!\left(\prod_{i\in\mathrm{Fin}(m)}
            \prod_{w\in B}
            \|z_w\|_{\mathbb C_{p(w)}}^{(k_i/m)^2\operatorname{placeWeight}(M,w)}\right)
  =\frac{\displaystyle\sum_{i\in\mathrm{Fin}(m)}\sum_{p\in\mathrm{TL.badChars}}V_{i,p}}{m^2}.
$$

[Standard norms and finite packet log-volumes][converted-normalized]

The recorded MCP-CI job `ci-026751-a2c6295a` exited with code 0. Each of the seven axiom outputs lists `propext`, `Classical.choice`, and `Quot.sound`. [Review receipt][receipt]

## 日本語

### 1. `sectionQRootProduct`

$M=\mathbb Q(j(D.E))$ をモジュライ体、$K_t=D.\mathrm{Kt}$ をねじれ点体とし、$B=\mathrm{QI.badModuliFinset}$ とおく。$w\in B$ の上で切断が選ぶ有限素点を $s(w)=D.\mathrm{localData.sect.sectFin}(w)$ とし、その相対局所次数を $r_w=\operatorname{relLocalDeg}(s(w),w)$ とする。この定義は、任意の局所理論 `LT`、データ `TL : ThetaLocalData D LT` と `QI : QPilotInputs D`、実数の指数 $a$ を取る。完備化 $K_{t,s(w)}$ における、選ばれた Tate 根 `TL.qroot` のノルムを用いる。

$$
P(a)=\prod_{w\in B}\|\operatorname{qroot}(s(w))\|^{a/(r_w[M:\mathbb Q])}.
$$

各根は非零なので、すべての因子と積は正である。 [積の定義][product] · [正値性][positive]

### 2. `log_sectionQRootProduct`

仮定 `hModuli` は `D.algebraModK` による写像 $M\to K_t$ が合成 $M\to D.F\to K_t$ に等しいことを表す。任意の `LT` に対して `X := concreteVariantData D LT TL QI` とすると、次の等式を得る。

$$
\log P(a)=a\,X.\mathrm{qPilot.lhs}
   =-\frac{a\,X.\mathrm{qPilot.logQ}}{2D.\ell}.
$$

[写像についての仮定][moduli-map] · [対数の等式][signed] · [q-pilot の符号][sign-definition]

### 3. `sum_finite_packetVol_eq_log_sectionQRootProduct`

同じ `hModuli` の下で `LT := LocalConstruct.concreteLocalTheory (K := D.Kt)` とする。$m=(D.\ell-1)/2$ を自然数で計算し、$i\in\mathrm{Fin}(m)$ に対して $k_i=i.\mathrm{val}+1$ とおく。`R := TL.rhsData` とする。$p\in\mathrm{TL.badChars}$ に対応する有理数体の有限素点を `RationalPlace.finite` で表し、これを $q_p$ とする。カプセル $i$ と素点 $q_p$ で `R.vol.packetVol` を `(R.thetaHull i).region qₚ` に適用したパケット対数体積を $V_{i,p}$ とする。証明は局所公式を用い、q-pilot の寄与を剰余標数ごとにまとめる。

$$
V_{i,p}=-\frac{k_i^2\,X.\operatorname{logQAt}(p)}{2D.\ell},
  \qquad
  \sum_{p\in\mathrm{TL.badChars}}V_{i,p}=\log P(k_i^2).
$$

[有限素点でのパケット対数体積][packet]

### 4. `log_normalized_sectionQRootProduct_eq_sum_finite_packetVol`

同じ `hModuli` と具体的な局所理論を用いる。ラベルの比 $k_i/m$ は実数の除法で計算する。右辺は有限素点でのパケット対数体積の和を $m^2$ で割った値である。

$$
\log\!\left(\prod_{i\in\mathrm{Fin}(m)}P\!\left((k_i/m)^2\right)\right)
   =\frac{\displaystyle\sum_{i\in\mathrm{Fin}(m)}\sum_{p\in\mathrm{TL.badChars}}V_{i,p}}{m^2}.
$$

[正規化した積の等式][normalized]

### 5. `sourceP7_normalized_sectionQRootProduct_eq_finite_packetVol`

入力は `CI : CurveInputs tripodTheory AG K d`、`anab : AnabelianExistence AG TG`、`hX : IsSourceP7Variant CI anab X` である。証明は `hX` から P7 で選ばれた点と素数を取り出し、`CI.pointThetaData` によって `P` を構成する。`D := P.data`、`QI := P.qPilotInputs`、`TL := (P.localThetaData htwo).withBadChars P.qPilotInputs` とし、`htwo` は `hX` から得る。`hModuli` は `CI.pointThetaData_algebraMap_moduli_torsion` から得られる。結論は `D`、具体的な局所理論に対する `TL`、`QI` の存在を示し、`X = concreteVariantData D _ TL QI` と第 4 項の完備化のノルムによる等式を与える。 [P7 への特殊化][p7]

### 6. `sectionQRootProduct_eq_padicComplexProduct`

$p(w)=\operatorname{residueChar}(s(w))$、$z_w=\operatorname{qrootInPadicComplex}(s(w))$ とおく。この定義は根を有限素点での完備化の代数閉包へ移し、`padicAlgClEquiv` で `PadicAlgCl` へ写した後、`PadicComplex p(w)` に移す。最初と最後の写像はノルムを保つ。中間の写像には `padicAlgClEquiv_norm_pow` を用いる。$d_{K_t}(s(w))$ と $d_M(w)$ をそれぞれの絶対局所次数とする。切断の `sectFin_liesOver` により、局所次数の乗法公式と相対局所次数の非零性が成り立つ。

$$
\|z_w\|_{\mathbb C_{p(w)}}^{d_{K_t}(s(w))}
   =\|\operatorname{qroot}(s(w))\|,
\qquad d_{K_t}(s(w))=d_M(w)r_w,\qquad r_w\ne 0.
$$

ノルムの冪により、元の指数に $d_{K_t}(s(w))$ が掛かる。乗法公式で $r_w$ を約分すると、モジュライ体の素点の算術的な重みを得る。

$$
\frac{a\,d_{K_t}(s(w))}{r_w[M:\mathbb Q]}
   =a\,\frac{d_M(w)}{[M:\mathbb Q]}
   =a\,\operatorname{placeWeight}(M,w).
$$

任意の `LT`、対応する `TL`、`QI`、実数 $a$ に対して、定理は次の等式を与える。

$$
P(a)=\prod_{w\in B}\|z_w\|_{\mathbb C_{p(w)}}^{a\,\operatorname{placeWeight}(M,w)}.
$$

[根の像][root-map] · [ノルムの冪][root-norm] · [局所次数][tower] · [算術的な重み][weight] · [標準ノルムによる積][converted]

### 7. `log_normalized_sectionPadicComplexProduct_eq_sum_finite_packetVol`

定理は `hModuli`、具体的な局所理論に対する `TL`、および `QI` を仮定する。第 4 項の各カプセルにおける積を第 6 項で書き換える。和を取るのは `TL.badChars.attach` が添字付ける有理数体の有限素点である。

$$
\log\!\left(\prod_{i\in\mathrm{Fin}(m)}
            \prod_{w\in B}
            \|z_w\|_{\mathbb C_{p(w)}}^{(k_i/m)^2\operatorname{placeWeight}(M,w)}\right)
  =\frac{\displaystyle\sum_{i\in\mathrm{Fin}(m)}\sum_{p\in\mathrm{TL.badChars}}V_{i,p}}{m^2}.
$$

[標準ノルムと有限素点のパケット対数体積の等式][converted-normalized]

記録済みの MCP-CI ジョブ `ci-026751-a2c6295a` の終了コードは 0 である。七つの宣言の公理出力は、いずれも `propext`、`Classical.choice`、`Quot.sound` である。 [審査結果][receipt]

[product]: ReviewCor312RepresentativePadicProduct.lean#L28
[positive]: ReviewCor312RepresentativePadicProduct.lean#L37
[moduli-map]: ReviewCor312RepresentativePadicProduct.lean#L45
[signed]: ReviewCor312RepresentativePadicProduct.lean#L52
[sign-definition]: ../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_LeftHandSide.lean#L117
[packet]: ReviewCor312RepresentativePadicProduct.lean#L67
[normalized]: ReviewCor312RepresentativePadicProduct.lean#L94
[p7]: ReviewCor312RepresentativePadicProduct.lean#L123
[root-map]: ReviewCor312RepresentativePadicProduct.lean#L209
[root-norm]: ReviewCor312RepresentativePadicProduct.lean#L213
[tower]: ../../../../Solutions/Source_TripodRelativeDegreeTower.lean#L73
[weight]: ../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L78
[converted]: ReviewCor312RepresentativePadicProduct.lean#L219
[converted-normalized]: ReviewCor312RepresentativePadicProduct.lean#L248
[receipt]: ci-026751-a2c6295a.result.json
