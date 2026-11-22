# Source_ReferenceIutCor312RepresentativeComparisonLog

## 简体中文

### `paperNormalizedQRootLog`

设 $K_t=D.\mathrm{Kt}$，$s$ 为 $K_t$ 的任意有限位，$p_s$ 为 $s$ 的剩余特征。令 $y_s=\mathrm{TL.qroot}(s)$。定义 `paperNormalizedQRootLog TL s` 在实际完成域 $K_{t,s}=\mathrm{LocalCompletion.completionAt}(K_t,s)$ 中取下值。$p_s^\ast$ 在式中转换为完成域的元素。

$$
L_s=(p_s^\ast)^{-1}\operatorname{padicLog}(1+p_s^\ast y_s)
    \in K_{t,s},
\qquad
p_s^\ast=\begin{cases}4,&p_s=2,\\p_s,&p_s\ne 2.\end{cases}
$$

`LocalPadicLog.padicLog` 是主单位上的普通 $p$ 进对数。证明由 `TL.ordp_qroot_nonneg s` 得到 $\|y_s\|\le 1$，再用 $p_s$ 为素数、$\|p_s\|<1$ 和 `norm_paperNormalizedLog` 得到第一条范数等式。令 $J_s$ 为 `completionInPadicComplex s`。标准范数的正局部次数幂等于完成域范数，因此可由第一条等式得到第二条。

$$
\|L_s\|_{K_{t,s}}=\|y_s\|_{K_{t,s}},
\qquad
\|J_s(L_s)\|_{\mathbb C_{p_s}}=\|J_s(y_s)\|_{\mathbb C_{p_s}}.
$$

[对数定义][ordinary] · [除以 \(p^\ast\) 的构造][scale] · [完成域范数证明][local-norm] · [标准范数证明][standard-norm] · [完成域到标准 \(\mathbb C_p\) 的映射][embedding]

### `sectionQRootProduct_eq_comparisonLogProduct`

令 $M=\mathbb Q(j(D.E))$，$B=\mathrm{QI.badModuliFinset}$，$s(w)=D.\mathrm{localData.sect.sectFin}(w)$。对带有 $w\in B$ 证明的每个模域有限位，调用者提供 `logValue w`。`hLogValue w` 给出同一完成域中的元素等式。

$$
\operatorname{logValue}(w)\in K_{t,s(w)},\qquad
\operatorname{logValue}(w)\overset{\mathrm{hLogValue}(w)}{=}L_{s(w)}.
$$

定理接受一般局部理论 `LT` 的 `TL`、`QI`、这一逐处的值族与等式，以及任意实指数 $a$。记 $P(a)=\mathrm{TL.sectionQRootProduct}(\mathrm{QI},a)$，则

$$
P(a)=
 \prod_{w\in B}
 \|J_{s(w)}(\operatorname{logValue}(w))\|_{\mathbb C_{p_{s(w)}}}^{
    a\,\operatorname{placeWeight}(M,w)}.
$$

Lean 在 `QI.badModuliFinset.attach` 上取积，以便在每个因子中使用成员证明。证明先把 $P(a)$ 改写为选定 Tate 根的标准范数乘积，再用 `hLogValue` 和标准范数等式逐因子替换。 [代表元乘积等式][product] · [标准范数乘积][standard-product] · [算术权重][weight]

### `log_normalized_sectionComparisonLogProduct_eq_sum_finite_packetVol`

定理还要求 `hModuli` 和具体局部理论 `LocalConstruct.concreteLocalTheory (K := D.Kt)`。`hModuli` 断言 `D.algebraModK` 给出的 $M\to K_t$ 等于 $M\to D.F\to K_t$。输入仍包括 `QI`、`logValue` 与同一逐处等式 `hLogValue`。

令 $m=(D.\ell-1)/2$ 在自然数中计算，指数中的商在实数中计算。令 `R := TL.rhsData`。对 `TL.badChars.attach` 中的素数 $p$，记 $q_p$ 为对应的有限有理位。$V_{i,p}$ 是胶囊 $i$ 在该位上对 `(R.thetaHull i).region qₚ` 取 `R.vol.packetVol` 所得的包对数体积。定理在每个胶囊处代入上一条乘积等式。

$$
\operatorname{Real.log}\!\left(
  \prod_{i\in\mathrm{Fin}(m)}\prod_{w\in B}
  \|J_{s(w)}(\operatorname{logValue}(w))\|_{\mathbb C_{p_{s(w)}}}^{
     ((i.\mathrm{val}+1)/m)^2\,\operatorname{placeWeight}(M,w)}
  \right)
  =\frac{\displaystyle\sum_{i\in\mathrm{Fin}(m)}\sum_{p\in\mathrm{TL.badChars}}V_{i,p}}{m^2}.
$$

[归一化等式][normalized]

## English

### `paperNormalizedQRootLog`

Let $K_t=D.\mathrm{Kt}$, and let $s$ be any finite place of $K_t$ with residue characteristic $p_s$. Put $y_s=\mathrm{TL.qroot}(s)$. The definition `paperNormalizedQRootLog TL s` computes this value in the actual completion $K_{t,s}=\mathrm{LocalCompletion.completionAt}(K_t,s)$. The formula uses the image of $p_s^\ast$ in that field.

$$
L_s=(p_s^\ast)^{-1}\operatorname{padicLog}(1+p_s^\ast y_s)
    \in K_{t,s},
\qquad
p_s^\ast=\begin{cases}4,&p_s=2,\\p_s,&p_s\ne 2.\end{cases}
$$

`LocalPadicLog.padicLog` is the ordinary $p$-adic logarithm on principal units. The proof uses `TL.ordp_qroot_nonneg s` to get $\|y_s\|\le 1$. Primality and $\|p_s\|<1$ then give the completion-norm equality via `norm_paperNormalizedLog`. Let $J_s$ be `completionInPadicComplex s`. The positive local-degree power of the standard norm equals the completion norm. This gives the second equality.

$$
\|L_s\|_{K_{t,s}}=\|y_s\|_{K_{t,s}},
\qquad
\|J_s(L_s)\|_{\mathbb C_{p_s}}=\|J_s(y_s)\|_{\mathbb C_{p_s}}.
$$

[Logarithm definition][ordinary] · [Division by \(p^\ast\)][scale] · [Completion-norm proof][local-norm] · [Standard-norm proof][standard-norm] · [Map to standard \(\mathbb C_p\)][embedding]

### `sectionQRootProduct_eq_comparisonLogProduct`

Put $M=\mathbb Q(j(D.E))$, $B=\mathrm{QI.badModuliFinset}$, and $s(w)=D.\mathrm{localData.sect.sectFin}(w)$. For each moduli place with a proof of $w\in B$, the caller supplies `logValue w`. The premise `hLogValue w` gives an equality of elements in the same completion.

$$
\operatorname{logValue}(w)\in K_{t,s(w)},\qquad
\operatorname{logValue}(w)\overset{\mathrm{hLogValue}(w)}{=}L_{s(w)}.
$$

The theorem takes `TL` for any local theory `LT`, together with `QI`. It takes the family of values, its pointwise proof, and any real exponent $a$. Put $P(a)=\mathrm{TL.sectionQRootProduct}(\mathrm{QI},a)$. The theorem gives

$$
P(a)=
 \prod_{w\in B}
 \|J_{s(w)}(\operatorname{logValue}(w))\|_{\mathbb C_{p_{s(w)}}}^{
    a\,\operatorname{placeWeight}(M,w)}.
$$

Lean uses `QI.badModuliFinset.attach` to carry the membership proof in each factor. The proof rewrites $P(a)$ as the standard-norm product of the chosen Tate roots. It substitutes the supplied values factor by factor using `hLogValue` and the standard-norm equality. [Representative product identity][product] · [Standard-norm product][standard-product] · [Arithmetic weight][weight]

### `log_normalized_sectionComparisonLogProduct_eq_sum_finite_packetVol`

The theorem takes `hModuli` and `TL` for `LocalConstruct.concreteLocalTheory (K := D.Kt)`. The premise `hModuli` equates the map $M\to K_t$ from `D.algebraModK` with the composite $M\to D.F\to K_t$. It also takes `QI`, `logValue`, and the same pointwise equality `hLogValue`.

Compute $m=(D.\ell-1)/2$ in the natural numbers. The exponent uses real division. Put `R := TL.rhsData`, and let $q_p$ be the finite rational place for the prime $p$ in `TL.badChars.attach`. Let $V_{i,p}$ be the packet log-volume `R.vol.packetVol` of `(R.thetaHull i).region qₚ` at capsule $i$ and place $q_p$. The proof substitutes the previous product identity for each capsule.

$$
\operatorname{Real.log}\!\left(
  \prod_{i\in\mathrm{Fin}(m)}\prod_{w\in B}
  \|J_{s(w)}(\operatorname{logValue}(w))\|_{\mathbb C_{p_{s(w)}}}^{
     ((i.\mathrm{val}+1)/m)^2\,\operatorname{placeWeight}(M,w)}
  \right)
  =\frac{\displaystyle\sum_{i\in\mathrm{Fin}(m)}\sum_{p\in\mathrm{TL.badChars}}V_{i,p}}{m^2}.
$$

[Normalized identity][normalized]

## 日本語

### `paperNormalizedQRootLog`

$K_t=D.\mathrm{Kt}$ とし、その任意の有限素点 $s$ の剰余標数を $p_s$ とする。$y_s=\mathrm{TL.qroot}(s)$ とおく。`paperNormalizedQRootLog TL s` は、実際の完備体 $K_{t,s}=\mathrm{LocalCompletion.completionAt}(K_t,s)$ の中で次の値を計算する。式中の $p_s^\ast$ はその完備体に移した元である。

$$
L_s=(p_s^\ast)^{-1}\operatorname{padicLog}(1+p_s^\ast y_s)
    \in K_{t,s},
\qquad
p_s^\ast=\begin{cases}4,&p_s=2,\\p_s,&p_s\ne 2.\end{cases}
$$

`LocalPadicLog.padicLog` は主単数上の通常の $p$ 進対数である。証明は `TL.ordp_qroot_nonneg s` から $\|y_s\|\le 1$ を得る。$p_s$ が素数で $\|p_s\|<1$ であることと `norm_paperNormalizedLog` を用いて、最初のノルムの等式を得る。`completionInPadicComplex s` を $J_s$ とする。標準ノルムを正の局所次数で冪乗すると完備体のノルムになるため、二つ目の等式が従う。

$$
\|L_s\|_{K_{t,s}}=\|y_s\|_{K_{t,s}},
\qquad
\|J_s(L_s)\|_{\mathbb C_{p_s}}=\|J_s(y_s)\|_{\mathbb C_{p_s}}.
$$

[対数の定義][ordinary] · [\(p^\ast\) による除法][scale] · [完備体のノルムの証明][local-norm] · [標準ノルムの証明][standard-norm] · [標準 \(\mathbb C_p\) への写像][embedding]

### `sectionQRootProduct_eq_comparisonLogProduct`

$M=\mathbb Q(j(D.E))$、$B=\mathrm{QI.badModuliFinset}$、$s(w)=D.\mathrm{localData.sect.sectFin}(w)$ とする。$w\in B$ の証明を伴う各モジュライ体の有限素点に対し、呼び出し側が `logValue w` を与える。仮定 `hLogValue w` は、同じ完備体の元についての等式を与える。

$$
\operatorname{logValue}(w)\in K_{t,s(w)},\qquad
\operatorname{logValue}(w)\overset{\mathrm{hLogValue}(w)}{=}L_{s(w)}.
$$

定理は任意の局所理論 `LT` に対する `TL`、`QI`、この値の族と各素点での等式、任意の実数指数 $a$ を受け取る。$P(a)=\mathrm{TL.sectionQRootProduct}(\mathrm{QI},a)$ とすると、次の等式が成り立つ。

$$
P(a)=
 \prod_{w\in B}
 \|J_{s(w)}(\operatorname{logValue}(w))\|_{\mathbb C_{p_{s(w)}}}^{
    a\,\operatorname{placeWeight}(M,w)}.
$$

Lean の積は `QI.badModuliFinset.attach` 上で取り、各因子に所属の証明を持たせる。証明は $P(a)$ を選ばれた Tate 根の標準ノルムの積に書き換え、`hLogValue` と標準ノルムの等式を用いて因子ごとに置換する。 [代表元の積の等式][product] · [標準ノルムによる積][standard-product] · [算術的な重み][weight]

### `log_normalized_sectionComparisonLogProduct_eq_sum_finite_packetVol`

定理は `hModuli` と `LocalConstruct.concreteLocalTheory (K := D.Kt)` に対する `TL` を仮定する。`hModuli` は `D.algebraModK` による $M\to K_t$ が合成 $M\to D.F\to K_t$ に等しいことを表す。`QI`、`logValue`、および各素点での同じ等式 `hLogValue` も入力である。

$m=(D.\ell-1)/2$ を自然数で計算する。指数の商には実数の除法を用いる。`R := TL.rhsData` とし、`TL.badChars.attach` の素数 $p$ に対応する有理数体の有限素点を $q_p$ とする。カプセル $i$ と素点 $q_p$ における `(R.thetaHull i).region qₚ` のパケット対数体積 `R.vol.packetVol` を $V_{i,p}$ とする。証明は各カプセルで直前の積の等式を代入する。

$$
\operatorname{Real.log}\!\left(
  \prod_{i\in\mathrm{Fin}(m)}\prod_{w\in B}
  \|J_{s(w)}(\operatorname{logValue}(w))\|_{\mathbb C_{p_{s(w)}}}^{
     ((i.\mathrm{val}+1)/m)^2\,\operatorname{placeWeight}(M,w)}
  \right)
  =\frac{\displaystyle\sum_{i\in\mathrm{Fin}(m)}\sum_{p\in\mathrm{TL.badChars}}V_{i,p}}{m^2}.
$$

[正規化した等式][normalized]

## 公开签名 · Public signatures · 公開シグネチャ

```lean
universe u v

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {D : InitialThetaData AG TG} {LT : LocalTheory.{u, v} D.Kt}
```

[声明上下文 · Declaration context · 宣言の文脈](../../../../Solutions/Source_ReferenceIutCor312RepresentativeComparisonLog.lean#L12)

```lean
noncomputable def paperNormalizedQRootLog (TL : ThetaLocalData D LT) (s : FinitePlace D.Kt) :
    LocalCompletion.completionAt D.Kt s
```

[Lean][ordinary]

```lean
theorem sectionQRootProduct_eq_comparisonLogProduct
    (TL : ThetaLocalData D LT) (QI : QPilotInputs D)
    (logValue : (w : QI.badModuliFinset) →
      LocalCompletion.completionAt D.Kt (D.localData.sect.sectFin w.1))
    (hLogValue : ∀ w, logValue w = TL.paperNormalizedQRootLog (D.localData.sect.sectFin w.1))
    (exponent : ℝ) :
    let M := ↥(fieldOfModuli D.F D.E)
    TL.sectionQRootProduct QI exponent =
      ∏ w ∈ QI.badModuliFinset.attach,
        ‖completionInPadicComplex (D.localData.sect.sectFin w.1) (logValue w)‖ ^
          (exponent * placeWeight M w.1)
```

[Lean][product]

```lean
theorem log_normalized_sectionComparisonLogProduct_eq_sum_finite_packetVol
    (hModuli : @algebraMap ↥(fieldOfModuli D.F D.E) D.Kt _ _ D.algebraModK =
      (algebraMap D.F D.Kt).comp (algebraMap ↥(fieldOfModuli D.F D.E) D.F))
    (TL : ThetaLocalData D (LocalConstruct.concreteLocalTheory (K := D.Kt)))
    (QI : QPilotInputs D)
    (logValue : (w : QI.badModuliFinset) →
      LocalCompletion.completionAt D.Kt (D.localData.sect.sectFin w.1))
    (hLogValue : ∀ w, logValue w = TL.paperNormalizedQRootLog (D.localData.sect.sectFin w.1)) :
    let m := (D.ℓ - 1) / 2
    let M := ↥(fieldOfModuli D.F D.E)
    let R := TL.rhsData
    Real.log (∏ i : Fin m, ∏ w ∈ QI.badModuliFinset.attach,
      ‖completionInPadicComplex (D.localData.sect.sectFin w.1) (logValue w)‖ ^
        ((((i.1 + 1 : ℕ) : ℝ) / (m : ℝ)) ^ 2 * placeWeight M w.1)) =
      (∑ i : Fin m, ∑ p ∈ TL.badChars.attach,
        let q := RationalPlace.finite ⟨p.1, TL.badChars_prime p.1 p.2⟩
        R.vol.packetVol i q ((R.thetaHull i).region q)) / (m : ℝ) ^ 2
```

[Lean][normalized]

[ordinary]: ../../../../Solutions/Source_ReferenceIutCor312RepresentativeComparisonLog.lean#L22
[local-norm]: ../../../../Solutions/Source_ReferenceIutCor312RepresentativeComparisonLog.lean#L27
[standard-norm]: ../../../../Solutions/Source_ReferenceIutCor312RepresentativeComparisonLog.lean#L40
[product]: ../../../../Solutions/Source_ReferenceIutCor312RepresentativeComparisonLog.lean#L55
[normalized]: ../../../../Solutions/Source_ReferenceIutCor312RepresentativeComparisonLog.lean#L73
[scale]: ../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalPadicPaperLog.lean#L19
[embedding]: ../../../../Solutions/Source_ReferenceIutCor312RepresentativePadicProduct.lean#L39
[standard-product]: ../../../../Solutions/Source_ReferenceIutCor312RepresentativePadicProduct.lean#L71
[weight]: ../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L78
