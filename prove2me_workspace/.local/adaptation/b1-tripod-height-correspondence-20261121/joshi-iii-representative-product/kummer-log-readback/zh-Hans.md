# Cor. 3.12 代表元的 Kummer 对数声明核读

以下六个声明对应审查任务 `ci-026827-16c29d38` 记录的源码版本。[Lean 源码](../../../../../Solutions/Source_ReferenceIutCor312RepresentativeKummerLog.lean#L40) · [MCP-CI 回执](../ci-026827-16c29d38.result.json)

前五个声明取任意 `TL : ThetaLocalData D LT` 和 `D.Kt` 的任意有限位 $s$。记 $K_s=(D.\mathrm{Kt})_s$、$p_s=\operatorname{residueChar}(s)$、$r_s=\mathrm{TL.qroot}(s)$。当 $p_s=2$ 时令 $p_s^*=4$，否则令 $p_s^*=p_s$。

## 1. `paperQRootPrincipalUnit`

在 $K_s^\times$ 的主单位子群中构造 $u_s=1+p_s^*r_s$。由 $\lVert r_s\rVert\le 1$ 得到 $\lVert u_s-1\rVert<1$，并构造 $u_s$ 的可逆元表示。

## 2. `paperQRootKummerClass`

对 $u_s$ 施用 `LocalKummer.Rational.kummerHom`，取其加法类 $c_s$。所用代数闭包为 `AlgebraicClosure K_s`，类 $c_s$ 属于连续 Galois 上同调 $H^1(G_{K_s},\mathbb Q_{p_s}(1))$。

## 3. `ambientLog_paperQRootKummerClass`

通常的环境 Kummer 对数 `LocalCompletion.KummerValuation.ambientLog` 在 $c_s$ 上的值等于 $u_s$ 的 $p_s$ 进对数。等式的两边都在 $K_s$ 中。

$$
\operatorname{ambientLog}_s(c_s)=\log_{p_s}(1+p_s^*r_s).
$$

## 4. `paperQRootKummerLog`

在 $K_s$ 中将环境 Kummer 对数乘以 $(p_s^*)^{-1}$，定义归一化值 $L_s$。

$$
L_s=(p_s^*)^{-1}\operatorname{ambientLog}_s(c_s).
$$

## 5. `paperQRootKummerLog_eq_paperNormalizedQRootLog`

证明 $L_s$ 等于已有的 `TL.paperNormalizedQRootLog s`。该式把第四个声明的上同调构造与解析表达式 $(p_s^*)^{-1}\log_{p_s}(1+p_s^*r_s)$ 对齐。

## 6. `log_normalized_sectionKummerLogProduct_eq_sum_finite_packetVol`

此处 `TL` 基于 `LocalConstruct.concreteLocalTheory (K := D.Kt)`，并给定 `QI : QPilotInputs D`。记 $M=\operatorname{fieldOfModuli}(D.F,D.E)$。假设 `hModuli` 断言由 `D.algebraModK` 指定的 $M\to D.\mathrm{Kt}$ 代数映射等于 $M\to D.F\to D.\mathrm{Kt}$ 的复合。

记 $m=(D.\ell-1)/2$，其计算在自然数中进行。对 $w\in\mathrm{QI.badModuliFinset}$，以 `D.localData.sect.sectFin` 取 P7 代表位 $s(w)$。设 $\iota_s=\mathrm{completionInPadicComplex}(s)$，乘积中的范数是目标 $\mathbb C_{p_s}$ 的标准范数。对于 $p\in\mathrm{TL.badChars}$，记其对应的有理有限位为 $q_p$。设 `R := TL.rhsData`，用 $V_R(i,q_p)$ 表示 `R.vol.packetVol i q_p ((R.thetaHull i).region q_p)`。

$$
\log_{\mathbb R}\!\left(
 \prod_{i\in\operatorname{Fin}(m)}
 \prod_{w\in\mathrm{QI.badModuliFinset}}
 \bigl\lVert\iota_{s(w)}(L_{s(w)})\bigr\rVert^{((i+1)/m)^2\operatorname{placeWeight}(M,w)}
\right)
=
\frac{\displaystyle\sum_{i\in\operatorname{Fin}(m)}
 \sum_{p\in\mathrm{TL.badChars}} V_R(i,q_p)}{m^2}.
$$

指数中的 $i+1$ 取 `Fin m` 的自然数值再转为实数，$m$ 在指数及右侧分母中也转为实数。

## 周期环比较可复用的单位判据

以下定理位于 `JoshiTeich.Act1Scene1.LocalCompletion`。在数域 $K$ 的有限位 $w$ 取剩余特征 $p$ 及代数闭包 $\Omega$。其 Lean 声明如下。[LocalCompletionKummerUnitCriterion.lean](../../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalCompletionKummerUnitCriterion.lean#L97)

```lean
theorem rationalKummer_mem_saturated_iff_norm_eq_one
    (hpw : Arithmetic.residueChar w = p) (a : (completionAt K w)ˣ) :
    (LocalKummer.Rational.kummerHom (Ω := Ω) p a).toAdd ∈
      LocalPadicLog.saturatedKummerImage p ↔ ‖(a : completionAt K w)‖ = 1
```

以 $w=s$、$p=p_s$、$a=u_s$ 代入。第一项的主单位界给出 $\lVert u_s\rVert=1$，从而 $c_s$ 属于 `saturatedKummerImage p_s`。

证明真正的 $H^1_e$ 成员性还需证明 $c_s$ 在将系数扩张到 $B_{\mathrm{cris}}^{\varphi=1}\otimes_{\mathbb Q_{p_s}}\mathbb Q_{p_s}(1)$ 后变为零。论文中的对数公式还需与 Bloch–Kato 指数映射的逆比较，并核对 $p_s^*$ 的归一化。[论文的成员性陈述](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3199>) · [论文的对数公式](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3226>)
