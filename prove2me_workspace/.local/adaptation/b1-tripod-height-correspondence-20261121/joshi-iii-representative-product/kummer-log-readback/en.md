# Kummer logarithms for the representatives in Cor. 3.12

This readback uses the source version recorded in review `ci-026827-16c29d38`. [Lean source](../../../../../Solutions/Source_ReferenceIutCor312RepresentativeKummerLog.lean#L40) · [MCP-CI receipt](../ci-026827-16c29d38.result.json)

The first five declarations use any `TL : ThetaLocalData D LT` and any finite place $s$ of `D.Kt`. Let $K_s=(D.\mathrm{Kt})_s$, $p_s=\operatorname{residueChar}(s)$, and $r_s=\mathrm{TL.qroot}(s)$. Set $p_s^*=4$ if $p_s=2$ and $p_s^*=p_s$ otherwise.

## 1. `paperQRootPrincipalUnit`

This definition constructs $u_s=1+p_s^*r_s$ in the principal unit subgroup of $K_s^\times$. The bound $\lVert r_s\rVert\le 1$ gives $\lVert u_s-1\rVert<1$.

## 2. `paperQRootKummerClass`

This definition applies `LocalKummer.Rational.kummerHom` to $u_s$ and takes its additive class $c_s$. It uses `AlgebraicClosure K_s` for the algebraic closure. The class lies in the continuous Galois cohomology group $H^1(G_{K_s},\mathbb Q_{p_s}(1))$.

## 3. `ambientLog_paperQRootKummerClass`

The ordinary ambient Kummer logarithm `LocalCompletion.KummerValuation.ambientLog` sends $c_s$ to the $p_s$-adic logarithm of $u_s$ in $K_s$.

$$
\operatorname{ambientLog}_s(c_s)=\log_{p_s}(1+p_s^*r_s).
$$

## 4. `paperQRootKummerLog`

This definition multiplies the ordinary ambient Kummer logarithm by $(p_s^*)^{-1}$ in $K_s$. Its value is

$$
L_s=(p_s^*)^{-1}\operatorname{ambientLog}_s(c_s).
$$

## 5. `paperQRootKummerLog_eq_paperNormalizedQRootLog`

The theorem equates $L_s$ with `TL.paperNormalizedQRootLog s`. The latter has the analytic formula $(p_s^*)^{-1}\log_{p_s}(1+p_s^*r_s)$.

## 6. `log_normalized_sectionKummerLogProduct_eq_sum_finite_packetVol`

The theorem takes `TL` on `LocalConstruct.concreteLocalTheory (K := D.Kt)` and `QI : QPilotInputs D`. Let $M=\operatorname{fieldOfModuli}(D.F,D.E)$. The hypothesis `hModuli` equates the algebra map $M\to D.\mathrm{Kt}$ from `D.algebraModK` with the composite $M\to D.F\to D.\mathrm{Kt}$.

Let $m=(D.\ell-1)/2$, with division in the natural numbers. For $w\in\mathrm{QI.badModuliFinset}$, let $s(w)$ be the representative place that P7 selects with `D.localData.sect.sectFin`. Write $\iota_s=\mathrm{completionInPadicComplex}(s)$. The product uses the standard norm of the target $\mathbb C_{p_s}$. For $p\in\mathrm{TL.badChars}$, let $q_p$ be its rational finite place. Set `R := TL.rhsData` and let $V_R(i,q_p)$ mean `R.vol.packetVol i q_p ((R.thetaHull i).region q_p)`.

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

In the exponent, $i+1$ uses the natural number value of $i$ and then casts to $\mathbb R$. The exponent and the denominator on the right also use the real value of $m$.

## Unit criterion for the period-ring comparison

The following theorem is in `JoshiTeich.Act1Scene1.LocalCompletion`. Take a finite place $w$ of a number field $K$, its residue prime $p$, and an algebraic closure $\Omega$ of the completion. [LocalCompletionKummerUnitCriterion.lean](../../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalCompletionKummerUnitCriterion.lean#L97)

```lean
theorem rationalKummer_mem_saturated_iff_norm_eq_one
    (hpw : Arithmetic.residueChar w = p) (a : (completionAt K w)ˣ) :
    (LocalKummer.Rational.kummerHom (Ω := Ω) p a).toAdd ∈
      LocalPadicLog.saturatedKummerImage p ↔ ‖(a : completionAt K w)‖ = 1
```

Set $w=s$, $p=p_s$, and $a=u_s$. The principal unit bound gives $\lVert u_s\rVert=1$. The criterion then gives $c_s\in\mathrm{saturatedKummerImage}(p_s)$.

The $H^1_e$ membership proof requires $c_s$ to map to zero after scalar extension to $B_{\mathrm{cris}}^{\varphi=1}\otimes_{\mathbb Q_{p_s}}\mathbb Q_{p_s}(1)$. The paper's logarithm formula requires a comparison with the inverse Bloch–Kato exponential and its $p_s^*$ normalization. [Membership in the paper](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3199>) · [Logarithm formula in the paper](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3226>)
