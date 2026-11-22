# Cor. 3.12 の代表元に対する Kummer 対数の宣言

以下の六つの宣言は、レビュー `ci-026827-16c29d38` に記録されたソースに対応する。[Lean ソース](../../../../../Solutions/Source_ReferenceIutCor312RepresentativeKummerLog.lean#L40) · [MCP-CI レビュー結果](../ci-026827-16c29d38.result.json)

最初の五つの宣言は、任意の `TL : ThetaLocalData D LT` と `D.Kt` の任意の有限素点 $s$ に適用できる。$K_s=(D.\mathrm{Kt})_s$、$p_s=\operatorname{residueChar}(s)$、$r_s=\mathrm{TL.qroot}(s)$ とおく。$p_s=2$ のとき $p_s^*=4$ とし、それ以外のとき $p_s^*=p_s$ とする。

## 1. `paperQRootPrincipalUnit`

$K_s^\times$ の主単数群の元として $u_s=1+p_s^*r_s$ を構成する。$\lVert r_s\rVert\le 1$ から $\lVert u_s-1\rVert<1$ が従う。

## 2. `paperQRootKummerClass`

$u_s$ に `LocalKummer.Rational.kummerHom` を適用し、加法表記での類 $c_s$ を取る。代数閉包には `AlgebraicClosure K_s` を用いる。$c_s$ は連続 Galois コホモロジー $H^1(G_{K_s},\mathbb Q_{p_s}(1))$ の元である。

## 3. `ambientLog_paperQRootKummerClass`

連続コホモロジー全体に定義された通常の Kummer 対数 `LocalCompletion.KummerValuation.ambientLog` を $c_s$ に適用すると、$K_s$ における $u_s$ の $p_s$ 進対数を得る。

$$
\operatorname{ambientLog}_s(c_s)=\log_{p_s}(1+p_s^*r_s).
$$

## 4. `paperQRootKummerLog`

通常の Kummer 対数に $K_s$ 内で $(p_s^*)^{-1}$ を掛け、正規化した値 $L_s$ を定義する。

$$
L_s=(p_s^*)^{-1}\operatorname{ambientLog}_s(c_s).
$$

## 5. `paperQRootKummerLog_eq_paperNormalizedQRootLog`

$L_s$ が既存の `TL.paperNormalizedQRootLog s` と等しいことを示す。後者は解析的な式 $(p_s^*)^{-1}\log_{p_s}(1+p_s^*r_s)$ で与えられる。

## 6. `log_normalized_sectionKummerLogProduct_eq_sum_finite_packetVol`

`LocalConstruct.concreteLocalTheory (K := D.Kt)` 上の `TL` と `QI : QPilotInputs D` をとる。モジュライ体を $M=\operatorname{fieldOfModuli}(D.F,D.E)$ とおく。仮定 `hModuli` は、`D.algebraModK` による代数準同型 $M\to D.\mathrm{Kt}$ が合成 $M\to D.F\to D.\mathrm{Kt}$ に等しいことを表す。

$m=(D.\ell-1)/2$ は自然数で計算する。各 $w\in\mathrm{QI.badModuliFinset}$ に対し、P7 が `D.localData.sect.sectFin` で選ぶ代表素点を $s(w)$ とする。$\iota_s=\mathrm{completionInPadicComplex}(s)$ とおく。積には写像先 $\mathbb C_{p_s}$ の標準ノルムを用いる。各 $p\in\mathrm{TL.badChars}$ に対応する有理有限素点を $q_p$ とする。`R := TL.rhsData` とし、`R.vol.packetVol i q_p ((R.thetaHull i).region q_p)` を $V_R(i,q_p)$ と書く。

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

指数の $i+1$ は $i$ の自然数値に $1$ を足してから実数に移す。指数と右辺の分母では $m$ も実数に移す。

## 周期環との比較に使える単数判定

以下の定理は `JoshiTeich.Act1Scene1.LocalCompletion` にある。数体 $K$ の有限素点 $w$、その剰余標数 $p$、完備化の代数閉包 $\Omega$ をとる。[LocalCompletionKummerUnitCriterion.lean](../../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalCompletionKummerUnitCriterion.lean#L97)

```lean
theorem rationalKummer_mem_saturated_iff_norm_eq_one
    (hpw : Arithmetic.residueChar w = p) (a : (completionAt K w)ˣ) :
    (LocalKummer.Rational.kummerHom (Ω := Ω) p a).toAdd ∈
      LocalPadicLog.saturatedKummerImage p ↔ ‖(a : completionAt K w)‖ = 1
```

$w=s$、$p=p_s$、$a=u_s$ とする。主単数の条件から $\lVert u_s\rVert=1$ が従うので、この定理により $c_s$ は `saturatedKummerImage p_s` に属する。

$H^1_e$ への所属には、係数を $B_{\mathrm{cris}}^{\varphi=1}\otimes_{\mathbb Q_{p_s}}\mathbb Q_{p_s}(1)$ に拡大したときに $c_s$ が零に写ることを示す必要がある。論文の対数公式には、Bloch–Kato 指数写像の逆写像との比較と $p_s^*$ による正規化の確認も必要となる。[論文の所属条件](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3199>) · [論文の対数公式](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3226>)
