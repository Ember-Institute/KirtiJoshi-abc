# Joshi III 的标准点、Bloch–Kato 因子与 P7 代表元乘积

令 \(M\) 为模域，\(B\) 为坏模域有限处的集合，\(s(v)\) 为截面选取的挠点域有限处。记 \(r_v\) 为该处的 Tate 根，\(d_v=[K_{s(v)}:M_v]\)，\(m=(\ell-1)/2\)。P7 的代表元乘积等式为
\[
\log\!\left(\prod_{j=1}^m\prod_{v\in B}
  \|r_v\|_{\mathrm{Haar}}^{(j/m)^2/(d_v[M:\mathbb Q])}\right)
=\frac1{m^2}\sum_{j=1}^m\sum_p V_{j,p}.
\]
其中 \(V_{j,p}\) 是第 \(j\) 个胶囊在有限处 \(p\) 的实际包对数体积。原叶检查与联合公理审查分别通过 ci-026663-f887862b 和 ci-026672-29e2ba52。 [P7 等式](../../../../Solutions/Source_ReferenceIutCor312RepresentativeProduct.lean#L117) · [验收记录](../SOURCE_LEDGER.md#joshi-iii-的归一化乘积与规范-p7-的有限处包体积)

## 平方指数与标准点

Joshi III 式 (4.2.2.2) 把第 \(j\) 个赋值写成第一个赋值的 \(j^2\) 次幂。§4.5 将标准点放在第 \(m\) 个坐标。若用该坐标作底数，则 \(j^2/m^2\) 正好给出相对指数，Joshi II 用 \(K_m=\mathbb C_p\) 明确写出这个换算。Joshi III 式 (9.9.4)–(9.9.6) 的底数下标印为 \(1\)。令 \(j=1\)，式 (9.9.4) 字面即要求一个收缩范数 \(0<x<1\) 满足 \(x=x^{1/m^2}\)，而 \(m>1\)。P7 的 \((j/m)^2\) 采用与第 \(m\) 坐标一致的读法。 [第一个坐标的标度](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L1146>) · [标准点](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L1229>) · [式 (9.9.4)](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L3467>) · [Joshi II 的标准范数公式](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.tex#L1147>)

## 局部与全局次数

式 (9.9.6) 的原始乘积使用逐处逐坐标的范数。§9.10.5 对 Haar 因子采用局部权重 \(1/d_v\)。P7 另含全局因子 \(1/[M:\mathbb Q]\)。把同一个根映到标准 \(\mathbb C_p\) 后，现有范数定律及次数塔给出
\[
\|r_v\|_{\mathrm{Haar}}
   = |r_v|_{\mathbb C_p}^{[K_{s(v)}:\mathbb Q_p]},
\qquad
\frac{[K_{s(v)}:\mathbb Q_p]}{d_v[M:\mathbb Q]}
   =\frac{[M_v:\mathbb Q_p]}{[M:\mathbb Q]}.
\]
因此 P7 的每个标准范数因子带指数 \((j/m)^2[M_v:\mathbb Q_p]/[M:\mathbb Q]\)。模域为 \(\mathbb Q\) 时，次数比等于一。Scene1 的 actualPaperRootNorm 使用残余次数校正 \(\|r_v\|_{\mathrm{Haar}}^{1/f_{s(v)}}\)，在标准范数下对应 \(|r_v|_{\mathbb C_p}^{e_{s(v)}}\)。 [原始乘积](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L3471>) · [局部 Haar 权重](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L3552>) · [范数换算](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalCompletionAlgebraicPadicNorm.lean#L220) · [次数塔](../../../../Solutions/Source_TripodRelativeDegreeTower.lean#L71) · [残余次数校正](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaPaperRelativeNormBridge.lean#L25)

## Bloch–Kato 归一化

Joshi III 式 (9.9.2)–(9.9.3) 使用 \(\log(1+p^*r)/p^*\) 作为所列 Bloch–Kato 类的像。\(p^*=p\) 对应奇素数，\(p^*=4\) 对应 \(2\)。普通 p-adic 对数的范数恒等式已经证明该表达式与 \(r\) 同范数。归一化审查还证明，原整 Kummer 类在小球校准的普通对数下给出该表达式的 \(p^*\) 倍，在除以 \(p^*\) 的比较映射下给出该表达式。要把数值等式用于论文的 Form 2，需要识别实际 \(H^1_e\) 类及其归一化，将该类运送到各 untilt 并证实相应张量区域的包络包含。 [论文的对数公式](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L3226>) · [普通范数恒等式](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalPadicPaperLog.lean#L50) · [归一化审查](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaBlochKatoNormalizationAudit.lean#L42) · [Form 2 所用的张量区域](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L3624>)
