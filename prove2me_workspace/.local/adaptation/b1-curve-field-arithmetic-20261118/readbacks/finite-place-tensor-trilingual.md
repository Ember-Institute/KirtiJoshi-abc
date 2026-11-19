# Finite-place tensor packets

## English

### Common setup

Let $K$ be a number field, $p$ a rational prime, and $c$ a tuple of places of $K$ indexed by a finite type $I$. A place lies over $p$ if it is finite with residue characteristic $p$. Write $A$ for the packet `Tensor K (.finite p) c`. When every entry lies over $p$, the specified equivalence identifies the tensor of the completions over $\mathbb Q_p$ with $A$. If some entry fails this condition, $A$ is the zero ring. Write $R$ for the integral closure of $\mathbb Z_p$ in $A$ and $aR$ for its image under multiplication by $a$. [Packet and places over p](../../../../Solutions/Source_ReferenceIutConcreteLocalPacket.lean#L35) · [Packet equivalence](../../../../Solutions/Source_ReferenceIutConcreteLocalPacketEquiv.lean#L77) · [Integral closure](../../../../Solutions/Source_ReferenceIutConcreteLocalIntegral.lean#L147)

### Finite Haar measure and least hull

Let $\mu$ be the additive Haar measure `finiteHaar p c` on the Borel sets of $A$. The integral closure has $0<\mu(R)<\infty$. For each $a\in A$, the set $aR$ is compact and measurable and has finite measure. If $a$ is a unit, that measure is positive. [Additive Haar measure](../../../../Solutions/Source_ReferenceIutConcreteLocalHaar.lean#L43) · [Compactness and measurability](../../../../Solutions/Source_ReferenceIutConcreteLocalHaar.lean#L58) · [Measure of a unit multiple](../../../../Solutions/Source_ReferenceIutConcreteLocalHaar.lean#L67)

Let $n=\dim_{\mathbb Q_p}A$. The normalized log-volume `finiteComponentVol p c` is the real-valued function $V$ defined on sets $S\subseteq A$ by the following formula.

$$
V(S)=\frac{\log\!\left(\operatorname{toReal}(\mu(S))/\operatorname{toReal}(\mu(R))\right)}{n}.
$$

Here `toReal` is Lean's conversion from extended nonnegative reals, and $\log$ is the real natural logarithm. In particular, $V(R)=0$. For units $a,b\in A^\times$, the inclusion $aR\subseteq bR$ gives $V(aR)\le V(bR)$. If some entry of $c$ fails to lie over $p$, then $n=0$ and $V(S)=0$ for every $S$ under Lean's real division convention. [Log-volume and monotonicity](../../../../Solutions/Source_ReferenceIutConcreteLocalHaar.lean#L80) · [Zero-ring volume](../../../../Solutions/Source_ReferenceIutConcreteLocalHaar.lean#L98)

Let $m_p$ be multiplication by $p$ on $A$. For measurable $U\subseteq A$, `finiteHaar_prime_preimage` gives the first formula below in the extended nonnegative reals. For the second formula, `finiteComponentVol_prime_preimage` also requires every entry of $c$ to lie over $p$ and $0<\mu(U)<\infty$.

$$
\mu(m_p^{-1}(U))=p^n\mu(U),\qquad
V(m_p^{-1}(U))=V(U)+\log p.
$$

[Raw Haar preimage](../../../../Solutions/Source_ReferenceIutConcreteLocalHaar.lean#L113) · [Log-volume preimage](../../../../Solutions/Source_ReferenceIutConcreteLocalHaar.lean#L124)

A set $U\subseteq A$ belongs to `finiteAdmissible p c` if it is nonempty and measurable, its closure is compact, and $0<\mu(U)<\infty$. The sets $R$ and $aR$ for each unit $a$ satisfy these conditions. For admissible $U$ and with all entries over $p$, `finiteComponentVol_prime_preimage_of_admissible` gives the same increase of $\log p$ under $m_p^{-1}$. [Admissible regions](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteHull.lean#L39) · [Admissible preimage law](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteHull.lean#L62)

For each admissible $U$, `exists_leastHull_finite` gives a unit $a\in A^\times$ with the following inclusions. The statement applies to every tuple $c$. In the zero-ring case the construction takes $a=1$ and $R=A$.

$$
U\subseteq aR,\qquad
\forall b\in A^\times,\quad U\subseteq bR\ \Longrightarrow\ aR\subseteq bR.
$$

[Least hull](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteHull.lean#L124)

### Finite indeterminacy

Write $\mathcal A$ for `finiteIndAut p c`. When all entries lie over $p$, choose a $\mathbb Q_p$-algebra automorphism of each completion separately. Apply these automorphisms to their tensor factors and transport the resulting map to $A$ along the specified packet equivalence. The set $\mathcal A$ consists of the maps obtained this way. In the zero-ring case it consists of the identity map. [Finite indeterminacy set](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteIndeterminacy.lean#L46) · [Factor automorphisms](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalCompletionTensorIndeterminacy.lean#L112)

The identity belongs to $\mathcal A$. This set is finite, and every $\phi\in\mathcal A$ is the underlying function of a $\mathbb Q_p$-algebra automorphism of $A$. Proposition 1.4(iv), `prop14_iv`, gives $\phi(R)\subseteq R$ for each such $\phi$ at every rational prime. [Identity and finiteness](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteIndeterminacy.lean#L56) · [Algebra automorphisms](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteIndeterminacy.lean#L72) · [Proposition 1.4(iv)](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteIndeterminacy.lean#L112)

If $S\subseteq A$ is compact and $\mu(S)>0$, the union $\bigcup_{\phi\in\mathcal A}\phi(S)$ is admissible. In particular, for every $a\in A^\times$, `theta_admissible_finite` gives admissibility of $\bigcup_{\phi\in\mathcal A}\phi(aR)$. [Compact sets and unit multiples](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteIndeterminacy.lean#L93)

### The finite log-shell

Write $\mathcal L$ for `finiteLogShell p c`. When all entries lie over $p$, take the tensor log-shell of the actual completions, take its span as a module over the normalization in that tensor, and transport this set to $A$ along the packet equivalence. For a zero-ring packet, $\mathcal L=R$. [Finite log-shell](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteLogShell.lean#L30) · [Normalization span](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalCompletionTensorSaturatedLogShell.lean#L91)

For every tuple, $\overline{\mathcal L}$ is compact and $R\subseteq\mathcal L$. If $p$ is odd and every entry of $c$ that is a finite place $w$ has absolute ramification index $1$, then $\mathcal L=R$. [Compactness and containment](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteLogShell.lean#L49) · [Odd unramified equality](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteLogShell.lean#L60)

For each $\phi\in\mathcal A$, `finiteIndAut_logShell` gives $\phi(\mathcal L)\subseteq\mathcal L$. The union $\bigcup_{\phi\in\mathcal A}\phi(\mathcal L)$ is admissible. [Log-shell images and admissibility](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteLogShell.lean#L76)

### Proposition 1.4(iii)

Assume every entry of $c$ lies over $p$. Fix $j\in I$ and a finite place $w$ with `c j = Place.finite w`. Take $x\in K_w$ with $x\ne0$. Require $\lambda=\operatorname{ord}_p(x)\ge0$, with the normalization $\operatorname{ord}_p(p)=1$. Write $\operatorname{incl}_j:K_w\to A$ for the factor inclusion from this equality of places. [Factor inclusion](../../../../Solutions/Source_ReferenceIutConcreteLocalPacket.lean#L400) · [Normalized valuation](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L87)

Take $d:I\to\mathbb R$. For every $i\in I$ and finite place $w'$ with `c i = Place.finite w'`, require $d(i)=\operatorname{differentExponent}(K,w')$. This exponent is the multiplicity of the prime of $w'$ in the absolute different ideal of $K$, divided by the absolute ramification index of $w'$. Write $e_i$ for the absolute ramification index of the place $c(i)$. [Normalized different exponent](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L105)

The theorem `prop14iii_of_isOver` gives a unit $a\in A^\times$ with the following inclusions and bound.

$$
\forall\,\phi\in\mathcal A,\quad \phi\bigl(\operatorname{incl}_j(x)R\bigr)\subseteq aR,\qquad
V(aR)\le
\left(-\lambda+\sum_{i\in I}d(i)+1\right)\log p
 +\sum_{\substack{i\in I\\p-2<e_i}}\bigl(3+\log e_i\bigr).
$$

The subtraction in $p-2<e_i$ is in $\mathbb N$. The proof takes $a=p^{\lfloor\lambda\rfloor}$ in $A$, where the floor is a natural number. For this choice $V(aR)=-\lfloor\lambda\rfloor\log p$. [Proposition 1.4(iii)](../../../../Solutions/Source_ReferenceIutConcreteLocalProp14.lean#L103) · [Choice of the unit](../../../../Solutions/Source_ReferenceIutConcreteLocalProp14.lean#L116) · [Log-volume of a prime power](../../../../Solutions/Source_ReferenceIutConcreteLocalProp14.lean#L59)

## 中文

### 共同设定

设 $K$ 为数域，$p$ 为有理素数，$c$ 为以有限类型 $I$ 为指标的 $K$ 的位的元组。位于 $p$ 上方的位是剩余特征为 $p$ 的有限位。记 $A$ 为张量包 `Tensor K (.finite p) c`。若每一项都位于 $p$ 上方，指定的同构将各完备化在 $\mathbb Q_p$ 上的张量积识别为 $A$。若某一项不满足此条件，$A$ 是零环。记 $R$ 为 $\mathbb Z_p$ 在 $A$ 中的整闭包，$aR$ 为 $R$ 在乘以 $a$ 的映射下的像。 [张量包与位于 p 上方的位](../../../../Solutions/Source_ReferenceIutConcreteLocalPacket.lean#L35) · [张量包同构](../../../../Solutions/Source_ReferenceIutConcreteLocalPacketEquiv.lean#L77) · [整闭包](../../../../Solutions/Source_ReferenceIutConcreteLocalIntegral.lean#L147)

### 有限处 Haar 测度与最小包络

记 $\mu$ 为 $A$ 上的加法 Haar 测度 `finiteHaar p c`，取 Borel 可测结构。整闭包满足 $0<\mu(R)<\infty$。对任意 $a\in A$，集合 $aR$ 紧致、可测且测度有限。若 $a$ 为单位，则该测度为正。 [加法 Haar 测度](../../../../Solutions/Source_ReferenceIutConcreteLocalHaar.lean#L43) · [紧致性与可测性](../../../../Solutions/Source_ReferenceIutConcreteLocalHaar.lean#L58) · [单位倍的测度](../../../../Solutions/Source_ReferenceIutConcreteLocalHaar.lean#L67)

令 $n=\dim_{\mathbb Q_p}A$。归一化对数体积 `finiteComponentVol p c` 是定义在集合 $S\subseteq A$ 上的实值函数 $V$，其定义为

$$
V(S)=\frac{\log\!\left(\operatorname{toReal}(\mu(S))/\operatorname{toReal}(\mu(R))\right)}{n}.
$$

其中 `toReal` 是 Lean 从扩展非负实数到实数的转换，$\log$ 是实自然对数。特别地，$V(R)=0$。若 $a,b\in A^\times$ 且 $aR\subseteq bR$，则 $V(aR)\le V(bR)$。若 $c$ 有某一项不位于 $p$ 上方，则 $n=0$，按 Lean 的实数除法约定，对所有 $S$ 都有 $V(S)=0$。 [对数体积与单调性](../../../../Solutions/Source_ReferenceIutConcreteLocalHaar.lean#L80) · [零环的体积](../../../../Solutions/Source_ReferenceIutConcreteLocalHaar.lean#L98)

令 $m_p$ 为 $A$ 上乘以 $p$ 的映射。对任意可测 $U\subseteq A$，`finiteHaar_prime_preimage` 给出下列第一个等式，取值于扩展非负实数。第二个等式由 `finiteComponentVol_prime_preimage` 给出，还需 $c$ 的每一项都位于 $p$ 上方且 $0<\mu(U)<\infty$。

$$
\mu(m_p^{-1}(U))=p^n\mu(U),\qquad
V(m_p^{-1}(U))=V(U)+\log p.
$$

[Haar 测度的原像公式](../../../../Solutions/Source_ReferenceIutConcreteLocalHaar.lean#L113) · [对数体积的原像公式](../../../../Solutions/Source_ReferenceIutConcreteLocalHaar.lean#L124)

集合 $U\subseteq A$ 属于 `finiteAdmissible p c`，当且仅当它非空、可测、闭包紧致且 $0<\mu(U)<\infty$。$R$ 及每个单位 $a$ 对应的 $aR$ 均满足这些条件。若 $U$ 可容许且所有项都位于 $p$ 上方，`finiteComponentVol_prime_preimage_of_admissible` 给出 $m_p^{-1}$ 下同样的 $\log p$ 增量。 [可容许区域](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteHull.lean#L39) · [可容许情形的原像公式](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteHull.lean#L62)

对每个可容许的 $U$，`exists_leastHull_finite` 给出单位 $a\in A^\times$，满足以下包含关系。该陈述适用于任意元组 $c$。在零环情形，构造取 $a=1$ 且 $R=A$。

$$
U\subseteq aR,\qquad
\forall b\in A^\times,\quad U\subseteq bR\ \Longrightarrow\ aR\subseteq bR.
$$

[最小包络](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteHull.lean#L124)

### 有限处的不定性

记 $\mathcal A$ 为 `finiteIndAut p c`。若所有项都位于 $p$ 上方，分别取各完备化的一个 $\mathbb Q_p$-代数自同构，在张量积中逐因子作用，再通过指定的张量包同构将所得映射传到 $A$。$\mathcal A$ 由这些映射组成。零环情形的 $\mathcal A$ 只含恒等映射。 [有限的不定性映射集](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteIndeterminacy.lean#L46) · [因子自同构](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalCompletionTensorIndeterminacy.lean#L112)

恒等映射属于 $\mathcal A$。该集合有限，其中每个 $\phi$ 都是 $A$ 的某个 $\mathbb Q_p$-代数自同构的底层函数。对任意有理素数及任意这样的 $\phi$，命题 1.4(iv) 对应的 `prop14_iv` 给出 $\phi(R)\subseteq R$。 [恒等映射与有限性](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteIndeterminacy.lean#L56) · [代数自同构](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteIndeterminacy.lean#L72) · [命题 1.4(iv)](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteIndeterminacy.lean#L112)

若 $S\subseteq A$ 紧致且 $\mu(S)>0$，则并集 $\bigcup_{\phi\in\mathcal A}\phi(S)$ 可容许。特别地，对任意单位 $a\in A^\times$，`theta_admissible_finite` 给出 $\bigcup_{\phi\in\mathcal A}\phi(aR)$ 的可容许性。 [紧集与单位倍](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteIndeterminacy.lean#L93)

### 有限处的对数壳

记 $\mathcal L$ 为 `finiteLogShell p c`。若所有项都位于 $p$ 上方，在各实际完备化的张量积中取张量对数壳，再取它在该张量积的归一化环上生成的子模，并通过张量包同构将此集合传到 $A$。若张量包为零环，则 $\mathcal L=R$。 [有限处的对数壳](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteLogShell.lean#L30) · [归一化环上的生成子模](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalCompletionTensorSaturatedLogShell.lean#L91)

对每个元组，$\overline{\mathcal L}$ 紧致，且 $R\subseteq\mathcal L$。若 $p$ 为奇素数，且 $c$ 中每一项只要是有限位 $w$，其绝对分歧指数就等于 $1$，则 $\mathcal L=R$。 [紧致性与包含关系](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteLogShell.lean#L49) · [奇素数且分歧指数为一时的等式](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteLogShell.lean#L60)

对每个 $\phi\in\mathcal A$，`finiteIndAut_logShell` 给出 $\phi(\mathcal L)\subseteq\mathcal L$。并集 $\bigcup_{\phi\in\mathcal A}\phi(\mathcal L)$ 可容许。 [对数壳的像与可容许性](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteLogShell.lean#L76)

### 命题 1.4(iii)

假设 $c$ 的每一项都位于 $p$ 上方。固定 $j\in I$、有限位 $w$ 与等式 `c j = Place.finite w`。取非零的 $x\in K_w$，要求 $\lambda=\operatorname{ord}_p(x)\ge0$，其中 $\operatorname{ord}_p(p)=1$。记 $\operatorname{incl}_j:K_w\to A$ 为由该位的等式给出的张量因子嵌入。 [因子嵌入](../../../../Solutions/Source_ReferenceIutConcreteLocalPacket.lean#L400) · [归一化赋值](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L87)

取 $d:I\to\mathbb R$。对每个 $i\in I$ 及满足 `c i = Place.finite w'` 的有限位 $w'$，要求 $d(i)=\operatorname{differentExponent}(K,w')$。该指数是 $w'$ 对应素理想在 $K$ 的绝对不同理想中的重数，除以 $w'$ 的绝对分歧指数。令 $e_i$ 为 $c(i)$ 的绝对分歧指数。 [归一化不同指数](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L105)

定理 `prop14iii_of_isOver` 给出单位 $a\in A^\times$，满足以下包含关系与上界。

$$
\forall\,\phi\in\mathcal A,\quad \phi\bigl(\operatorname{incl}_j(x)R\bigr)\subseteq aR,\qquad
V(aR)\le
\left(-\lambda+\sum_{i\in I}d(i)+1\right)\log p
 +\sum_{\substack{i\in I\\p-2<e_i}}\bigl(3+\log e_i\bigr).
$$

$p-2<e_i$ 中的减法在 $\mathbb N$ 中进行。证明在 $A$ 中选取 $a=p^{\lfloor\lambda\rfloor}$，其中下取整值是自然数。此时 $V(aR)=-\lfloor\lambda\rfloor\log p$。 [命题 1.4(iii)](../../../../Solutions/Source_ReferenceIutConcreteLocalProp14.lean#L103) · [单位的选取](../../../../Solutions/Source_ReferenceIutConcreteLocalProp14.lean#L116) · [素数幂倍的对数体积](../../../../Solutions/Source_ReferenceIutConcreteLocalProp14.lean#L59)

## 日本語

### 共通の設定

$K$ を数体、$p$ を有理素数、$c$ を有限型 $I$ で添字付けられた $K$ の素点の組とする。$p$ の上にある素点とは、剰余標数 $p$ の有限素点である。`Tensor K (.finite p) c` を $A$ と書く。すべての成分が $p$ の上にあれば、指定された同型により、各完備化の $\mathbb Q_p$ 上のテンソル積を $A$ と同一視できる。この条件を満たさない成分があれば、$A$ は零環である。$A$ における $\mathbb Z_p$ の整閉包を $R$ とし、$a$ による乗法での $R$ の像を $aR$ と書く。 [テンソルと p の上の素点](../../../../Solutions/Source_ReferenceIutConcreteLocalPacket.lean#L35) · [テンソルの同型](../../../../Solutions/Source_ReferenceIutConcreteLocalPacketEquiv.lean#L77) · [整閉包](../../../../Solutions/Source_ReferenceIutConcreteLocalIntegral.lean#L147)

### 有限素点での Haar 測度と最小包絡

$A$ のボレル可測構造上の加法的 Haar 測度 `finiteHaar p c` を $\mu$ とする。整閉包について $0<\mu(R)<\infty$ が成り立つ。任意の $a\in A$ に対して $aR$ はコンパクトかつ可測で、測度は有限である。$a$ が単元ならば、この測度は正である。 [加法的 Haar 測度](../../../../Solutions/Source_ReferenceIutConcreteLocalHaar.lean#L43) · [コンパクト性と可測性](../../../../Solutions/Source_ReferenceIutConcreteLocalHaar.lean#L58) · [単元倍の測度](../../../../Solutions/Source_ReferenceIutConcreteLocalHaar.lean#L67)

$n=\dim_{\mathbb Q_p}A$ とおく。正規化対数体積 `finiteComponentVol p c` は、集合 $S\subseteq A$ 上の次の実数値関数 $V$ である。

$$
V(S)=\frac{\log\!\left(\operatorname{toReal}(\mu(S))/\operatorname{toReal}(\mu(R))\right)}{n}.
$$

`toReal` は Lean における拡張非負実数から実数への変換であり、$\log$ は実数の自然対数である。特に $V(R)=0$ である。単元 $a,b\in A^\times$ に対し、$aR\subseteq bR$ ならば $V(aR)\le V(bR)$ である。$p$ の上にない成分が $c$ にあれば $n=0$ であり、Lean の実数除法の規約により任意の $S$ について $V(S)=0$ である。 [対数体積と単調性](../../../../Solutions/Source_ReferenceIutConcreteLocalHaar.lean#L80) · [零環での体積](../../../../Solutions/Source_ReferenceIutConcreteLocalHaar.lean#L98)

$m_p$ を $A$ における $p$ 倍写像とする。可測集合 $U\subseteq A$ に対し、`finiteHaar_prime_preimage` は拡張非負実数における下の第一式を与える。`finiteComponentVol_prime_preimage` の第二式には、$c$ の全成分が $p$ の上にあることと $0<\mu(U)<\infty$ も必要である。

$$
\mu(m_p^{-1}(U))=p^n\mu(U),\qquad
V(m_p^{-1}(U))=V(U)+\log p.
$$

[Haar 測度の逆像公式](../../../../Solutions/Source_ReferenceIutConcreteLocalHaar.lean#L113) · [対数体積の逆像公式](../../../../Solutions/Source_ReferenceIutConcreteLocalHaar.lean#L124)

集合 $U\subseteq A$ が `finiteAdmissible p c` に属するのは、空でなく可測で、閉包がコンパクトであり、$0<\mu(U)<\infty$ のとき、かつそのときに限る。$R$ と、各単元 $a$ に対する $aR$ はこの条件を満たす。$U$ が許容で全成分が $p$ の上にある場合、`finiteComponentVol_prime_preimage_of_admissible` によれば $m_p$ による逆像で対数体積は同じく $\log p$ だけ増える。 [許容集合](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteHull.lean#L39) · [許容集合の逆像公式](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteHull.lean#L62)

許容集合 $U$ に対し、`exists_leastHull_finite` は次の包含関係を満たす単元 $a\in A^\times$ を与える。任意の素点の組 $c$ について成り立つ。零環の場合、構成では $a=1$ を取り、$R=A$ である。

$$
U\subseteq aR,\qquad
\forall b\in A^\times,\quad U\subseteq bR\ \Longrightarrow\ aR\subseteq bR.
$$

[最小包絡](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteHull.lean#L124)

### 有限素点での不定性

`finiteIndAut p c` を $\mathcal A$ と書く。全成分が $p$ の上にあれば、各完備化ごとに $\mathbb Q_p$-代数自己同型を選ぶ。それぞれのテンソル因子に作用させ、指定された同型を介して得られた写像を $A$ に移す。$\mathcal A$ はこうして得られる写像の集合である。零環の場合は恒等写像のみからなる。 [不定性の写像の有限集合](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteIndeterminacy.lean#L46) · [因子の自己同型](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalCompletionTensorIndeterminacy.lean#L112)

恒等写像は $\mathcal A$ に属する。この集合は有限で、各 $\phi\in\mathcal A$ は $A$ のある $\mathbb Q_p$-代数自己同型の台写像である。任意の有理素数および各 $\phi$ に対して、命題 1.4(iv) の `prop14_iv` は $\phi(R)\subseteq R$ を与える。 [恒等写像と有限性](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteIndeterminacy.lean#L56) · [代数自己同型](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteIndeterminacy.lean#L72) · [命題 1.4(iv)](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteIndeterminacy.lean#L112)

$S\subseteq A$ がコンパクトで $\mu(S)>0$ ならば、和集合 $\bigcup_{\phi\in\mathcal A}\phi(S)$ は許容である。特に、任意の単元 $a\in A^\times$ に対し、`theta_admissible_finite` によって $\bigcup_{\phi\in\mathcal A}\phi(aR)$ は許容となる。 [コンパクト集合と単元倍](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteIndeterminacy.lean#L93)

### 有限素点での対数殻

`finiteLogShell p c` を $\mathcal L$ と書く。全成分が $p$ の上にあれば、実際の完備化のテンソル積におけるテンソル対数殻を取り、そのテンソル積の正規化環上で生成される部分加群をとる。この集合を指定された同型で $A$ に移す。零環の場合は $\mathcal L=R$ である。 [有限素点の対数殻](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteLogShell.lean#L30) · [正規化環上で生成される部分加群](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalCompletionTensorSaturatedLogShell.lean#L91)

任意の素点の組について、$\overline{\mathcal L}$ はコンパクトで $R\subseteq\mathcal L$ が成り立つ。$p$ が奇素数で、$c$ の成分が有限素点 $w$ であるたびにその絶対分岐指数が $1$ ならば、$\mathcal L=R$ である。 [コンパクト性と包含関係](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteLogShell.lean#L49) · [奇素数での不分岐の場合の等式](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteLogShell.lean#L60)

各 $\phi\in\mathcal A$ に対し、`finiteIndAut_logShell` は $\phi(\mathcal L)\subseteq\mathcal L$ を与える。和集合 $\bigcup_{\phi\in\mathcal A}\phi(\mathcal L)$ は許容である。 [対数殻の像と許容性](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteLogShell.lean#L76)

### 命題 1.4(iii)

$c$ の全成分が $p$ の上にあると仮定する。$j\in I$ と有限素点 $w$ を取り、`c j = Place.finite w` とする。$0$ でない $x\in K_w$ を取り、$\lambda=\operatorname{ord}_p(x)\ge0$ を仮定する。付値は $\operatorname{ord}_p(p)=1$ と正規化する。この素点の等式から得られる因子の埋め込みを $\operatorname{incl}_j:K_w\to A$ とする。 [因子の埋め込み](../../../../Solutions/Source_ReferenceIutConcreteLocalPacket.lean#L400) · [正規化付値](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L87)

$d:I\to\mathbb R$ を取る。任意の $i\in I$ と `c i = Place.finite w'` を満たす有限素点 $w'$ について、$d(i)=\operatorname{differentExponent}(K,w')$ を仮定する。この指数は、$K$ の絶対ディファレントにおける $w'$ の素イデアルの重複度を、$w'$ の絶対分岐指数で割ったものである。$c(i)$ の絶対分岐指数を $e_i$ と書く。 [正規化したディファレントの指数](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L105)

`prop14iii_of_isOver` は、次の包含関係と上界を満たす単元 $a\in A^\times$ を与える。

$$
\forall\,\phi\in\mathcal A,\quad \phi\bigl(\operatorname{incl}_j(x)R\bigr)\subseteq aR,\qquad
V(aR)\le
\left(-\lambda+\sum_{i\in I}d(i)+1\right)\log p
 +\sum_{\substack{i\in I\\p-2<e_i}}\bigl(3+\log e_i\bigr).
$$

$p-2<e_i$ の減法は $\mathbb N$ 上で行う。証明では $A$ で $a=p^{\lfloor\lambda\rfloor}$ を取る。床関数の値は自然数であり、このとき $V(aR)=-\lfloor\lambda\rfloor\log p$ である。 [命題 1.4(iii)](../../../../Solutions/Source_ReferenceIutConcreteLocalProp14.lean#L103) · [単元の選択](../../../../Solutions/Source_ReferenceIutConcreteLocalProp14.lean#L116) · [素数べき倍の対数体積](../../../../Solutions/Source_ReferenceIutConcreteLocalProp14.lean#L59)
