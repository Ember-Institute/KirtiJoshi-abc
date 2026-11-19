# The P7 q-pilot and Corollary 3.12

The P7 formula has the sign and the arithmetic weights of Mochizuki III. Joshi III prints a q term with the opposite sign. Its displayed sum also omits the weights needed to compare it with P7. [Mochizuki III, Corollary 3.12](../../../../../refer/Mochizuki/Inter-universal_Teichmuller_Theory.md#L4239) · [Joshi III, displayed corollary](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L3649>)

## The verified P7 formula

Fix the bundle $P$ from `CI.pointThetaData` in the `IsSourceP7Variant` witness. Write $D=P.data$, $F=D.F$, $E=D.E$, $M=\mathbb Q(j(E))$, and $K=D.Kt$. Use `P.localTheory` and `TL := (P.localThetaData htwo).withBadChars P.qPilotInputs`. Let $B$ be `P.qPilotInputs.badModuliFinset`, whose membership is equivalent to membership in `D.VBad`. For $v\in B$, let $s(v)$ be `D.localData.sect.sectFin v`, $d_v=[K_{s(v)}:M_v]$, $n=[M:\mathbb Q]$, and $a_v=\log\|\mathrm{TL.qroot}(s(v))\|$. The signed P7 q-pilot satisfies

$$
Q_{\mathrm{P7}}=\frac1n\sum_{v\in B}\frac{a_v}{d_v}
=-\frac{1}{2\ell n}\sum_{v\in B}\log|j(E)|_v.
$$

The absolute value on $M_v$ uses the residue field cardinality. Bad reduction on the nonempty set $B$ gives $|j(E)|_v>1$, so $Q_{\mathrm{P7}}<0$. For any $w$ of $K$ above $v\in B$, the local theorem gives $\log\|\mathrm{TL.qroot}(w)\|/[K_w:M_v]=-\log|j(E)|_v/(2\ell)$. Thus any representative gives the same relative-degree weighted term. [P7 witness](../../../../Solutions/Source_TripodP7.lean#L27) · [Point specialization](../../../../Solutions/Source_ReferenceIutPointModuliMap.lean#L32) · [Local identity](../../../../Solutions/Source_ReferenceIutCor312RepresentativeQPilot.lean#L51) · [Bad moduli places](../../../../Solutions/Source_ReferenceIutCor312QPilotModuli.lean#L49) · [Moduli formula](../../../../Solutions/Source_ReferenceIutCor312QPilotModuli.lean#L115)

The point specialization passed MCP-CI job `ci-023245-51a64279`. The joint review, `ci-023258-e891f8b6`, reports only `propext`, `Classical.choice`, and `Quot.sound` for the 11 reviewed declarations. [Leaf receipt](../receipts/round-ci-023245-51a64279-result.json) · [Review receipt](../receipts/round-ci-023258-e891f8b6-result.json)

## Joshi III

Set $\ell^*=(\ell-1)/2$. Let $J_p$ be Joshi's selected odd split multiplicative places over $p$, and let $r_w=q_w^{1/(2\ell)}$. Write $V$ for the volume of the theta region in Form 2. With the absolute values used in that display, taking logs of $V\ge\prod_p\prod_{w\in J_p}|r_w|^{\ell^*}$ gives

$$
\frac{\log V}{\ell^*}\ge\sum_p\sum_{w\in J_p}\log|r_w|.
$$

Joshi then defines the signed theta term using $\sum_p- |\log V_p|$ and states that each $\log V_p\le 0$. Under that convention, the left side can be written as $-|\log V|/\ell^*$. The printed corollary puts $-\sum_p\sum_{w\in J_p}\log|r_w|$ on the right. On nonempty support, $0<|r_w|<1$ makes this right side strictly positive, while the printed left side is nonpositive. The same contradiction holds with positive weights on the right. [Form 2 and proof](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L3617>) · [Signed theta convention](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L3634>) · [Printed inequality](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L3649>) · [Lean sign audit](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/Corollary312SourceSignAudit.lean#L66)

The weighted-volume section uses $1/[L'_w:(L_{\mathrm{mod}})_v]$ for $w$ above $v$. The corollary displays a plain sum. With the identifications below, adding the local and global degree factors to the signed sum gives the P7 expression

$$
\frac1{[M:\mathbb Q]}\sum_p\sum_{w\in J_p}
\frac{\log|r_w|_{\mathrm{Haar}}}{[L'_w:(L_{\mathrm{mod}})_v]}.
$$

This equality concerns the normalized q term. A lower bound for it with the corresponding normalized theta volume requires a volume comparison. [Joshi's weights](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L3552>) · [Haar normalization](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L3495>)

## Mochizuki III and IV

Mochizuki III, Corollary 3.12, writes $-|\log(\Theta)|\ge-|\log(q)|$ with $|\log(q)|>0$. For a single representative $\underline v$ above $v\mid p$, Remark 3.1.1(ii) uses the weight

$$
\frac{1}{[K_{\underline v}:(F_{\mathrm{mod}})_v] \sum_{u\mid p}[(F_{\mathrm{mod}})_u:\mathbb Q_p]}.
$$

The denominator sum runs over the entire moduli fiber above $p$. After identifying $F_{\mathrm{mod}}$ with $M$, the degree formula makes the sum $[M:\mathbb Q]$. With the matched representative and completion, the weight is $1/(d_v n)$. [Mochizuki III, Corollary 3.12](../../../../../refer/Mochizuki/Inter-universal_Teichmuller_Theory.md#L4239) · [Remark 3.1.1(ii)](../../../../../refer/Mochizuki/Inter-universal_Teichmuller_Theory.md#L2090)

In the setting of IUT IV, Theorem 1.10, $|\log(q)|=\log(\mathfrak q)/(2\ell)$. The divisor $\mathfrak q$ uses the complete fibers over $\mathbb V_{\mathrm{mod}}^{\mathrm{bad}}$. If the curve, bad support, and local normalizations agree, its normalized degree is $\sum_{v\in B}\log|j(E)|_v/n$. Indeed, at a place $b$ of $F$ over $v\in B$ the degree contribution before global normalization is $-\log|q_b|_b=\log|j(E)|_b$. The logs scale by $[F_b:M_v]$. Summing these degrees over $b\mid v$ gives $[F:M]$, which cancels the relative factor in $[F:\mathbb Q]$. Thus the signed q-pilot of Mochizuki III equals $Q_{\mathrm{P7}}$ under these identifications. [IUT IV, q-divisor support](../../../../../refer/Mochizuki/Inter-universal_Teichmuller_Theory_4.md#L578) · [IUT IV, normalized degree](../../../../../refer/Mochizuki/Inter-universal_Teichmuller_Theory_4.md#L598) · [IUT IV, q-pilot magnitude](../../../../../refer/Mochizuki/Inter-universal_Teichmuller_Theory_4.md#L613) · [Lean fiber sum](../../../../Solutions/Source_ReferenceIutCor312QPilotModuli.lean#L63)

## Identifications for a comparison of the same P7 bundle

1. Identify Joshi's $C$ with $E$ as an elliptic curve over $L\simeq F$, and identify $X=C\setminus\{O\}$ with the punctured curve of $D$. Identify $L_{\mathrm{mod}}\simeq M$ by the $j$-invariant and $L'\simeq K$ by the $\ell$-torsion representation. Use the same identifications for Mochizuki's $F_{\mathrm{mod}}\subset F\subset K$. Require the field maps to commute with both inclusions. The verified Lean map equality is internal to the P7 tower. [Joshi's initial data](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L996>) · [IUT I, Definition 3.1(b) and (c), pp. 61–62](<../../../../../refer/Mochizuki/Inter-universal Teichmuller Theory I.pdf>) · [P7 algebra maps](../../../../Solutions/Source_ReferenceIutPointModuliMap.lean#L16)

2. Match the paper's place above $v$ with $s(v)$ under the tower, and preserve restriction to $M$ and residue characteristic. For a termwise comparison on the chosen representatives, require $J_p$ to map bijectively to $\{s(v):v\in B,\ p(v)=p\}$ at every $p$. The weighted local identity also permits a different single place above each matched $v$ on the q side. IUT I allows a chosen nonempty set of odd multiplicative places with residue characteristic prime to $\ell$. In a realization with the same curve, choose its bad set to be $B$ and its section to be the P7 section. [Joshi's section and rational-prime fibers](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L1023>) · [IUT I, Definition 3.1(b), (c), and (e), pp. 61–62](<../../../../../refer/Mochizuki/Inter-universal Teichmuller Theory I.pdf>) · [P7 local identity](../../../../Solutions/Source_ReferenceIutCor312RepresentativeQPilot.lean#L51)

3. Check the bad support for Joshi's displayed sum. P7 requires multiplicative reduction at all $b\mid v$ in $F$ and excludes $p(v)=2,\ell$. Joshi's definition selects odd split multiplicative places. At the identified $F_b$, rational odd torsion rules out nonsplit multiplicative reduction. In the nonsplit case a Galois element with nontrivial quadratic character acts by $-1$ on the cyclic quotient of the odd-order Tate torsion. This contradicts rationality of the full odd torsion. With the reduction conditions identified, $B$ equals the restriction of Joshi's support to $p\ne\ell$. Equality with the full support then requires that it contain no place over $\ell$. P7's (P3) bounds the local order at bad places over $\ell$ and allows such places. [Joshi's support](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L1006>) · [Joshi's rational 6-torsion](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L1023>) · [P7 support](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean#L55) · [P7 conditions](../../../../Solutions/Source_TripodP7.lean#L33)

4. Identify the towers of completions over $v$, including the maps from $M_v$ and $F_b$ into $K_{s(v)}$, where $b=s(v)|_F$. Transport the paper's Tate parameter to the one supplied by `D.prime.tate` at $b$. Then the transported root and `TL.qroot` have the same nonzero $(2\ell)$-th power. Their quotient is a root of unity of norm one. For equality of the logs alone, equality of the Tate parameter orders suffices. Both orders follow from $|q_b|_b=|j(E)|_b^{-1}$ for the matched Tate uniformizations. [Joshi's Tate roots](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L1062>) · [P7 root and completion maps](../../../../Solutions/Source_ReferenceIutConcreteThetaRegion.lean#L60) · [Tate order and $j$](../../../../Solutions/Source_ReferenceIutCor312QPilotModuli.lean#L25)

5. Compare the absolute values on those completions. For a uniformizer $\pi$ of a field with residue field of cardinality $p^f$, Lean uses $\|\pi\|=p^{-f}$. The normalized Haar measure gives $\operatorname{Vol}(\pi\mathcal O)=[\mathcal O:\pi\mathcal O]^{-1}=p^{-f}$, so the Haar modulus gives precisely the Lean norm. Joshi earlier specifies $|\pi|_{\mathbb C_p}=p^{-1}$ at a chosen local field. A log computed with that norm must be multiplied by $f$ to obtain the Haar log on that field. The two conventions give equal raw logs when $f=1$. [Lean norm](../../../../Solutions/Source_TripodFinitePlaceArithmetic.lean#L104) · [Joshi's $\mathbb C_p$ convention](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L1748>) · [Joshi's Haar modulus](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L3495>)

## The theta volume of the fixed P7 bundle

Let $X_{\mathrm{P7}}$ be `concreteVariantData D P.localTheory TL P.qPilotInputs`. To identify both sides of the P7 inequality with Mochizuki's Corollary 3.12, the theta terms must satisfy

$$
X_{\mathrm{P7}}.\texttt{rhsData.rhs}=-|\log(\Theta)|_{\mathrm{IUT\ III}}.
$$

Here `rhsData.rhs` is the procession-normalized log-volume of the hull of the P7 theta-pilot region. Its definition takes the average of sums over all rational places. Match the union of theta-pilot images under (Ind1)–(Ind3), the corresponding hulls, and their volumes. Account for the tensor tuple multiplicities, the passage from the full P7 fibers to the selected source places, and all finite and archimedean contributions. Remark 3.1.1(ii) uses a sum over tuples with possible repeated places for the tensor normalization. [Lean hull and volume](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_RightHandSide.lean#L129) · [Lean procession average](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Cor312_LogVolume.lean#L177) · [Mochizuki III, tensor weights](../../../../../refer/Mochizuki/Inter-universal_Teichmuller_Theory.md#L2096) · [Mochizuki III, theta region](../../../../../refer/Mochizuki/Inter-universal_Teichmuller_Theory.md#L4245)

`ThetaLocalData.not_forall_corollary312Variant` varies the archimedean shell in `LocalTheory` and keeps the q-pilot fixed. The source-specific consumer instead requires `Corollary312Variant` only on `IsSourceP7Variant` bundles. Evidence for that consumer needs the volume of the fixed P7 data. [Universal counterexample](../../../../Solutions/Source_ReferenceIutCor312UniversalAudit.lean#L369) · [Source-specific consumer](../../../../Solutions/Source_TripodCanonicalCorollary22.lean#L72)
