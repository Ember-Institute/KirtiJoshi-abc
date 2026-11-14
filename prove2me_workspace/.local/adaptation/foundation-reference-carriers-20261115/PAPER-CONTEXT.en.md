# Original-paper context for the five foundation definition bundles

Author/source text only. Independent blind readbacks remain separate. Mathematical symbols below are manual transcriptions checked against rendered original PDF pages. Raw extraction evidence remains unchanged in paper-context-evidence/.

## Iut.Cor312.ThetaData.Places

**Paper source context.** Mochizuki I, §0, “Numbers” (p. 35), fixes $\mathbb V(F)$ as the union of archimedean and nonarchimedean valuations of a number field. The same paragraph explicitly relates “valuation” to “place” and “absolute value.” Definition 3.1(b) later uses $\mathbb V_{\mathrm{mod}}=\mathbb V(F_{\mathrm{mod}})$, and Definition 3.1(e) selects places above this set (pp. 61–63). This is the paper setting served by the local place carrier.

**Implementation scope.** The reference implementation uses Mathlib’s finite and infinite places as a tagged disjoint union. It also supplies the embeddings of both summands, an ideal-theoretic relation between finite places, and the residue characteristic of a finite place. Those are local implementation choices supporting the paper notation. This bundle alone does not construct the full initial $\Theta$-data or establish every normalization comparison between Mathlib and the paper.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), §0, Numbers, paragraph defining V(F); printed/PDF page(s) 35.

> Let $F$ be a number field [i.e., a finite extension of the field of rational numbers]. Then we shall write
>
> $$\mathbb V(F)=\mathbb V(F)^{\mathrm{arc}}\bigcup\mathbb V(F)^{\mathrm{non}}$$
>
> for the set of valuations of $F$, that is to say, the union of the sets of archimedean [i.e., $\mathbb V(F)^{\mathrm{arc}}$] and nonarchimedean [i.e., $\mathbb V(F)^{\mathrm{non}}$] valuations of $F$. Here, we note that this terminology “valuation”, as it is applied in the present series of papers, corresponds to such terminology as “place” or “absolute value” in the work of other authors.

Transcription: visually checked; line breaks and typography are normalized as recorded in the source evidence.

**Actual consumer.** Place indices enter RHSData and the later local estimates. Finite residue characteristics and the lies-over relation also feed the q-order expressions. These dependencies reach Theorem110Invariants.theorem110, whose arithmetic certificate, local estimates, prime-counting bound, and Corollary 3.12 variant remain supplied premises.

## Iut.Cor312.ThetaData.PointMap

**Paper source context.** Mochizuki I, Definition 3.1(a)–(c) (pp. 61–62), starts from a number field $F$, its algebraic closure $\overline F$, an elliptic curve $E_F$ obtained by filling the puncture of $X_F$, and a torsion-defined finite Galois extension $K/F$. This concrete curve-and-extension setting supplies the service context for transporting points after extending the coefficient field. The excerpts identify this setting; they do not state the local helper’s universal type.

**Implementation scope.** Iut.Anabelian.pointMap is a local wrapper around Mathlib’s base-change map on nonsingular Weierstrass points. For arbitrary fields $k,K$, a Weierstrass curve $E/k$, and a ring homomorphism $f:k\to K$, it gives the additive map on nonsingular-point groups, carrying infinity to infinity and $(x,y)$ to $(f(x),f(y))$. Its universal field-level statement is not attributed verbatim to Mochizuki. Applying it to the paper’s field inclusions is ordinary supporting infrastructure, not an identification with a paper theorem or an anabelian reconstruction claim.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), Definition 3.1(a), complete item; printed/PDF page(s) 61.

> $F$ is a number field such that $\sqrt{-1}\in F$; $\overline F$ is an algebraic closure of $F$. Write $G_F\overset{\mathrm{def}}{=}\operatorname{Gal}(\overline F/F)$.

Transcription: visually checked; line breaks and typography are normalized as recorded in the source evidence.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), Definition 3.1(b), opening sentences through the clause defining E_F; printed/PDF page(s) 61.

> $X_F$ is a once-punctured elliptic curve [i.e., a hyperbolic curve of type $(1,1)$] over $F$ that admits stable reduction over all $v\in\mathbb V(F)^{\mathrm{non}}$. Write $E_F$ for the elliptic curve over $F$ determined by $X_F$ [so $X_F\subseteq E_F$];

Transcription: visually checked; line breaks and typography are normalized as recorded in the source evidence.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), Definition 3.1(c), first sentence through the definition of K; printed/PDF page(s) 62.

> $l$ is a prime number $\geq5$ such that the image of the outer homomorphism
>
> $$G_F\to GL_2(\mathbb F_l)$$
>
> determined by the $l$-torsion points of $E_F$ contains the subgroup $SL_2(\mathbb F_l)\subseteq GL_2(\mathbb F_l)$; write $K\subseteq\overline F$ for the finite Galois extension of $F$ determined by the kernel of this homomorphism.

Transcription: visually checked; line breaks and typography are normalized as recorded in the source evidence.

**Actual consumer.** The dependency graph uses pointMap in TateFamily, then InitialThetaData, then Corollary312VariantData.data and theorem110. This helper transports existing points; it does not supply the Tate uniformization, initial-data existence, or final numerical estimate.

## Iut.Cor312.RationalPlace

**Paper source context.** Mochizuki III, Introduction (p. 11), calls $\mathbb V_{\mathbb Q}$ the set of valuations of $\mathbb Q$. The following passage constructs one local tensor product for each $v_{\mathbb Q}$ by first summing over chosen places above $v_{\mathbb Q}$ and then tensoring over the labels. The opening of §3 repeats $\mathbb V_{\mathbb Q}\overset{\mathrm{def}}{=}\mathbb V(\mathbb Q)$ (p. 92). Mochizuki I, §0, p. 35, supplies the general place terminology.

**Implementation scope.** The local RationalPlace type represents this index by one constructor for each rational prime and a separate infinity constructor. Its IsFinite predicate tests the constructor. Its residueChar function returns the prime on a finite label and returns $0$ at infinity by an explicit implementation convention. The definition does not itself construct absolute values or prove equivalence with Mathlib’s places of $\mathbb Q$. The direct paper location for this index is III, pp. 11 and 92; I, Definition 3.1(e), provides broader initial-data background.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory III: Canonical Splittings of the Log-theta-lattice* (May 2020), Introduction, sentence defining the rational valuation index; printed/PDF page(s) 11.

> Write $\mathbb V_{\mathbb Q}$ for the set of valuations of $\mathbb Q$.

Transcription: visually checked; line breaks and typography are normalized as recorded in the source evidence.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory III: Canonical Splittings of the Log-theta-lattice* (May 2020), Introduction, construction paragraph and both bullets, ending with the name tensor packet; printed/PDF page(s) 11.

> Then, in order to obtain objects that are immune to the various label indeterminacies discussed above, we consider, for each element $*\in\mathbb S_{j+1}^{\pm}$, and for each [say, for simplicity, nonarchimedean] $v_{\mathbb Q}\in\mathbb V_{\mathbb Q}$,
>
> - the direct sum of the log-shells associated to the prime-strip labeled by the given element $*\in\mathbb S_{j+1}^{\pm}$ at the $\underline v\in\underline{\mathbb V}$ that lie over $v_{\mathbb Q}$;
>
> we then form
>
> - the tensor product, over the elements $*\in\mathbb S_{j+1}^{\pm}$, of these direct sums.
>
> This collection of tensor products associated to $v_{\mathbb Q}\in\mathbb V_{\mathbb Q}$ will be referred to as the tensor packet associated to the collection of prime-strips indexed by elements of $\mathbb S_{j+1}^{\pm}$.

Transcription: visually checked; line breaks and typography are normalized as recorded in the source evidence.

**Actual consumer.** RationalPlace indexes the local packet data and LogVolumeData.globalVol. The graph proceeds through LocalEstimate.rhs_le to theorem110. This indexing retains the separate rational-place contributions used when IV, Theorem 1.10, proof Step (viii), sums local upper bounds (p. 30); the carrier does not prove those bounds.

## Iut.Cor312.Procession

**Paper source context.** Mochizuki I, §0 (pp. 33–34), defines a capsule as a finite indexed family of objects of a category, and defines its morphisms using injections of index sets together with component morphisms. III, Introduction (p. 10), replaces a single label container by a diagram of inclusions of finite sets, referring to I, Propositions 4.11 and 6.9. The displayed sets are $\mathbb S^{\pm}_{j+1}=\{0,1,\ldots,j\}$, including $j=0$. The local combinatorial carrier retains only the finite label sets and their monotone inclusions.

**Implementation scope.** Capsule stores a finite subset of a fixed label type, with its cardinality and its label subtype. Procession stores a finite, non-strictly increasing chain of such finite subsets. This is a specialization to label bookkeeping, not the full paper capsule of objects and morphisms; it stores neither the attached objects nor their component morphisms. In standard(n), local index $i$ corresponds to paper label bound $j=i+1$, so the local chain starts with $\mathbb S^{\pm}_2$ and omits the paper’s initial singleton $\mathbb S^{\pm}_1$. The generic definitions allow empty label sets and length $0$.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), §0, Monoids and Categories, paragraph defining capsules (crosses the page break); printed/PDF page(s) 33, 34.

> Let $\mathcal C$ be a category. We define a capsule of objects of $\mathcal C$ to be a finite collection $\{A_j\}_{j\in J}$ [i.e., where $J$ is a finite index set] of objects $A_j$ of $\mathcal C$; if $|J|$ denotes the cardinality of $J$, then we shall refer to a capsule with index set $J$ as a $|J|$-capsule; also, we shall write $\pi_0(\{A_j\}_{j\in J})\overset{\mathrm{def}}{=}J$.

Transcription: visually checked; line breaks and typography are normalized as recorded in the source evidence.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), §0, immediately after the capsule definition, first morphism sentence and its consequence; printed/PDF page(s) 34.

> A morphism of capsules of objects of $\mathcal C$
>
> $$\{A_j\}_{j\in J}\to\{A'_{j'}\}_{j'\in J'}$$
>
> is defined to consist of an injection $\iota:J\hookrightarrow J'$, together with, for each $j\in J$, a morphism $A_j\to A'_{\iota(j)}$ of objects of $\mathcal C$. Thus, the capsules of objects of $\mathcal C$ form a category $\operatorname{Capsule}(\mathcal C)$.

Transcription: visually checked; line breaks and typography are normalized as recorded in the source evidence.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory III: Canonical Splittings of the Log-theta-lattice* (May 2020), Introduction, sentence introducing the alternative approach via processions; printed/PDF page(s) 10.

> Thus, we consider the following alternative approach, via processions [cf. [IUTchI], Propositions, 4.11, 6.9].

Transcription: visually checked; line breaks and typography are normalized as recorded in the source evidence.

**Actual consumer.** Theorem110’s proof rewrites the supplied container chain to Procession.standard(X.lstar). It then uses capsule cardinalities in the normalized sum. The combinatorics organize the supplied local estimates and do not prove the paper’s symmetry, prime-strip, or Corollary 3.12 assertions.

## Iut.Cor312.PacketPresentation

**Paper source context.** Mochizuki III, Proposition 3.1 (pp. 92–93), describes local tensor packets, their ring decompositions, and integral structures. Remark 3.9.5 (pp. 126–127) then defines holomorphic hulls in that arithmetic setting. Item (i) retains a finite-log-volume, relatively compact subset prerequisite. For a relatively compact input it chooses the smallest containing region obtained by scaling the integral structure by an element nonzero in every field component. For an input that is not relatively compact, the paper instead assigns the full ambient space. Both branches belong to the quoted paper definition.

**Implementation scope.** DirectSumPresentation is only an interface: an arbitrary index type $C$, component commutative rings $A_c$, a topology on each component, and designated subsets $O_c$. It does not require $C$ to be finite, the rings to be fields, the ring operations to be continuous, or the subsets to be actual integer rings. Its total space is the dependent product. Product regions impose separate component conditions. IsHullRegion means $R=aO$ for a componentwise invertible multiplier. In a field, invertible agrees with nonzero. In a nontrivial commutative ring a unit is nonzero, while a nonzero element need not be a unit; the carrier also allows trivial rings, where zero is a unit. This bundle neither constructs the paper’s tensor decomposition nor provides the qualification, leastness, or full-space branch of the paper’s hull operation.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory III: Canonical Splittings of the Log-theta-lattice* (May 2020), Remark 3.9.5, complete opening paragraph; printed/PDF page(s) 126.

> In situations that involve consideration of various sorts of regions [cf. the discussion of Remarks 3.1.1, (iii), (iv); 3.9.4] to which the log-volume may be applied, it is often of use to consider the notion of the holomorphic hull of a region.

Transcription: visually checked; line breaks and typography are normalized as recorded in the source evidence.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory III: Canonical Splittings of the Log-theta-lattice* (May 2020), Remark 3.9.5(i), complete item; printed/PDF page(s) 127.

> Suppose that we are in the situation of Proposition 3.9, (i). Let
>
> $$ {}^{\alpha}U\subseteq\mathcal I^{\mathbb Q}({}^{\alpha}\mathcal F_{v_{\mathbb Q}})\quad\text{(respectively, }{}^{A}U\subseteq\mathcal I^{\mathbb Q}({}^{A}\mathcal F_{v_{\mathbb Q}});\quad{}^{A,\alpha}U\subseteq\mathcal I^{\mathbb Q}({}^{A,\alpha}\mathcal F_{\underline v})\text{)} $$
>
> be a subset that contains a relatively compact subset whose log-volume [cf. the discussion of Remark 3.1.1, (iii), (iv), as well as Remark 3.9.7, (ii), below] is finite [i.e., $>-\infty$]. If ${}^{\alpha}U$ (respectively, ${}^{A}U$; ${}^{A,\alpha}U$) is relatively compact, then we define the holomorphic hull of ${}^{\alpha}U$ (respectively, ${}^{A}U$; ${}^{A,\alpha}U$) to be the smallest subset of the form
>
> $$ {}^{\alpha}H\overset{\mathrm{def}}{=}\lambda\cdot\mathcal O_{{}^{\alpha}\mathcal F_{v_{\mathbb Q}}}\quad\text{(respectively, }{}^{A}H\overset{\mathrm{def}}{=}\lambda\cdot\mathcal O_{{}^{A}\mathcal F_{v_{\mathbb Q}}};\quad{}^{A,\alpha}H\overset{\mathrm{def}}{=}\lambda\cdot\mathcal O_{{}^{A,\alpha}\mathcal F_{\underline v}}\text{)} $$
>
> — where, relative to the direct sum decomposition of $\mathcal I^{\mathbb Q}((-))$ as a direct sum of fields [cf. the discussion of Proposition 3.9, (i)], $\lambda\in\mathcal I^{\mathbb Q}((-))$ is an element such that each component of $\lambda$ [i.e., relative to this direct sum decomposition] is nonzero — that contains ${}^{\alpha}U$ (respectively, ${}^{A}U$; ${}^{A,\alpha}U$). If ${}^{\alpha}U$ (respectively, ${}^{A}U$; ${}^{A,\alpha}U$) is not relatively compact, then we define the holomorphic hull of ${}^{\alpha}U$ (respectively, ${}^{A}U$; ${}^{A,\alpha}U$) to be $\mathcal I^{\mathbb Q}({}^{\alpha}\mathcal F_{v_{\mathbb Q}})$ (respectively, $\mathcal I^{\mathbb Q}({}^{A}\mathcal F_{v_{\mathbb Q}})$; $\mathcal I^{\mathbb Q}({}^{A,\alpha}\mathcal F_{\underline v})$). One verifies immediately that the holomorphic hull is well-defined [under the conditions stated].

Transcription: visually checked; line breaks and typography are normalized as recorded in the source evidence.

**Actual consumer.** The presentation and region predicates feed the large volume container, LogVolumeData, and LocalEstimate. The resulting dependency paths reach theorem110. The paper’s use of a hull volume is explicit in IV, Theorem 1.10, proof Step (iv) (p. 26); the formal numerical theorem receives the corresponding local estimates as premises.

## Paper versions

I: Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020).
https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf
Local: `/home/admin-wsl/Coq/abc/refer/Mochizuki/Inter-universal Teichmuller Theory I.pdf`. SHA-256: `7360e3ed27c235b5497a0743d3ed1646fbb97688547d16b7c784fc7f127f1f03`.

III: Shinichi Mochizuki, *Inter-universal Teichmüller Theory III: Canonical Splittings of the Log-theta-lattice* (May 2020).
https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf
Local: `/tmp/p2m-foundation-readback-v2-20261115/Inter-universal Teichmuller Theory III.pdf`. SHA-256: `9a7ee3c77b1c7717210c0613eb39b6844649d0040dc3d9e1be7d544f8f91a0b9`.

IV: Shinichi Mochizuki, *Inter-universal Teichmüller Theory IV: Log-volume Computations and Set-theoretic Foundations* (April 2020).
https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20IV.pdf
Local: `/home/admin-wsl/Coq/abc/refer/Mochizuki/Inter-universal Teichmuller Theory IV.pdf`. SHA-256: `5bf4b1e0a8c2686562a6859e5009d301335044cfb5efec5d3a9edf764e4af87f`.
