Original Mochizuki paper context for the four Tate/theta carrier bundles.

This is author/source context, separate from an independent code-only readback. The selection has 20 commands. The supplied mathematical structures do not establish their own existence or their identity with the paper objects.

The exact source notices declare Apache 2.0. Tate has no standalone upstream LICENSE in the recorded provenance. The source files cite standard Tate references for the explicit formulas; this packet quotes only original Mochizuki papers.

## TateCurvesTheta.TateCurve.JInvariant

**Paper source context.** Mochizuki I, Definition 3.1(c), uses curve-associated q-parameters at bad places. GenEll §3 describes a Tate parameter naturally associated to a semistable local elliptic curve. These passages explain why a local parameter must be linked to the chosen curve. They do not give the explicit c₄³/Δ formula in this selection.

**Implementation scope.** The selected command defines tateJ as t.tateCurve.c₄ ^ 3 / t.tateCurve.Δ. It is a field expression with totalized division. This command does not prove that the discriminant is nonzero. The source file contains further theorems, but tateJ_eq_j, ellipticity, norm estimates, and parameter existence or uniqueness are outside this selection. The formula belongs to the imported Tate implementation. Its source header cites the standard Tate theory of Silverman and Tate. No formula in this packet is attributed to the Mochizuki quotations. Equality with the j-invariant of a paper curve requires an additional bridge.

Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position* (February 2009), §3, paragraph introducing local theory at nonarchimedean primes, immediately before the torsion discussion; printed/PDF page(s) 14, 15. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf.

> Next, we consider the local theory at nonarchimedean primes. Let $K$ be a finite extension of $\mathbb Q_p$ [where $p$ is a prime number] with residue field $k$, maximal ideal $\mathfrak m_K\subseteq\mathcal O_K$, and valuation map $v_K:K^{\times}\to\mathbb Z$ [which we normalize so that $v_K$ is surjective]; $\overline K$ an algebraic closure of $K$; $G_K\overset{\mathrm{def}}{=}\operatorname{Gal}(\overline K/K)$; $E\to\operatorname{Spec}(\mathcal O_K)$ a one-dimensional semi-abelian scheme over $\mathcal O_K$ such that the generic fiber $E_K$ of $E$ is proper, while the special fiber $E_k$ of $E$ is isomorphic to $(\mathbb G_m)_k$, the multiplicative group over $k$.

Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position* (February 2009), §3, paragraph immediately before Lemma 3.2, first two Tate-parameter sentences; printed/PDF page(s) 15. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf.

> Moreover, the extension class associated to this exact sequence is precisely that obtained by extracting an $l$-th root of the Tate parameter $q_E\in\mathfrak m_K$. The Tate parameter is an element of $\mathfrak m_K$ that is naturally associated to $E$ and has the property that the subscheme $\mathcal O_K/(q_E)$ is equal to the pull-back via the classifying morphism $\operatorname{Spec}(\mathcal O_K)\to\overline{\mathcal M}_{\mathrm{ell}}$ — where we write $\overline{\mathcal M}_{\mathrm{ell}}$ for the moduli stack of one-dimensional semi-abelian varieties over $\mathbb Z$ — of the divisor at infinity $\infty_{\mathcal M}\subseteq\overline{\mathcal M}_{\mathrm{ell}}$.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), Definition 3.1(c), second complete sentence; printed/PDF page(s) 62. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf.

> Also, we suppose that $l$ is prime to the [residue characteristics of the] elements of $\mathbb V_{\mathrm{mod}}^{\mathrm{bad}}$, as well as to the orders of the $q$-parameters of $E_F$ [i.e., in the terminology of [GenEll], Definition 3.3, the “local heights” of $E_F$] at the primes of $\mathbb V(F)^{\mathrm{bad}}$.

**Actual consumer.** AdmissiblePrimeData.tateJ_eq uses tateJ in a supplied equality with the embedded j-invariant of E. The original dependency graph then reaches theorem110. The equality is a structure field; this definition does not produce it.

## TateCurvesTheta.TateCurve.Parametrization

**Paper source context.** GenEll §3 describes a local curve with multiplicative special fiber and its Tate parameter. Étale Theta §1 uses the graph covering of a split special fiber. These passages explain the arithmetic setting for multiplicative uniformization. They do not display the selected X and Y series or prove their analytic properties.

**Implementation scope.** The four selected commands are Xterm, Yterm, X, and Y. For u : Kˣ and n : ℤ, Xterm is qⁿu/(1−qⁿu)² and Yterm is (qⁿu)²/(1−qⁿu)³. X is the integer-indexed tsum of Xterm minus 2·eisenstein 1. Y is the tsum of Yterm plus eisenstein 1. The declarations assume a NormedField and a TateParameter; they impose no exclusion of u in q^ℤ. Division is totalized, including at a zero denominator. A Lean tsum expression alone does not prove summability. These four definitions establish no convergence theorem, Weierstrass equation, group homomorphism, or quotient uniformization. Such statements elsewhere in the source are outside the selection. The formula normalization comes from the imported Tate implementation and its stated standard Tate references. It is not a transcription of a formula in the cited Mochizuki passages.

Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position* (February 2009), §3, paragraph introducing local theory at nonarchimedean primes, immediately before the torsion discussion; printed/PDF page(s) 14, 15. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf.

> Next, we consider the local theory at nonarchimedean primes. Let $K$ be a finite extension of $\mathbb Q_p$ [where $p$ is a prime number] with residue field $k$, maximal ideal $\mathfrak m_K\subseteq\mathcal O_K$, and valuation map $v_K:K^{\times}\to\mathbb Z$ [which we normalize so that $v_K$ is surjective]; $\overline K$ an algebraic closure of $K$; $G_K\overset{\mathrm{def}}{=}\operatorname{Gal}(\overline K/K)$; $E\to\operatorname{Spec}(\mathcal O_K)$ a one-dimensional semi-abelian scheme over $\mathcal O_K$ such that the generic fiber $E_K$ of $E$ is proper, while the special fiber $E_k$ of $E$ is isomorphic to $(\mathbb G_m)_k$, the multiplicative group over $k$.

Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position* (February 2009), §3, paragraph immediately before Lemma 3.2, first two Tate-parameter sentences; printed/PDF page(s) 15. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf.

> Moreover, the extension class associated to this exact sequence is precisely that obtained by extracting an $l$-th root of the Tate parameter $q_E\in\mathfrak m_K$. The Tate parameter is an element of $\mathfrak m_K$ that is naturally associated to $E$ and has the property that the subscheme $\mathcal O_K/(q_E)$ is equal to the pull-back via the classifying morphism $\operatorname{Spec}(\mathcal O_K)\to\overline{\mathcal M}_{\mathrm{ell}}$ — where we write $\overline{\mathcal M}_{\mathrm{ell}}$ for the moduli stack of one-dimensional semi-abelian varieties over $\mathbb Z$ — of the divisor at infinity $\infty_{\mathcal M}\subseteq\overline{\mathcal M}_{\mathrm{ell}}$.

Shinichi Mochizuki, *The Étale Theta Function and its Frobenioid-theoretic Manifestations* (December 2008), §1, printed page 11, first paragraph through “a natural surjection”; printed/PDF page(s) 11. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/The%20Etale%20Theta%20Function%20and%20its%20Frobenioid-theoretic%20Manifestations.pdf.

> Since the special fiber of $\mathfrak X$ is split, it follows that the universal graph-covering of the dual graph of this special fiber determines [up to composition with an element of $\operatorname{Aut}(\mathbb Z)=\{\pm1\}$] a natural surjection […]

**Actual consumer.** Xterm feeds X and Yterm feeds Y. The coordinate pins iso_x and iso_y in the supplied TateStructure use X and Y. TateStructure then feeds TateFamily, InitialThetaData, Corollary312VariantData.data, and theorem110 in the original graph.

## Iut.Cor312.ThetaData.AdmissiblePrime

**Paper source context.** Mochizuki I, Definition 3.1(a)–(c), fixes an algebraic closure, a prime l≥5, the l-torsion representation with SL₂ in its image, and its kernel field. It also imposes coprimality with residue characteristics and q-parameter orders. GenEll Definition 3.3 calls the valuation of q_E the local height. These original passages motivate the supplied data and the normalized-order interface.

**Implementation scope.** The six selected commands are galPointMap, galPointMap_torsionBy, localCompletion, AdmissiblePrimeData, torsionField, and qOrder. galPointMap is the functorial additive map on affine nonsingular points induced by an F-algebra automorphism of Fbar. galPointMap_torsionBy proves preservation of n-torsion. localCompletion abbreviates the finite-place adic completion. AdmissiblePrimeData has all 15 actual fields: ℓ, ℓ_prime, five_le, torsionBasis, rep, rep_spec, sl_le_range, ker_isOpen, galois_deg_prime, residueChar_coprime, tate, tateJ_eq, unif, unif_isUniformizer, and q_order_coprime. The torsionBasis is a supplied additive equivalence with Fin 2 → ZMod ℓ. rep_spec pins the supplied representation to the functorial action in this basis. The local tateJ_eq, uniformizers, and coprimality proofs are supplied fields. The structure assumes Field Fbar and Algebra F Fbar, but it does not itself require Fbar to be algebraically closed or algebraic over F. This differs from the paper’s algebraic-closure setting. torsionField is only the fixed-field definition IntermediateField.fixedField D.rep.ker. This selected definition does not prove finiteness, Galoisness, or an identification with the paper’s K. ker_isOpen records a topological condition; this packet does not infer those extension theorems from it. qOrder reads orderNat from the supplied parameter and uniformizer through toOrdered. Equality with the paper’s local height requires a norm/valuation bridge and curve identity. The selected commands do not construct an admissible prime, a torsion basis, or an inhabitant of this structure. The quotation of Definition 3.1(b) includes rational 2·3-torsion, but this is not an AdmissiblePrimeData field.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), Definition 3.1(a), first two sentences; printed/PDF page(s) 61. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf.

> $F$ is a number field such that $\sqrt{-1}\in F$; $\overline F$ is an algebraic closure of $F$. Write $G_F\overset{\mathrm{def}}{=}\operatorname{Gal}(\overline F/F)$.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), Definition 3.1(b), final sentence across the page break; printed/PDF page(s) 61, 62. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf.

> Here, we suppose further that the field extension $F/F_{\mathrm{mod}}$ is Galois of degree prime to $l$, and that the $2\cdot3$-torsion points of $E_F$ are rational over $F$.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), Definition 3.1(c), first sentence, including its displayed homomorphism; printed/PDF page(s) 62. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf.

> $l$ is a prime number $\geq 5$ such that the image of the outer homomorphism $G_F\to GL_2(\mathbb F_l)$ determined by the $l$-torsion points of $E_F$ contains the subgroup $SL_2(\mathbb F_l)\subseteq GL_2(\mathbb F_l)$; write $K\subseteq\overline F$ for the finite Galois extension of $F$ determined by the kernel of this homomorphism.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), Definition 3.1(c), second complete sentence; printed/PDF page(s) 62. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf.

> Also, we suppose that $l$ is prime to the [residue characteristics of the] elements of $\mathbb V_{\mathrm{mod}}^{\mathrm{bad}}$, as well as to the orders of the $q$-parameters of $E_F$ [i.e., in the terminology of [GenEll], Definition 3.3, the “local heights” of $E_F$] at the primes of $\mathbb V(F)^{\mathrm{bad}}$.

Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position* (February 2009), §3, local torsion discussion immediately before Lemma 3.2, sentence following the definition of M_l(E); printed/PDF page(s) 15. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf.

> Thus, $M_l(E)$ is [noncanonically!] isomorphic as an $\mathbb F_l$-module to $\mathbb F_l\times\mathbb F_l$, and, moreover, is equipped with a continuous action by $G_K$ induced by the natural action of $G_K$ on $\overline K$.

Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position* (February 2009), Definition 3.3, complete definition; printed/PDF page(s) 15. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf.

> We shall refer to the positive integer $v_K(q_E)\in\mathbb Z_{>0}$ as the local height of $E$ [or $E_K$].

**Actual consumer.** The action map and torsion-preservation lemma occur in rep_spec. localCompletion supplies the field for bad-place parameters and uniformizers. AdmissiblePrimeData and torsionField reach theorem110 in the original graph. qOrder feeds Corollary312VariantData.logQAt and then theorem110.

## Iut.Cor312.ThetaData.TateStructure

**Paper source context.** Étale Theta §1 constructs a surjection to Z from the graph covering of a split special fiber. Definition 2.5 specializes the theta-covering setting over a p-adic local field. Mochizuki I, Definition 3.1(f), chooses a cusp from the graph quotient’s canonical generator up to sign. GenEll §3 places the roots-of-unity part in the local torsion sequence. These are original-paper contexts for the selected local group interfaces. Definitions 2.3–2.5 concern log orbicurve coverings; they are not direct definitions of the Lean structure or its coordinate formulas.

**Implementation scope.** The nine selected commands are xCoord, yCoord, TateStructure, ofUnit, ofUnit_mul, ofUnit_one, ofUnit_inv, graphLine, and IsCanonical. xCoord and yCoord return zero at infinity. At an affine point they return (x−C.r)/C.u² and (y−C.t−C.s·(x−C.r))/C.u³. TateStructure has exactly six supplied fields: t, C, hC, iso, iso_x, and iso_y. hC identifies C • E with t.tateCurve. iso is an additive equivalence from Additive (kˣ / zpowers t.q) to E.toAffine.Point. The two coordinate fields pin iso away from units satisfying qⁿu=1. The source section declares a complete rank-one valued field; unused section assumptions may disappear during elaboration. This context packet does not certify retained compiler parameters. The structure does not explicitly require E.IsElliptic. It supplies a uniformization and proves no existence theorem for general E. The source’s later ofTateParameter construction is not selected. ofUnit composes the quotient map with the supplied iso. The three selected lemmas give multiplication-to-addition, the image of 1, and the image of inversion. graphLine is the AddSubgroup of images of units u with u^ℓ=1, for arbitrary ℓ : ℕ. Its closure proof uses those lemmas. IsCanonical, also for arbitrary ℓ : ℕ, requires a unit representative and an integer m with u^ℓ=q^(1+ℓm) or u^ℓ=q^(−1+ℓm). The selected commands do not require ℓ to be prime. They do not prove roots exist, graphLine lies in a torsion subgroup, a graph-quotient isomorphism, or identification with the paper’s canonical cusp. They do not establish a paper identity from their names.

Shinichi Mochizuki, *The Étale Theta Function and its Frobenioid-theoretic Manifestations* (December 2008), §1, printed page 11, first paragraph through “a natural surjection”; printed/PDF page(s) 11. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/The%20Etale%20Theta%20Function%20and%20its%20Frobenioid-theoretic%20Manifestations.pdf.

> Since the special fiber of $\mathfrak X$ is split, it follows that the universal graph-covering of the dual graph of this special fiber determines [up to composition with an element of $\operatorname{Aut}(\mathbb Z)=\{\pm1\}$] a natural surjection […]

Shinichi Mochizuki, *The Étale Theta Function and its Frobenioid-theoretic Manifestations* (December 2008), §2, paragraph immediately before Definition 2.5; printed/PDF page(s) 36. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/The%20Etale%20Theta%20Function%20and%20its%20Frobenioid-theoretic%20Manifestations.pdf.

> Now, we return to the discussion of §1. In particular, we assume that $K$ is a finite extension of $\mathbb Q_p$.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), Definition 3.1(f), third sentence; printed/PDF page(s) 63. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf.

> If $\underline v\in\underline{\mathbb V}^{\mathrm{bad}}$, then we assume that $\underline\epsilon_{\underline v}$ is the cusp that arises from the canonical generator [up to sign] “$\pm1$” of the quotient “$\mathbb Z$” that appears in the definition of a “hyperbolic orbicurve of type $(1,\mathbb Z/l\mathbb Z)_\pm$” given in [EtTh], Definition 2.5, (i).

Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position* (February 2009), §3, paragraph immediately before Lemma 3.2, first two Tate-parameter sentences; printed/PDF page(s) 15. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf.

> Moreover, the extension class associated to this exact sequence is precisely that obtained by extracting an $l$-th root of the Tate parameter $q_E\in\mathfrak m_K$. The Tate parameter is an element of $\mathfrak m_K$ that is naturally associated to $E$ and has the property that the subscheme $\mathcal O_K/(q_E)$ is equal to the pull-back via the classifying morphism $\operatorname{Spec}(\mathcal O_K)\to\overline{\mathcal M}_{\mathrm{ell}}$ — where we write $\overline{\mathcal M}_{\mathrm{ell}}$ for the moduli stack of one-dimensional semi-abelian varieties over $\mathbb Z$ — of the divisor at infinity $\infty_{\mathcal M}\subseteq\overline{\mathcal M}_{\mathrm{ell}}$.

**Actual consumer.** xCoord and yCoord serve the coordinate-pin fields. ofUnit and its selected lemmas support graphLine and IsCanonical. Those definitions feed TateFamily, InitialThetaData, Corollary312VariantData.data, and theorem110 in the original graph. This records use of supplied local data, not construction of all initial Θ-data.
