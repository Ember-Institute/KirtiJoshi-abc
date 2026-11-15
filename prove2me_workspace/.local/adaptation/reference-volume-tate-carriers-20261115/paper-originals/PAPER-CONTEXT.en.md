# Volume and Tate carrier source context

Author/source context only. Independent blind readbacks belong to separate records.

## Iut.Cor312.ContainerHull

**Paper source context.** Mochizuki III, Remark 3.9.5(i)–(ii), defines a local holomorphic hull and records its fixed-point, inclusion, and monotonicity properties. The definition requires a relatively compact subset with finite log-volume. For relatively compact input, the hull is the smallest containing scaled integral region with every multiplier component nonzero. For input that is not relatively compact, the paper specifies the full ambient space. Proposition 3.9(iii) supplies the finite-exception setting for global log-volumes. These passages provide service context for the local construction that applies supplied hull maps at each packet and each label-set index.

**Implementation scope.** The selected commands are ContainerHullSystem, IsAdmissible, hull_integralRegion, hullAdmissible, and hullFamily. ContainerHullSystem supplies one HullSystem for every packet and label-set index. It also supplies admissibility of each designated integral region. IsAdmissible requires each region to belong to the corresponding supplied admissible class. The integral region is a fixed point of its supplied hull. This proves preservation of the finite-exception condition under the packetwise operation hullAdmissible. That operation is defined on every AdmissibleRegion without an IsAdmissible premise; the premise is needed for the unselected inclusion and monotonicity results. hullFamily applies this operation at every label-set index. These definitions preserve the indices. They do not construct arithmetic hull systems or identify the arbitrary component rings with the paper’s fields. The prerequisite HullSystem has an arbitrary admissible class and a supplied total hull map. Outside that class its values are unconstrained. Its hull class uses unit multipliers and may be smaller than all such regions. Those choices differ from the full-space branch and nonzero field multipliers in the paper. The leastness and admissibility fields are supplied assumptions.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory III: Canonical Splittings of the Log-theta-lattice* (May 2020), Remark 3.9.5(i), opening hypothesis and final well-definedness sentence; printed/PDF page(s) 127. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf.

> Suppose that we are in the situation of Proposition 3.9, (i). […] be a subset that contains a relatively compact subset whose log-volume [cf. the discussion of Remark 3.1.1, (iii), (iv), as well as Remark 3.9.7, (ii), below] is finite [i.e., $>-\infty$]. […] One verifies immediately that the holomorphic hull is well-defined [under the conditions stated].

Shinichi Mochizuki, *Inter-universal Teichmüller Theory III: Canonical Splittings of the Log-theta-lattice* (May 2020), Remark 3.9.5(ii), displayed properties P1–P3; printed/PDF page(s) 127. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf.

> (P1) $\phi(H)=H$, for any $H\in\mathbb H$;
>
> (P2) $P\subseteq\phi(P)$, for any $P\in\mathbb P$;
>
> (P3) $\phi(P_1)\subseteq\phi(P_2)$, for any $P_1,P_2\in\mathbb P$ such that $P_1\subseteq P_2$.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory III: Canonical Splittings of the Log-theta-lattice* (May 2020), Proposition 3.9(iii), finite local-volume support and summation passage; printed/PDF page(s) 117. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf.

> for the subset of elements whose components, indexed by $v_{\mathbb Q}\in\mathbb V_{\mathbb Q}$, have zero log-volume [cf. (i)] for all but finitely many $v_{\mathbb Q}\in\mathbb V_{\mathbb Q}$. Then, by adding the log-volumes of (i) [all but finitely many of which are zero!] at the various $v_{\mathbb Q}\in\mathbb V_{\mathbb Q}$, one obtains a global log-volume […]

**Actual consumer.** HullFamily feeds RHSData.thetaHull and then RHSData.rhs and theorem110. IsAdmissible enters RHSData; the supplied local hull systems also enter local estimates. These paths use the data conditionally.

## Iut.Cor312.LogVolume

**Paper source context.** Mochizuki III, Proposition 3.9(i), gives packet-normalized local log-volumes with zero value on the designated integral structures. Multiplication by the residue characteristic subtracts its logarithm in the nonarchimedean case. The same item averages over the capsules of a procession. Proposition 3.9(iii) sums local values that vanish outside finitely many rational places. Remark 3.1.1(ii) gives arithmetic extension-degree weights; item (iii) warns that weighted log-volumes need not be logarithms of ordinary measures. The local interface separates supplied component values, packet values, the global sum, and the average over label sets.

**Implementation scope.** The selected commands are LogVolumeData, globalVol, and processionVol. LogVolumeData supplies real-valued component and packet functions on all subsets. It requires strictly positive place weights whose sum on each fiber is one. It records zero component values on finite-place integral subsets, a +log(p) law for preimages under multiplication by p on unit-scaled integral subsets, and zero on a designated archimedean subset archBall. The type of archBall does not assert that it is a Hermitian ball. The packet integral region has zero value. On a product region with every component nonempty, the packet value is the sum of component values weighted by the product of the place weights over labels. The law includes no compactness, measurability, or finite-positive-measure premise. These are actual interface conditions, not a construction of Haar measure. The functions have values on empty and unbounded sets, but no general monotonicity field is present. globalVol uses a finite sum over all rational places; the region equals the integral region outside a finite set, so the summand vanishes there. processionVol divides the sum of global values by the procession length. A zero length is permitted; Lean’s real division gives zero in that case. The code does not identify its weights with the paper’s degree formulas. In particular, the header’s intended [K_v:Q_vQ]/[K:Q] formula differs from the inverse-extension-degree formula on paper page 94. Positive weights with fiber sum one do not prove this missing arithmetic identification. Global principal-element invariance and equality with arithmetic degree are not fields of this interface.

**Effective source.** Accepted graph ci-012771-ee109b3e uses the local override. Its SHA-256 is 002f44da071e858c1fe48f3608da4e75f1179d3cd6c3007444bc5453440b7ef0; upstream is 79f0f12f1c82d6a0b6b83a42197527542fa946e9a5bb8dd4fd3572fd88edaf15. The override adds elaboration settings and an explicit local CommRing instance, typed binder, and typed prime cast in componentVol_prime_preimage. It does not claim to be the unchanged upstream Git blob.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory III: Canonical Splittings of the Log-theta-lattice* (May 2020), Remark 3.1.1(ii), normalized direct-sum weight display; printed/PDF page(s) 94. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf.

> When, moreover, we consider direct sums over all $\underline v\in\underline{\mathbb V}$ lying over a given $v_{\mathbb Q}\in\mathbb V_{\mathbb Q}$ as in the case of $\underline{\log}({}^{\alpha}\mathcal F_{v_{\mathbb Q}})$, it will be convenient to use the normalized weight
>
> $$\frac{1}{[K_{\underline v}:(F_{\mathrm{mod}})_v]\cdot\left(\sum_{\mathbb V_{\mathrm{mod}}
> i w\mid v_{\mathbb Q}}[(F_{\mathrm{mod}})_w:\mathbb Q_{v_{\mathbb Q}}]\right)}$$

Shinichi Mochizuki, *Inter-universal Teichmüller Theory III: Canonical Splittings of the Log-theta-lattice* (May 2020), Remark 3.1.1(iii), displayed warning; printed/PDF page(s) 95. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf.

> such weighted sums of log-volumes do not, in general, arise as some positive real multiple of the [natural] logarithm of a “volume” or “measure” in the usual sense of measure theory.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory III: Canonical Splittings of the Log-theta-lattice* (May 2020), Proposition 3.9(i), nonarchimedean packet-normalization sentence; printed/PDF page(s) 115. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf.

> Here, we assume that these log-volumes are normalized so that multiplication of an element of “$\mathfrak M(-)$” by $p_{\underline v}$ corresponds to adding the quantity $-\log(p_{\underline v})\in\mathbb R$; we shall refer to this normalization as the packet-normalization.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory III: Canonical Splittings of the Log-theta-lattice* (May 2020), Proposition 3.9(i), final averaging sentence; printed/PDF page(s) 116. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf.

> Finally, when working with collections of capsules in a procession, as in Proposition 3.4, (ii), we obtain, in both the nonarchimedean and archimedean cases, log-volumes on the products of the “$\mathfrak M(-)$” associated to the various capsules under consideration, which we normalize by taking the average, over the various capsules under consideration; we shall refer to this normalization as the procession-normalization [cf. Remark 3.9.3 below].

Shinichi Mochizuki, *Inter-universal Teichmüller Theory III: Canonical Splittings of the Log-theta-lattice* (May 2020), Proposition 3.9(iii), finite local-volume support and summation passage; printed/PDF page(s) 117. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf.

> for the subset of elements whose components, indexed by $v_{\mathbb Q}\in\mathbb V_{\mathbb Q}$, have zero log-volume [cf. (i)] for all but finitely many $v_{\mathbb Q}\in\mathbb V_{\mathbb Q}$. Then, by adding the log-volumes of (i) [all but finitely many of which are zero!] at the various $v_{\mathbb Q}\in\mathbb V_{\mathbb Q}$, one obtains a global log-volume […]

**Actual consumer.** globalVol feeds LocalEstimate.rhs_le and theorem110. processionVol feeds RHSData.rhs and theorem110. These paths use supplied functions and laws; they do not prove the local numerical estimates.

## TateCurvesTheta.QParameter.PrimeToOrder

**Paper source context.** Mochizuki I, Definition 3.1(c), assumes that the chosen prime is prime to the orders of the q-parameters at the indicated bad primes. It identifies those orders with the local heights of GenEll, Definition 3.3. In GenEll §3, the local setting uses a finite extension of Q_p and a surjective integer valuation. The local height is the positive integer v_K(q_E). This supplies the mathematical service context for a coprimality predicate and a positive integer attached to a parameter.

**Implementation scope.** PrimeToOrder ℓ n is Nat.Coprime ℓ n for arbitrary natural numbers ℓ and n. Its definition does not require that ℓ be prime. OrderedTateParameter extends an arbitrary NormedField TateParameter with a supplied positive natural number orderNat. The structure itself contains no equation relating orderNat to q, a valuation, the series, or the curve. Its PrimeToOrder predicate applies Nat.Coprime to ℓ and orderNat. The selected decidability instances implement these predicates. No theorem here asserts the existence of a suitable prime or proves that a particular prime satisfies the condition. The paper also assumes coprimality with residue characteristics; that is separate from this predicate. The later toOrdered construction supplies a particular norm-based order under a uniformizer assumption, but does not change what an arbitrary OrderedTateParameter contains.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), Definition 3.1(c), second complete sentence; printed/PDF page(s) 62. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf.

> Also, we suppose that $l$ is prime to the [residue characteristics of the] elements of $\mathbb V_{\mathrm{mod}}^{\mathrm{bad}}$, as well as to the orders of the $q$-parameters of $E_F$ [i.e., in the terminology of [GenEll], Definition 3.3, the “local heights” of $E_F$] at the primes of $\mathbb V(F)^{\mathrm{bad}}$.

Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position* (February 2009), §3, paragraph introducing local theory at nonarchimedean primes, immediately before the torsion discussion; printed/PDF page(s) 14, 15. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf.

> Next, we consider the local theory at nonarchimedean primes. Let $K$ be a finite extension of $\mathbb Q_p$ [where $p$ is a prime number] with residue field $k$, maximal ideal $\mathfrak m_K\subseteq\mathcal O_K$, and valuation map $v_K:K^{\times}\to\mathbb Z$ [which we normalize so that $v_K$ is surjective]; $\overline K$ an algebraic closure of $K$; $G_K\overset{\mathrm{def}}{=}\operatorname{Gal}(\overline K/K)$; $E\to\operatorname{Spec}(\mathcal O_K)$ a one-dimensional semi-abelian scheme over $\mathcal O_K$ such that the generic fiber $E_K$ of $E$ is proper, while the special fiber $E_k$ of $E$ is isomorphic to $(\mathbb G_m)_k$, the multiplicative group over $k$.

Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position* (February 2009), Definition 3.3, complete definition; printed/PDF page(s) 15. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf.

> We shall refer to the positive integer $v_K(q_E)\in\mathbb Z_{>0}$ as the local height of $E$ [or $E_K$].

**Actual consumer.** orderNat feeds AdmissiblePrimeData.qOrder, Corollary312VariantData.logQAt, and theorem110. The coprimality predicate enters AdmissiblePrimeData. The decidability instances support predicate elaboration and evaluation; they are not additional paper results.

## TateCurvesTheta.TateCurve.Weierstrass

**Paper source context.** GenEll §3 discusses the Tate parameter q_E naturally associated to a specified semi-abelian curve E over a local integer ring. Its local height is v_K(q_E). This original passage supplies the curve-and-parameter setting served by the explicit coefficient construction. It does not give the q-series formulas in the selected source commands. Those formulas are implementation definitions from the tate-curves-theta repository. Their source comment cites Silverman; that comment is implementation provenance, not a visually checked original-paper quotation in this unit.

**Implementation scope.** For a TateParameter t over an arbitrary NormedField K, eisenstein k is the total infinite sum over n≥0 of (n+1)^k q^(n+1)/(1-q^(n+1)). The selected definitions set a₄=-5·eisenstein 3 and a₆=-(5·eisenstein 3+7·eisenstein 5)/12. tateCurve is a WeierstrassCurve with a₁=1, a₂=a₃=0, and these a₄,a₆. The four definitions require neither completeness nor an ultrametric norm. Their infinite sum uses Lean’s total tsum; these definitions alone do not prove convergence. The source file proves summability separately under completeness and an ultrametric norm, but those proofs are not selected here. In characteristics dividing 12, division by the field element 12 follows Lean’s total division convention. There is no characteristic restriction in these definitions. The result is a WeierstrassCurve, with no selected smoothness, discriminant-nonvanishing, elliptic-curve, uniformization, or identity theorem identifying it with GenEll’s E. Calling the declaration tateCurve does not establish those bridges.

Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position* (February 2009), §3, paragraph introducing local theory at nonarchimedean primes, immediately before the torsion discussion; printed/PDF page(s) 14, 15. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf.

> Next, we consider the local theory at nonarchimedean primes. Let $K$ be a finite extension of $\mathbb Q_p$ [where $p$ is a prime number] with residue field $k$, maximal ideal $\mathfrak m_K\subseteq\mathcal O_K$, and valuation map $v_K:K^{\times}\to\mathbb Z$ [which we normalize so that $v_K$ is surjective]; $\overline K$ an algebraic closure of $K$; $G_K\overset{\mathrm{def}}{=}\operatorname{Gal}(\overline K/K)$; $E\to\operatorname{Spec}(\mathcal O_K)$ a one-dimensional semi-abelian scheme over $\mathcal O_K$ such that the generic fiber $E_K$ of $E$ is proper, while the special fiber $E_k$ of $E$ is isomorphic to $(\mathbb G_m)_k$, the multiplicative group over $k$.

Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position* (February 2009), §3, paragraph immediately before Lemma 3.2, first two Tate-parameter sentences; printed/PDF page(s) 15. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf.

> Moreover, the extension class associated to this exact sequence is precisely that obtained by extracting an $l$-th root of the Tate parameter $q_E\in\mathfrak m_K$. The Tate parameter is an element of $\mathfrak m_K$ that is naturally associated to $E$ and has the property that the subscheme $\mathcal O_K/(q_E)$ is equal to the pull-back via the classifying morphism $\operatorname{Spec}(\mathcal O_K)\to\overline{\mathcal M}_{\mathrm{ell}}$ — where we write $\overline{\mathcal M}_{\mathrm{ell}}$ for the moduli stack of one-dimensional semi-abelian varieties over $\mathbb Z$ — of the divisor at infinity $\infty_{\mathcal M}\subseteq\overline{\mathcal M}_{\mathrm{ell}}$.

Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position* (February 2009), Definition 3.3, complete definition; printed/PDF page(s) 15. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf.

> We shall refer to the positive integer $v_K(q_E)\in\mathbb Z_{>0}$ as the local height of $E$ [or $E_K$].

**Actual consumer.** The series feeds a₄ and a₆, which feed tateCurve, tateJ, AdmissiblePrimeData, and theorem110. This is the graph’s coefficient-to-invariant path, not an identification with a paper curve.

## TateCurvesTheta.QParameter.NormalizedOrder

**Paper source context.** GenEll §3 fixes a surjective valuation v_K:K^×→Z in its p-adic local setting. Definition 3.3 calls the positive integer v_K(q_E) the local height. Mochizuki I, Definition 3.1(c), refers to these local heights as the orders of the q-parameters. The selected local construction uses a supplied element whose norm generates all nonzero norm values. It then chooses the integer exponent of the parameter norm and proves that this exponent is positive. The original passages explain the normalization served by this construction.

**Implementation scope.** IsUniformizer π requires π≠0, ‖π‖<1, and an integer exponent representation ‖x‖=‖π‖^n for every unit x. This is a condition on a normed field; the selected statements do not require completeness or an ultrametric norm. The selected lemmas give ‖π‖>0 and log‖π‖<0. For a TateParameter t, exists_norm_q_eq_zpow obtains an exponent from the generation field. orderZ chooses such an integer. norm_q_eq_zpow gives its defining equation, and orderZ_pos proves positivity from the strict norm bounds. toOrdered sets orderNat to the natural-number conversion of this positive integer and preserves t. Positivity makes this conversion exact, although integer-to-natural conversion is generally truncated. This unit does not construct a uniformizer for an arithmetic completion. It does not prove that the norm-derived exponent agrees with the paper’s valuation, a special-fiber component count, or the order of a curve identified with the paper’s E. Those arithmetic identifications require additional input.

Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position* (February 2009), §3, paragraph introducing local theory at nonarchimedean primes, immediately before the torsion discussion; printed/PDF page(s) 14, 15. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf.

> Next, we consider the local theory at nonarchimedean primes. Let $K$ be a finite extension of $\mathbb Q_p$ [where $p$ is a prime number] with residue field $k$, maximal ideal $\mathfrak m_K\subseteq\mathcal O_K$, and valuation map $v_K:K^{\times}\to\mathbb Z$ [which we normalize so that $v_K$ is surjective]; $\overline K$ an algebraic closure of $K$; $G_K\overset{\mathrm{def}}{=}\operatorname{Gal}(\overline K/K)$; $E\to\operatorname{Spec}(\mathcal O_K)$ a one-dimensional semi-abelian scheme over $\mathcal O_K$ such that the generic fiber $E_K$ of $E$ is proper, while the special fiber $E_k$ of $E$ is isomorphic to $(\mathbb G_m)_k$, the multiplicative group over $k$.

Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position* (February 2009), Definition 3.3, complete definition; printed/PDF page(s) 15. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf.

> We shall refer to the positive integer $v_K(q_E)\in\mathbb Z_{>0}$ as the local height of $E$ [or $E_K$].

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), Definition 3.1(c), second complete sentence; printed/PDF page(s) 62. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf.

> Also, we suppose that $l$ is prime to the [residue characteristics of the] elements of $\mathbb V_{\mathrm{mod}}^{\mathrm{bad}}$, as well as to the orders of the $q$-parameters of $E_F$ [i.e., in the terminology of [GenEll], Definition 3.3, the “local heights” of $E_F$] at the primes of $\mathbb V(F)^{\mathrm{bad}}$.

**Actual consumer.** toOrdered feeds AdmissiblePrimeData.qOrder, Corollary312VariantData.logQAt, and theorem110. The selected exponent lemmas and norm facts support toOrdered. IsUniformizer is an input to AdmissiblePrimeData.
