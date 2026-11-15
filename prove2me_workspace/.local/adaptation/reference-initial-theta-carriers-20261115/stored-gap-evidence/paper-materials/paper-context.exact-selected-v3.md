English original-paper source context for exactly four bundles and 19 selected source commands.

This document is author/source context, separate from independent blind code-only readback. AST selection is from ci-014795-5a7d0419. Actual compiler type evidence from ci-014954-6c6f799b corrects the scalar-action scope: towerModK does not constrain the stored algebraModK. Compatibility between the canonical action used by tate and the stored algebra used by localData remains a producer obligation. This document does not discharge it. AG and TG remain supplied interfaces. Object existence and identification with the paper objects remain separate.

## Iut.Cor312.ThetaData.Orbicurve

**Paper source context.** Mochizuki I, Definition 3.1(d), specifies the torsion orbicurve, its K-core, and cartesian covering diagrams. Definition 3.1(f) chooses a cusp from a nonzero element of Q. Étale Theta Definition 2.1 defines the relevant orbicurve types through its preceding covering construction. Those passages provide the intended arithmetic meaning of this module. They do not define the Lean interface or prove that an arbitrary instance realizes that meaning.

**Selected implementation scope.**

`Iut.AnabelianGeometry` — Defines the supplied AnabelianGeometry interface with all 21 fields. Orbicurve, Cover, Cusp, RankOneQuotient, and the local TateStructure are type-valued fields. HasCore, IsCartesianSquare, and the three type predicates are supplied predicates. pi1 returns a ProfiniteGrp object. pi1Cover has supplied continuity and open-embedding laws. The record gives no geometric realization or general functor laws for the named operations. HasCore has no terminal-object law. AG.TateStructure is distinct from the concrete Iut.TateStructure, with no bridge supplied here. The interface itself is not constructed by this command.

`Iut.OrbicurveDataSection.CF` — Defines CF by applying AG.pmQuotient to AG.oncePunctured E. This applies supplied interface operations; it does not construct or verify a geometric quotient.

`Iut.OrbicurveDataSection.XK` — Defines XK by applying AG.baseChange to AG.oncePunctured E along F → P.torsionField. The fixed-field extension is an input. This command proves no finite-field-extension or geometric base-change theorem.

`Iut.OrbicurveDataSection.CK` — Defines CK by applying AG.baseChange to CF along F → P.torsionField. It proves no core property.

`Iut.OrbicurveDataSection.OrbicurveData` — Defines OrbicurveData with all 15 fields: CKu, CKu_type, CKu_core, XKu, XKu_type, XKu_to_XK, XKu_to_CKu, XK_to_CK, CKu_to_CK, diagram_cartesian, QIso, q, q_ne_zero, epsilon, and epsilon_spec. The objects, covers, predicates, and cusp are supplied data. QIso is an ordinary type equivalence with ZMod ℓ. RankOneQuotient has no required additive or module structure. q_ne_zero means QIso q ≠ 0; it does not prove intrinsic algebraic nonvanishing or invariance under arbitrary type equivalences. epsilon_spec pins the chosen cusp to the supplied cuspOfQuotient operation. The record does not construct the geometry, the cusp choice, or an inhabitant.

**Complete field inventory of selected structures.**

- `AnabelianGeometry` (21 fields): `Orbicurve`, `Cover`, `coverComp`, `baseChange`, `coverBaseChange`, `oncePunctured`, `pmQuotient`, `pi1`, `pi1Cover`, `pi1Cover_continuous`, `pi1Cover_isOpenEmbedding`, `IsCartesianSquare`, `Cusp`, `cuspBaseChange`, `HasCore`, `IsTypeOneEllTors`, `IsTypeOneEllTorsPM`, `TateStructure`, `IsTypeOneZModPM`, `RankOneQuotient`, `cuspOfQuotient`.
- `OrbicurveData` (15 fields): `CKu`, `CKu_type`, `CKu_core`, `XKu`, `XKu_type`, `XKu_to_XK`, `XKu_to_CKu`, `XK_to_CK`, `CKu_to_CK`, `diagram_cartesian`, `QIso`, `q`, `q_ne_zero`, `epsilon`, `epsilon_spec`.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), Definition 3.1(d), first sentence; printed/PDF page(s) 62. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf.

> $\underline C_K$ is a hyperbolic orbicurve of type $(1,l\text{-tors})_\pm$ [cf. [EtTh], Definition 2.1] over $K$, with $K$-core [cf. [CanLift], Remark 2.1.1; [EtTh], the discussion at the beginning of §2] given by $C_K\overset{\mathrm{def}}{=}C_F\times_F K$.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), Definition 3.1(d), sentence beginning “In particular”, with the three diagrams omitted; printed/PDF page(s) 62. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf.

> In particular, $\underline C_K$ determines, up to $K$-isomorphism, a hyperbolic orbicurve $\underline X_K$ of type $(1,l\text{-tors})$ [cf. [EtTh], Definition 2.1] over $K$, together with natural cartesian diagrams […] of finite étale coverings of hyperbolic orbicurves and corresponding open immersions of profinite groups.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), Definition 3.1(f), first sentence; printed/PDF page(s) 63. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf.

> $\underline\epsilon$ is a cusp of the hyperbolic orbicurve $\underline C_K$ [cf. (d)] that arises from a nonzero element of the quotient “$Q$” that appears in the definition of a “hyperbolic orbicurve of type $(1,l\text{-tors})_\pm$” given in [EtTh], Definition 2.1.

Shinichi Mochizuki, *The Étale Theta Function and its Frobenioid-theoretic Manifestations* (December 2008), Definition 2.1, full definition; printed/PDF page(s) 33. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/The%20Etale%20Theta%20Function%20and%20its%20Frobenioid-theoretic%20Manifestations.pdf.

> We shall refer to a smooth log orbicurve over $K$ that arises, up to isomorphism, as the smooth log orbicurve $\underline X^{\log}$ (respectively, $\underline C^{\log}$) constructed above for some choice of $\overline\Pi_X^{\mathrm{ell}}\twoheadrightarrow Q$ as being of type $(1,l\text{-tors})$ (respectively, $(1,l\text{-tors})_\pm$). We shall also apply this terminology to the associated hyperbolic orbicurves.

**Actual consumer.** The selected CF, XK, and CK definitions serve OrbicurveData. The supplied geometry and OrbicurveData feed LocalThetaData and InitialThetaData. Consumer paths are from the accepted original graph; they do not certify adapted kernel acceptance.

## Iut.Cor312.ThetaData.TateFamily

**Paper source context.** Mochizuki I, Definition 3.1(e)–(f), localizes the global covering data at chosen places and imposes a canonical graph-cusp condition. Étale Theta §1 derives the graph quotient from a split special fiber. GenEll §3 describes the local Tate parameter and its role in torsion. These passages explain the local uniformization context. They do not state the exact two Galois-equivariance fields in this Lean record.

**Selected implementation scope.**

`Iut.instDecidableEqIntermediateField` — Defines a local decidable-equality instance on the intermediate field by Classical.propDecidable. This supports the source implementation. It asserts no arithmetic or geometric property from the paper.

`Iut.curveK` — Abbreviates the Weierstrass curve obtained from E by the algebra map F → K. K is a supplied intermediate field with a NumberField instance in the source context.

`Iut.emb` — Abbreviates the finite-place embedding from K into localCompletion w.

`Iut.curveKw` — Abbreviates the map of curveK into the completion through emb. It does not assert split multiplicative reduction or existence of a Tate uniformization.

`Iut.galK` — Defines the additive map on affine nonsingular points induced by an F-algebra automorphism of K through the functorial point map.

`Iut.IsBadPlace` — Defines the predicate that a finite place w of K lies over some v in VBad. The predicate does not itself prove bad reduction.

`Iut.isBadPlace_galPlace` — Proves that IsBadPlace is preserved by the place action of an F-algebra automorphism of K. The proof uses the imported LiesOver transport lemma.

`Iut.TateFamily` — Defines TateFamily with all three supplied fields: S, graphLine_galPlace, and isCanonical_galPlace. S supplies a concrete Iut.TateStructure at every place satisfying IsBadPlace. The two remaining fields impose equality of the pulled-back graph subgroups under the Galois action and equivalence of the canonical-point predicates. The definition accepts arbitrary ℓ : ℕ and a number-field intermediate field K. It does not itself require ℓ to be prime or identify K with the torsion field. It does not construct the local structures or prove either equivariance field. No bridge to the abstract AG.TateStructure fields is supplied. Mathematical existence and uniqueness arguments in the source introduction are not proofs delivered by this selected command. The actual compiled TateFamily type has no parameter for InitialThetaData.algebraModK or towerModK. Its field-of-moduli relation uses the canonical inclusion into F. Compatibility with the separately stored algebra used by localData is a pending producer obligation.

**Complete field inventory of selected structures.**

- `TateFamily` (3 fields): `S`, `graphLine_galPlace`, `isCanonical_galPlace`.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), Definition 3.1(e), first sentence and its explanatory clause; printed/PDF page(s) 62. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf.

> $\underline{\mathbb V}\subseteq\mathbb V(K)$ is a subset that induces a natural bijection $\underline{\mathbb V}\xrightarrow{\sim}\mathbb V_{\mathrm{mod}}$ — i.e., a section of the natural surjection $\mathbb V(K)\twoheadrightarrow\mathbb V_{\mathrm{mod}}$.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), Definition 3.1(f), third sentence; printed/PDF page(s) 63. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf.

> If $\underline v\in\underline{\mathbb V}^{\mathrm{bad}}$, then we assume that $\underline\epsilon_{\underline v}$ is the cusp that arises from the canonical generator [up to sign] “$\pm1$” of the quotient “$\mathbb Z$” that appears in the definition of a “hyperbolic orbicurve of type $(1,\mathbb Z/l\mathbb Z)_\pm$” given in [EtTh], Definition 2.5, (i).

Shinichi Mochizuki, *The Étale Theta Function and its Frobenioid-theoretic Manifestations* (December 2008), §1, printed page 11, first paragraph through “a natural surjection”; printed/PDF page(s) 11. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/The%20Etale%20Theta%20Function%20and%20its%20Frobenioid-theoretic%20Manifestations.pdf.

> Since the special fiber of $\mathfrak X$ is split, it follows that the universal graph-covering of the dual graph of this special fiber determines [up to composition with an element of $\operatorname{Aut}(\mathbb Z)=\{\pm1\}$] a natural surjection […]

Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position* (February 2009), §3, paragraph introducing local theory at nonarchimedean primes, immediately before the torsion discussion; printed/PDF page(s) 14, 15. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf.

> Next, we consider the local theory at nonarchimedean primes. Let $K$ be a finite extension of $\mathbb Q_p$ [where $p$ is a prime number] with residue field $k$, maximal ideal $\mathfrak m_K\subseteq\mathcal O_K$, and valuation map $v_K:K^{\times}\to\mathbb Z$ [which we normalize so that $v_K$ is surjective]; $\overline K$ an algebraic closure of $K$; $G_K\overset{\mathrm{def}}{=}\operatorname{Gal}(\overline K/K)$; $E\to\operatorname{Spec}(\mathcal O_K)$ a one-dimensional semi-abelian scheme over $\mathcal O_K$ such that the generic fiber $E_K$ of $E$ is proper, while the special fiber $E_k$ of $E$ is isomorphic to $(\mathbb G_m)_k$, the multiplicative group over $k$.

Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position* (February 2009), §3, paragraph immediately before Lemma 3.2, first two Tate-parameter sentences; printed/PDF page(s) 15. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf.

> Moreover, the extension class associated to this exact sequence is precisely that obtained by extracting an $l$-th root of the Tate parameter $q_E\in\mathfrak m_K$. The Tate parameter is an element of $\mathfrak m_K$ that is naturally associated to $E$ and has the property that the subscheme $\mathcal O_K/(q_E)$ is equal to the pull-back via the classifying morphism $\operatorname{Spec}(\mathcal O_K)\to\overline{\mathcal M}_{\mathrm{ell}}$ — where we write $\overline{\mathcal M}_{\mathrm{ell}}$ for the moduli stack of one-dimensional semi-abelian varieties over $\mathbb Z$ — of the divisor at infinity $\infty_{\mathcal M}\subseteq\overline{\mathcal M}_{\mathrm{ell}}$.

**Actual consumer.** The selected base-field, completion, point-action, and bad-place commands support TateFamily. InitialThetaData.tate carries this supplied family at prime.torsionField and prime.ℓ. The selection includes no graphLineAt or IsCanonicalAt helper.

## Iut.Cor312.ThetaData.LocalConditions

**Paper source context.** Mochizuki I, Definition 3.1(e), chooses a section of places and states local covering, decomposition-group, and theta-root-model conditions. Definition 3.1(f) gives the canonical graph-cusp condition and the convention for the local group at good places. The continuation of (e) uses the tempered group at bad places. Étale Theta Definitions 2.3 and 2.5 explain the theta-covering types. In the fixed May 2020 PDF, these IUT passages are printed/PDF pages 62–63. The source comment’s page numbers 70–71 are not used for this packet.

**Selected implementation scope.**

`Iut.TemperedGeometry` — Defines TemperedGeometry with all seven fields: tempPi1, tempPi1Group, tempPi1Topology, tempToEtale, tempToEtale_continuous, IsThetaRootModel, and canonicalGraphCusp. It supplies a group and topology, plus a continuous homomorphism to AG.pi1. It imposes no topological-group compatibility, dense-image condition, or profinite-completion universal property. tempPi1 is declared for every field. The theta-root predicate and canonical cusp remain interface fields. canonicalGraphCusp has no explicit ℓ parameter. This command does not construct a tempered-fundamental-group theory or a theta-root model.

`Iut.ValuationSection` — Defines ValuationSection with all four fields: sectFin, sectInf, sectFin_liesOver, and sectInf_liesOver. These supply finite and infinite place choices with their LiesOver conditions. The record assumes the NumberField and field-of-moduli algebra instances required for its inputs. It does not construct the choices or prove initial-data existence. The actual compiled record takes a supplied field-of-moduli algebra on K. InitialThetaData.localData uses its stored algebraModK for this input. The compiled towerModK field does not establish compatibility of that stored algebra with the canonical action used by TateFamily; that compatibility is a pending producer obligation.

`Iut.localize` — Defines localize by AG.baseChange along the finite-place embedding into the completion. The exact selected AST command includes its variable … in wrapper. This definition supplies no general geometric base-change laws.

`Iut.LocalThetaData` — Defines LocalThetaData with all nine fields: sect, local_diagram_cartesian, decomp, decomp_isClosed, tateX, tateC, bad_type, bad_theta_model, and epsilon_graph. The local cartesian condition is supplied. decomp is a subgroup choice at every finite place of K, constrained only by closedness. No field identifies it with the valuation stabilizer or supplies the paper’s outer surjection onto it. tateX and tateC use the abstract AG.TateStructure. bad_type is applied to localized XKu, whereas the paper’s stated type condition concerns localized C. bad_theta_model is a supplied predicate on XKu; it does not construct separately named double-underlined natural models. epsilon_graph is an equality using the supplied canonicalGraphCusp. These fields do not prove that an arbitrary input realizes the original paper geometry. The actual compiled InitialThetaData.localData type passes the stored algebraModK to this record and its ValuationSection. InitialThetaData.tate does not take that stored algebra or towerModK. Agreement between the two scalar actions is a pending producer obligation.

**Complete field inventory of selected structures.**

- `TemperedGeometry` (7 fields): `tempPi1`, `tempPi1Group`, `tempPi1Topology`, `tempToEtale`, `tempToEtale_continuous`, `IsThetaRootModel`, `canonicalGraphCusp`.
- `ValuationSection` (4 fields): `sectFin`, `sectInf`, `sectFin_liesOver`, `sectInf_liesOver`.
- `LocalThetaData` (9 fields): `sect`, `local_diagram_cartesian`, `decomp`, `decomp_isClosed`, `tateX`, `tateC`, `bad_type`, `bad_theta_model`, `epsilon_graph`.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), Definition 3.1(e), first sentence and its explanatory clause; printed/PDF page(s) 62. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf.

> $\underline{\mathbb V}\subseteq\mathbb V(K)$ is a subset that induces a natural bijection $\underline{\mathbb V}\xrightarrow{\sim}\mathbb V_{\mathrm{mod}}$ — i.e., a section of the natural surjection $\mathbb V(K)\twoheadrightarrow\mathbb V_{\mathrm{mod}}$.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), Definition 3.1(e), continuation at the top of printed page 63; printed/PDF page(s) 63. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf.

> the various profinite groups […] admit natural outer surjections onto the decomposition group $G_{\underline v}\subseteq G_K\overset{\mathrm{def}}{=}\operatorname{Gal}(\overline F/K)$ determined, up to $G_K$-conjugacy, by $\underline v$.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), Definition 3.1(e), sentence beginning “Finally” on printed page 63, through the displayed natural models; printed/PDF page(s) 63. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf.

> Finally, we observe that when $\underline v\in\underline{\mathbb V}^{\mathrm{bad}}$, it follows from the theory of [EtTh], §2 — i.e., roughly speaking, “by extracting an $l$-th root of the theta function” — that $\underline X_{\underline v}$, $\underline C_{\underline v}$ admit natural models $\underline{\underline X}_{\underline v}$, $\underline{\underline C}_{\underline v}$ […]

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), Definition 3.1(f), third sentence; printed/PDF page(s) 63. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf.

> If $\underline v\in\underline{\mathbb V}^{\mathrm{bad}}$, then we assume that $\underline\epsilon_{\underline v}$ is the cusp that arises from the canonical generator [up to sign] “$\pm1$” of the quotient “$\mathbb Z$” that appears in the definition of a “hyperbolic orbicurve of type $(1,\mathbb Z/l\mathbb Z)_\pm$” given in [EtTh], Definition 2.5, (i).

Shinichi Mochizuki, *The Étale Theta Function and its Frobenioid-theoretic Manifestations* (December 2008), Definition 2.3, full definition; printed/PDF page(s) 35. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/The%20Etale%20Theta%20Function%20and%20its%20Frobenioid-theoretic%20Manifestations.pdf.

> We shall refer to a smooth log orbicurve over $K$ that arises, up to isomorphism, as the smooth log orbicurve $\underline{\underline X}^{\log}$ (respectively, $\underline{\underline C}^{\log}$) constructed in Proposition 2.2 above as being of type $(1,l\text{-tors}^{\Theta})$ (respectively, $(1,l\text{-tors}^{\Theta})_\pm$). We shall also apply this terminology to the associated hyperbolic orbicurves.

Shinichi Mochizuki, *The Étale Theta Function and its Frobenioid-theoretic Manifestations* (December 2008), §2, paragraph immediately before Definition 2.5; printed/PDF page(s) 36. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/The%20Etale%20Theta%20Function%20and%20its%20Frobenioid-theoretic%20Manifestations.pdf.

> Now, we return to the discussion of §1. In particular, we assume that $K$ is a finite extension of $\mathbb Q_p$.

**Actual consumer.** TemperedGeometry, ValuationSection, and localize support the selected LocalThetaData structure. InitialThetaData carries LocalThetaData as localData. Torsion-field finiteness proofs, valuation-image helpers, PivBad, and PivGood are not part of this 19-command selection.

## Iut.Cor312.ThetaData.Basic

**Paper source context.** Mochizuki I, Definition 3.1(a)–(f), specifies initial Θ-data by global, torsion, orbicurve, place, and cusp conditions. The present module assembles corresponding Lean interfaces and records. The paper’s statements of determined objects and natural models are source context. They do not establish the existence of a Lean value or discharge the AG and TG interfaces.

**Selected implementation scope.**

`Iut.InitialThetaData` — Defines InitialThetaData with all 18 fields, including instance fields: F, fieldF, numberFieldF, Fbar, fieldFbar, algebraFbar, isAlgClosure, E, isElliptic, VBad, global, prime, numberFieldK, algebraModK, towerModK, tate, orb, and localData. The assembled record explicitly requires IsAlgClosure F Fbar. It carries the NumberField instance on the fixed field K and a stored F_mod-algebra structure algebraModK. In the actual compiled type, towerModK uses IntermediateField.instSMulSubtypeMem to restrict the canonical F-action on K. Its type does not mention the stored algebraModK. Thus towerModK does not state compatibility of that stored algebra with the canonical action. The source comment claims that the field pins this compatibility uniquely; the compiled type does not express that claim. The tate field takes neither algebraModK nor towerModK, while localData and its ValuationSection use the stored algebraModK. Compatibility of these actions is a pending producer obligation. The concrete TateFamily in tate is not connected by a field or theorem here to the abstract AG Tate structures in localData. The record is relative to supplied AG and TG. It does not construct these interfaces, choose its mathematical inputs, prove an inhabitant exists, or establish full initial-Θ-data existence.

`Iut.InitialThetaData.ℓ` — Defines the natural-number helper ℓ by reading D.prime.ℓ. The prime conditions are supplied through D.prime; this helper does not construct an admissible prime.

**Complete field inventory of selected structures.**

- `InitialThetaData` (18 fields): `F`, `fieldF`, `numberFieldF`, `Fbar`, `fieldFbar`, `algebraFbar`, `isAlgClosure`, `E`, `isElliptic`, `VBad`, `global`, `prime`, `numberFieldK`, `algebraModK`, `towerModK`, `tate`, `orb`, `localData`.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), Definition 3.1(d), first sentence; printed/PDF page(s) 62. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf.

> $\underline C_K$ is a hyperbolic orbicurve of type $(1,l\text{-tors})_\pm$ [cf. [EtTh], Definition 2.1] over $K$, with $K$-core [cf. [CanLift], Remark 2.1.1; [EtTh], the discussion at the beginning of §2] given by $C_K\overset{\mathrm{def}}{=}C_F\times_F K$.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), Definition 3.1(e), first sentence and its explanatory clause; printed/PDF page(s) 62. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf.

> $\underline{\mathbb V}\subseteq\mathbb V(K)$ is a subset that induces a natural bijection $\underline{\mathbb V}\xrightarrow{\sim}\mathbb V_{\mathrm{mod}}$ — i.e., a section of the natural surjection $\mathbb V(K)\twoheadrightarrow\mathbb V_{\mathrm{mod}}$.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), Definition 3.1(f), first sentence; printed/PDF page(s) 63. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf.

> $\underline\epsilon$ is a cusp of the hyperbolic orbicurve $\underline C_K$ [cf. (d)] that arises from a nonzero element of the quotient “$Q$” that appears in the definition of a “hyperbolic orbicurve of type $(1,l\text{-tors})_\pm$” given in [EtTh], Definition 2.1.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), Definition 3.1(f), third sentence; printed/PDF page(s) 63. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf.

> If $\underline v\in\underline{\mathbb V}^{\mathrm{bad}}$, then we assume that $\underline\epsilon_{\underline v}$ is the cusp that arises from the canonical generator [up to sign] “$\pm1$” of the quotient “$\mathbb Z$” that appears in the definition of a “hyperbolic orbicurve of type $(1,\mathbb Z/l\mathbb Z)_\pm$” given in [EtTh], Definition 2.5, (i).

Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters* (May 2020), Definition 3.1(e), sentence beginning “Finally” on printed page 63, through the displayed natural models; printed/PDF page(s) 63. Official original: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20I.pdf.

> Finally, we observe that when $\underline v\in\underline{\mathbb V}^{\mathrm{bad}}$, it follows from the theory of [EtTh], §2 — i.e., roughly speaking, “by extracting an $l$-th root of the theta function” — that $\underline X_{\underline v}$, $\underline C_{\underline v}$ admit natural models $\underline{\underline X}_{\underline v}$, $\underline{\underline C}_{\underline v}$ […]

**Actual consumer.** The accepted original graph uses InitialThetaData in Corollary312VariantData.data. The selected ℓ helper reads its supplied prime. This bundle includes no other InitialThetaData helper definition.
