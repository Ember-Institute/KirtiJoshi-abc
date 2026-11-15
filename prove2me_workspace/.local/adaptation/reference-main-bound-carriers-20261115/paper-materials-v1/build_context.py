from pathlib import Path
import json, hashlib, re
BASE=Path('/home/admin-wsl/Coq/abc')
SRC=BASE/'prove2me_workspace/.local/adaptation/reference-main-bound-carriers-20261115'
OUT=Path(__file__).resolve().parent
E=OUT/'evidence'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text())
def dump(p,d):Path(p).write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
selection=load(SRC/'source-only-small-metadata/selected-command-map.json')
small=load(SRC/'source-only-small-metadata/small-source-metadata.json')
provenance=load(SRC/'source-provenance-audit.json')
inventory=load(SRC/'inventory.json')
q=[]
def quote(id,paper,pages,locator,text,scope='Complete sentence(s) at the cited location.'):
 q.append(dict(id=id,paper_id=paper,locator=locator,printed_pages=pages,file_pages=pages,quote_markdown=text,quote_scope=scope,transcription_status='Manually transcribed and visually checked against rendered original PDF pages in this task.',typography_note='Typeset line breaks and line-end hyphenation are joined. Mathematical symbols use KaTeX. Editorial omissions use […]. Underlines on paper objects are retained where present.',evidence=[dict(paper_id=paper,printed_page=p,file_page=p,page_image_path=str(E/f'{paper}-{p:03}.png'),page_image_sha256=sha(E/f'{paper}-{p:03}.png'),raw_text_path=str(E/f'{paper}-{p:03}.raw.txt'),raw_text_sha256=sha(E/f'{paper}-{p:03}.raw.txt')) for p in pages]))
quote('I-local-q-root','I',[71],'§3, Example 3.2(iv), opening sentence and sentence beginning “Note that”',r'''Write $q_{\underline v}$ for the $q$-parameter of the elliptic curve $E_{\underline v}$ over $K_{\underline v}$. […] Note that it follows from our assumption concerning $2$-torsion [cf. Definition 3.1, (b)], together with the definition of “$K$” [cf. Definition 3.1, (c)], that $q_{\underline v}$ admits a $2l$-th root […].''','The opening sentence and the next-but-one sentence, with the intervening sentence and the ambient monoid after “root” explicitly omitted. The root-value formula below them is outside this excerpt.')
quote('III-theta-volume','III',[173,174],'§3, Corollary 3.12, opening through the definition of the theta-pilot log-volume',r'''Suppose that we are in the situation of Theorem 3.11. Write

$$-\lvert\log(\underline{\underline\Theta})\rvert\in\mathbb R\cup\{+\infty\}$$

for the procession-normalized mono-analytic log-volume [i.e., where the average is taken over $j\in\mathbb F_l^{\circledast}$ — cf. Remark 3.1.1, (ii), (iii), (iv); Proposition 3.9, (i), (ii); Theorem 3.11, (i), (a)] of the holomorphic hull [cf. Remark 3.9.5, (i)] of the union of the possible images of a $\Theta$-pilot object [cf. Definition 3.8, (i)], relative to the relevant Kummer isomorphisms [cf. Theorem 3.11, (ii)], in the multiradial representation of Theorem 3.11, (i), which we regard as subject to the indeterminacies (Ind1), (Ind2), (Ind3) described in Theorem 3.11, (i), (ii).''')
quote('III-q-volume','III',[174],'§3, Corollary 3.12, sentence beginning “Write” after the theta-pilot definition',r'''Write

$$-\lvert\log(\underline{\underline q})\rvert\in\mathbb R$$

for the procession-normalized mono-analytic log-volume of the image of a $q$-pilot object [cf. Definition 3.8, (i)], relative to the relevant Kummer isomorphisms [cf. Theorem 3.11, (ii)], in the multiradial representation of Theorem 3.11, (i), which we do not regard as subject to the indeterminacies (Ind1), (Ind2), (Ind3) described in Theorem 3.11, (i), (ii).''')
quote('III-volume-inequality','III',[174],'§3, Corollary 3.12, final two sentences',r'''In particular, $\lvert\log(\underline{\underline q})\rvert>0$ is easily computed in terms of the various $q$-parameters of the elliptic curve $E_F$ [cf. [IUTchI], Definition 3.1, (b)] at $\underline v\in\underline{\mathbb V}^{\mathrm{bad}}\ (\ne\emptyset)$. Then it holds that $-\lvert\log(\underline{\underline\Theta})\rvert\in\mathbb R$, and

$$-\lvert\log(\underline{\underline\Theta})\rvert\geq-\lvert\log(\underline{\underline q})\rvert$$

— i.e., $C_{\Theta}\geq-1$ for any real number $C_{\Theta}\in\mathbb R$ such that $-\lvert\log(\underline{\underline\Theta})\rvert\leq C_{\Theta}\cdot\lvert\log(\underline{\underline q})\rvert$.''')
quote('IV-global-degree','IV',[21,22],'§1, Definition 1.9(i), sentence defining normalized degree and pullback equality',r'''If $\mathfrak a\in\operatorname{ADiv}_{\mathbb R}(F)$, then we shall refer to

$$\underline{\deg}(\mathfrak a)\overset{\mathrm{def}}{=}\frac{1}{[F:\mathbb Q]}\cdot\deg_F(\mathfrak a)$$

as the normalized degree of $\mathfrak a$. Thus, for any finite extension $K$ of $F$, we have

$$\underline{\deg}(\mathfrak a|_K)=\underline{\deg}(\mathfrak a)$$

— where we write $\underline{\deg}(\mathfrak a|_K)$ for the normalized degree of the pull-back $\mathfrak a|_K\in\operatorname{ADiv}_{\mathbb R}(K)$ [defined in the evident fashion] of $\mathfrak a$ to $K$.''')
quote('IV-fiber-degree','IV',[22],'§1, Definition 1.9(ii), opening through the definition of normalized E-degree',r'''Let $v_{\mathbb Q}\in\mathbb V_{\mathbb Q}\overset{\mathrm{def}}{=}\mathbb V(\mathbb Q)$, $E\subseteq\mathbb V(F)$ a nonempty set of elements lying over $v_{\mathbb Q}$. If $\mathfrak a=\sum_{v\in\mathbb V(F)}c_v\cdot v\in\operatorname{ADiv}_{\mathbb R}(F)$, then we shall write

$$\mathfrak a_E\overset{\mathrm{def}}{=}\sum_{v\in E}c_v\cdot v\in\operatorname{ADiv}_{\mathbb R}(F);\qquad\underline{\deg}_E(\mathfrak a)\overset{\mathrm{def}}{=}\frac{\deg(\mathfrak a_E)}{\sum_{v\in E}[F_v:\mathbb Q_{v_{\mathbb Q}}]}$$

for the portion of $\mathfrak a$ supported in $E$ and the “normalized $E$-degree” of $\mathfrak a$, respectively.''')
q[-1]['symbol_transcription']=['The numerator is printed as plain deg(a_E), without an underline or an F subscript. This excerpt retains that typography. The denominator is the sum of local degrees over E.']
quote('IV-q-normalization','IV',[23],'§1, Theorem 1.10 statement, sentence beginning “Here, we observe”',r'''Here, we observe that the various “$\log(q_{(-)})$”’s are independent of the choice of $F_{\square}$, and that the quantity “$\lvert\log(\underline{\underline q})\rvert\in\mathbb R_{>0}$” defined in [IUTchIII], Corollary 3.12, is equal to $\frac{1}{2l}\cdot\log(q)\in\mathbb R$ [cf. the definition of “$\underline q_{\underline v}$” in [IUTchI], Example 3.2, (iv)].''')
quote('IV-prime-counting','IV',[16],'§1, Proposition 1.6, final sentence',r'''In particular, there exists a positive real number $\eta_{\mathrm{prm}}$ such that

$$\sum_{p\leq\eta}1\leq\frac{4\eta}{3\cdot\log(\eta)}$$

— where the sum ranges over the prime numbers $p\leq\eta$ — for all positive real $\eta\geq\eta_{\mathrm{prm}}$.''')
quote('IV-invariants','IV',[22],'§1, Theorem 1.10, opening through the definition of the tripodal field',r'''Fix a collection of initial $\Theta$-data as in [IUTchI], Definition 3.1. Suppose that we are in the situation of [IUTchIII], Corollary 3.12, and that the elliptic curve $E_F$ has good reduction at every valuation $\in\mathbb V(F)^{\mathrm{good}}\cap\mathbb V(F)^{\mathrm{non}}$ that does not divide $2l$. In the notation of [IUTchI], Definition 3.1, let us write $d_{\mathrm{mod}}\overset{\mathrm{def}}{=}[F_{\mathrm{mod}}:\mathbb Q]$, $(1\leq)\ e_{\mathrm{mod}}\ (\leq d_{\mathrm{mod}})$ for the maximal ramification index of $F_{\mathrm{mod}}$ [i.e., of valuations $\in\mathbb V_{\mathrm{mod}}^{\mathrm{non}}$] over $\mathbb Q$, $d_{\mathrm{mod}}^*\overset{\mathrm{def}}{=}2^{12}\cdot3^3\cdot5\cdot d_{\mathrm{mod}}$, $e_{\mathrm{mod}}^*\overset{\mathrm{def}}{=}2^{12}\cdot3^3\cdot5\cdot e_{\mathrm{mod}}\ (\leq d_{\mathrm{mod}}^*)$, and

$$F_{\mathrm{mod}}\subseteq F_{\mathrm{tpd}}\overset{\mathrm{def}}{=}F_{\mathrm{mod}}(E_{F_{\mathrm{mod}}}[2])\subseteq F$$

for the “tripodal” intermediate field obtained from $F_{\mathrm{mod}}$ by adjoining the fields of definition of the $2$-torsion points of any model of $E_F\times_F\overline F$ over $F_{\mathrm{mod}}$ [cf. Proposition 1.8, (ii), (iii)].''','The opening of the theorem. The further (3·5)-torsion and field-generation hypotheses follow on the same page and are outside this excerpt. They remain part of the paper theorem.')
quote('IV-distinguished','IV',[24],'§1, proof of Theorem 1.10, Step (iii), first sentence',r'''If $F_{\mathrm{tpd}}\subseteq F_{\square}\subseteq K$ is any intermediate extension which is Galois over $F_{\mathrm{mod}}$, then we shall write

$$\mathbb V(F_{\square})^{\mathrm{dst}}\subseteq\mathbb V(F_{\square})^{\mathrm{non}}$$

for the set of “distinguished” nonarchimedean valuations $v\in\mathbb V(F_{\square})^{\mathrm{non}}$, i.e., $v$ that extend to a valuation $\in\mathbb V(K)^{\mathrm{non}}$ that ramifies over $\mathbb Q$.''')
quote('IV-indicator','IV',[25],'§1, proof of Theorem 1.10, Step (iii), clause defining iota after the s-divisors',r'''we set $\iota_{w_{\mathbb Q}}\overset{\mathrm{def}}{=}1$ if $p_{w_{\mathbb Q}}\leq e_{\mathrm{mod}}^*\cdot l$, $\iota_{w_{\mathbb Q}}\overset{\mathrm{def}}{=}0$ if $p_{w_{\mathbb Q}}>e_{\mathrm{mod}}^*\cdot l$.''','A complete clause after a semicolon. The preceding clause fixes the fiber notation; its omission is identified here.')
quote('IV-certificate-ii','IV',[24],'§1, proof of Theorem 1.10, Step (ii), displayed chain bounding the different of K',r'''$$\log(\mathfrak d^K)\leq\log(\mathfrak d^K)+\log(\mathfrak f^K)\leq\log(\mathfrak d^F)+\log(\mathfrak f^F)+2\cdot\log(l)$$
$$\leq\log(\mathfrak d^{F_{\mathrm{tpd}}})+\log(\mathfrak f^{F_{\mathrm{tpd}}})+2\cdot\log(l)+21$$''','A displayed inequality, not the surrounding proof paragraph. The preceding text invokes tame ramification and the Galois-group inclusion; the following text invokes Proposition 1.3(i),(ii).')
quote('IV-certificate-iii','IV',[26],'§1, proof of Theorem 1.10, Step (iii), sentence beginning “In a similar vein”',r'''In a similar vein, we conclude that

$$\log(s^{\mathbb Q})\leq2\cdot d_{\mathrm{mod}}\cdot(\log(\mathfrak d^{F_{\mathrm{tpd}}})+\log(\mathfrak f^{F_{\mathrm{tpd}}}))+\log(2\cdot3\cdot5\cdot l)$$
$$\leq2\cdot d_{\mathrm{mod}}\cdot(\log(\mathfrak d^{F_{\mathrm{tpd}}})+\log(\mathfrak f^{F_{\mathrm{tpd}}}))+5+\log(l)$$

and hence that […]''','Opening of a sentence through its first displayed chain; the next display is explicitly omitted.')
quote('IV-normalized-weights','IV',[18],'§1, Remark 1.7.1, paragraph beginning “Thus, in summary”',r'''Thus, in summary, when one works with normalized log-volumes as in Proposition 1.4, (i), the appropriate normalized weights are given by the expressions

$$\frac{\lambda_{\Pi\vec e^{\dagger}}}{\sum_{\vec e\in E^n}\lambda_{\Pi\vec e}}$$

[where $\vec e^{\dagger}\in E^n$] that appear in Proposition 1.7. Here, one takes “$E$” to be the set of elements of $\underline{\mathbb V}\xrightarrow{\sim}\mathbb V_{\mathrm{mod}}$ lying over a fixed $v_{\mathbb Q}$; one takes “$n$” to be the cardinality of $A$, so that one can write $A=\{\alpha_1,\ldots,\alpha_n\}$ [where the $\alpha_i$ are distinct]; if $e\in E$ corresponds to $\underline v\in\underline{\mathbb V}$, $v\in\mathbb V_{\mathrm{mod}}$, then one takes

$$\text{“}\lambda_e\text{”}\overset{\mathrm{def}}{=}[(F_{\mathrm{mod}})_v:\mathbb Q_{v_{\mathbb Q}}]\in\mathbb R_{>0}$$

and “$\beta_e$” to be a normalized log-volume of some compact open subset of $K_{\underline v}$.''')
quote('IV-local-objective','IV',[26],'§1, proof of Theorem 1.10, Step (iv), opening sentence',r'''In order to estimate the constant “$C_{\Theta}$” of [IUTchIII], Corollary 3.12, we must, according to the various definitions given in the statement of [IUTchIII], Corollary 3.12, compute an upper bound for the

procession-normalized mono-analytic log-volume of the holomorphic hull of the union of the possible images of a $\Theta$-pilot object, relative to the relevant Kummer isomorphisms [cf. [IUTchIII], Theorem 3.11, (ii)], in the multiradial representation of [IUTchIII], Theorem 3.11, (i), which we regard as subject to the indeterminacies (Ind1), (Ind2), (Ind3) described in [IUTchIII], Theorem 3.11, (i), (ii).''')
quote('IV-capsule-bound','IV',[28],'§1, proof of Theorem 1.10, Step (v), final sentences and display',r'''Here, we note that it follows immediately from the first equality of the first display of Proposition 1.7 that, after passing to weighted averages, the operation of symmetrizing with respect to the choice of “$i^{\dagger}\in I$” in $S_{j+1}^{\pm}$ does not affect the computation of the upper bound under consideration. Thus, by applying Proposition 1.7, we obtain that the resulting “weighted average upper bound” is given by

$$(j+1)\cdot\log(\mathfrak d^K_{v_{\mathbb Q}})-\frac{j^2}{2l}\cdot\log(q_{v_{\mathbb Q}})+\log(s^{\mathbb Q}_{v_{\mathbb Q}})+4(j+1)\cdot l_{\mathrm{mod}}^*\cdot\log(s^{\leq}_{v_{\mathbb Q}})$$''','Two sentences through the displayed bound. The continuation on page 29 recalls the notation of Step (iii).')
quote('IV-zero-bound','IV',[29],'§1, proof of Theorem 1.10, Step (vi), final two sentences',r'''One may then compute a “weighted average upper bound” and then a “procession-normalized upper bound”, as was done in Step (v). The resulting “procession-normalized upper bound” is clearly equal to $0$.''')
quote('IV-infinite-bound','IV',[30],'§1, proof of Theorem 1.10, Step (vii), sentences giving the archimedean bound',r'''Thus, an upper bound on the component of the log-volume under consideration may be obtained by computing an upper bound for the log-volume of this container. Such an upper bound

$$(j+1)\cdot\log(\pi)$$

follows immediately from the fact that [in order to ensure compatibility with arithmetic degrees of arithmetic line bundles — cf. [IUTchIII], Proposition 3.9, (iii) — one is obliged to adopt normalizations which imply that] the log-volume of $B_I$ is equal to $0$.''')

papers={}
for ident,title,date in [('I','Construction of Hodge Theaters','May 2020'),('III','Canonical Splittings of the Log-theta-lattice','May 2020'),('IV','Log-volume Computations and Set-theoretic Foundations','April 2020')]:
 pdf=BASE/'refer/Mochizuki'/f'Inter-universal Teichmuller Theory {ident}.pdf'
 papers[ident]=dict(author='Shinichi Mochizuki',title=f'Inter-universal Teichmüller Theory {ident}: {title}',version=date,official_url='https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20'+ident+'.pdf',local_pdf=str(pdf),sha256=sha(pdf),retrieved_date='Existing local original; this task made no download. Acquisition date not independently established here.',file_page_numbering='All cited PDF file pages were rendered and display the same printed page number.',version_evidence=dict(page_image_path=str(E/f'{ident}-001.png'),page_image_sha256=sha(E/f'{ident}-001.png'),raw_text_path=str(E/f'{ident}-001.raw.txt'),raw_text_sha256=sha(E/f'{ident}-001.raw.txt')))

normalizations=[
 dict(id='source-positive-weights',scope='QPilotData',statement_en='The source requires positive weights on its finite bad locus. It requires neither a total weight of one nor local-degree formulas.',source_fact='weight_pos : ∀ w ∈ badFinset, 0 < weight w',paper_relation='Arithmetic degree is the intended interpretation. That interpretation is not a law of this record.'),
 dict(id='paper-fiber-weights',scope='IUT IV, Remark 1.7.1; Proposition 1.7',statement_en='The paper fixes one rational place and normalizes products of positive local degrees by their sum over all tuples.',formula=r'w_{\vec e}=\frac{\prod_{i=1}^n\lambda_{e_i}}{\sum_{\vec f\in E^n}\prod_{i=1}^n\lambda_{f_i}},\quad\sum_{\vec e\in E^n}w_{\vec e}=1',formula_status='The sum-to-one equation is an editorial algebraic consequence of the displayed paper weights, not an additional verbatim quotation.',quotation_ids=['IV-normalized-weights'],paper_relation='These are fixed-fiber packet weights. They are not supplied or derived by QPilotData.weight_pos.'),
 dict(id='global-degree',scope='IUT IV, Definition 1.9(i)',statement_en='Global normalized degree divides the arithmetic degree by [F : Q].',quotation_ids=['IV-global-degree'],paper_relation='A positive arbitrary QPilotData.weight does not establish this global arithmetic identity.'),
 dict(id='fiber-degree',scope='IUT IV, Definition 1.9(ii)',statement_en='Normalized E-degree uses the sum of local degrees over a fixed nonempty fiber E. This denominator differs from the global denominator.',quotation_ids=['IV-fiber-degree'],paper_relation='logQAt groups source summands by residue characteristic. No selected command proves a conversion to the paper normalized fiber degree.'),
 dict(id='q-root-normalization',scope='IUT I, Example 3.2(iv); IUT IV, Theorem 1.10 statement',statement_en='The paper distinguishes a local q-parameter from its 2l-th root. IUT IV relates the positive q-pilot quantity to log(q)/(2l).',quotation_ids=['I-local-q-root','IV-q-normalization'],paper_relation='The source defines absLogQ as logQ/(2ℓ). The name absLogQ does not apply the real absolute-value function.'),
 dict(id='negative-q-side',scope='IUT III, Corollary 3.12; QPilotData.lhs',statement_en='The q-side is negative: lhs = -logQ/(2ℓ). The theta-side is already the log-volume denoted -|log(Theta)|.',quotation_ids=['III-q-volume','III-volume-inequality'],paper_relation='RHSData.rhs takes the procession volume directly. It does not add another minus sign.'),
 dict(id='half-order',scope='Corollary312VariantData.lstar; IUT IV, proof of Theorem 1.10, Steps (iv)–(v)',statement_en='The half-order ℓ* = (ℓ-1)/2 counts procession stages. It is distinct from the q-root denominator 2ℓ.',paper_relation='The source uses natural-number subtraction and division. RHSData.proc_standard supplies the standard procession law; it is an input field.'),
 dict(id='local-capsule-size',scope='IUT IV, proof of Theorem 1.10, Step (v)',statement_en='The paper uses n = j+1 for capsule size. The source coefficient ((n:ℝ)-1)^2/(2ℓ) follows this indexing.',quotation_ids=['IV-capsule-bound'],paper_relation='This matching formula does not prove local field estimates, identify arbitrary packet volumes, or establish the fiber normalization bridge.'),
 dict(id='prime-bound-factor',scope='PrimeCountingBound; IUT IV, Proposition 1.6',statement_en='The paper uses 4/3. The source certificate uses 3/2 and requires a threshold greater than one.',quotation_ids=['IV-prime-counting'],paper_relation='The selected command defines a certificate. It does not construct a prime-counting proof or establish that this change suffices downstream.')]

# Per-command entries describe use of the paper background, rather than an independent formal readback.
entries={
'Iut.QPilotData':('Supplies finite bad-place data for the intended arithmetic q-degree. The paper q-pilot object itself is not constructed.',['I-local-q-root','IV-global-degree','IV-q-normalization']),
'Iut.QPilotData.mem_bad':('A local bookkeeping lemma connects finite enumeration to the chosen bad locus. It has no separate verbatim paper counterpart.',['I-local-q-root']),
'Iut.QPilotData.logQ':('The intended arithmetic background is the globally normalized degree of the q-divisor. Arbitrary positive source weights do not establish this identification.',['IV-global-degree','IV-q-normalization']),
'Iut.QPilotData.absLogQ':('Uses the factor 1/(2ℓ) stated in IUT IV. Its name records a paper quantity, not an application of real absolute value.',['IV-q-normalization']),
'Iut.QPilotData.lhs':('Uses the negative q-pilot side of the comparison. The minus sign is essential.',['III-q-volume','III-volume-inequality']),
'Iut.RHSData':('Organizes the paper sequence: possible theta-pilot images, holomorphic hull, and procession-normalized volume. Regions, containments, admissibility, and compatibility remain supplied fields.',['III-theta-volume','IV-local-objective','IV-normalized-weights']),
'Iut.RHSData.thetaHull':('Applies the supplied hull operation to the supplied regions. It does not construct the multiradial representation or its images.',['III-theta-volume']),
'Iut.RHSData.rhs':('Uses procession-normalized volume as the theta-side. The paper initially permits +∞, then asserts finiteness; the source interface returns a real value.',['III-theta-volume','III-volume-inequality']),
'Iut.Corollary312VariantData':('Collects the local implementation inputs for the comparison. This record does not establish that those inputs realize the paper objects.',['III-theta-volume','III-q-volume']),
'Iut.Corollary312Variant':('Defines the local comparison with the paper direction: negative q-side ≤ theta-side. The command defines a proposition and supplies no proof.',['III-volume-inequality']),
'Iut.PrimeCountingBound':('Uses the prime-counting estimate as a supplied certificate, with 3/2 in place of the paper factor 4/3.',['IV-prime-counting']),
'Iut.Theorem110Invariants':('Carries numbers intended to represent ramification, different, conductor, and distinguished-prime data. It does not construct these arithmetic objects.',['IV-invariants','IV-distinguished','IV-global-degree']),
'Iut.Corollary312VariantData.ℓ':('Names the prime from the supplied initial theta-data. It does not supply additional paper hypotheses.',['IV-invariants']),
'Iut.Corollary312VariantData.lstar':('Names the half-order (ℓ-1)/2 used for procession stages. This is separate from 1/(2ℓ).',['IV-capsule-bound']),
'Iut.Corollary312VariantData.dmod':('Takes the degree of the supplied field of moduli. Its intended paper notation is d_mod.',['IV-invariants']),
'Iut.Corollary312VariantData.logQAt':('Groups the source logQ summands by residue characteristic. No selected theorem identifies this contribution with the paper normalized fiber quantity log(q_vQ).',['IV-fiber-degree','IV-q-normalization','IV-capsule-bound']),
'Iut.Theorem110Invariants.eStar':('Uses the paper factor 2^12·3^3·5 = 552960 on the supplied ramification bound.',['IV-invariants']),
'Iut.Theorem110Invariants.lmod':('Names log(eStar·ℓ), the l_mod* used in the local estimates. Its arithmetic meaning depends on the supplied invariant data.',['IV-capsule-bound','IV-indicator']),
'Iut.Theorem110Invariants.ι':('Records the cutoff at e_mod*·ℓ used in Step (iii). The value is 1 at and below the cutoff.',['IV-indicator']),
'Iut.Theorem110Invariants.logSQ':('Sums log p over the supplied distinguished primes, following the rational s-divisor in Step (iii). It does not prove that dst is the ramification locus.',['IV-distinguished','IV-certificate-iii']),
'Iut.Theorem110Invariants.logSle':('Counts supplied distinguished primes at and below the cutoff through the indicator sum. The arithmetic interpretation follows Step (iii).',['IV-indicator']),
'Iut.Theorem110Invariants.logDKtot':('Sums supplied different contributions over dst. It does not compute a different ideal or its arithmetic degree.',['IV-global-degree','IV-certificate-ii']),
'Iut.Theorem110Certificate':('Carries ℓ≥7, coverage of bad places, and the Step (ii) and Step (iii) bounds as explicit hypotheses. It proves none of them.',['IV-invariants','IV-certificate-ii','IV-certificate-iii']),
'Iut.Theorem110Invariants.capsuleBound':('Follows the Step (v) formula with capsule size n=j+1. Identification of source logQAt with paper fiber degree remains open.',['IV-capsule-bound','IV-normalized-weights','IV-fiber-degree']),
'Iut.Theorem110Invariants.LocalEstimate':('Carries local containing regions, local volume bounds, and monotonicity as supplied fields. It does not derive the local-field estimates of Propositions 1.4 and 1.5.',['IV-local-objective','IV-capsule-bound','IV-zero-bound','IV-infinite-bound']),
'Iut.Theorem110Invariants.LocalEstimate.placeBound':('Collects the three cases: distinguished finite bound, zero at other finite places, and n·log π at infinity. These numerical cases follow Steps (v)–(vii).',['IV-capsule-bound','IV-zero-bound','IV-infinite-bound']),
'Iut.Theorem110Invariants.LocalEstimate.dstPlaces':('Converts the supplied finite set of distinguished primes into rational places for later finite summation. This is local implementation bookkeeping.',['IV-distinguished'])}

bundle_text={
'Iut.Cor312.LeftHandSide':(
'Mochizuki distinguishes local Tate q-parameters from the global q-pilot object. IUT IV expresses the positive q-pilot quantity as log(q)/(2l). The comparison uses its negative. Global arithmetic degree and local fiber degree use different denominators.',
'This bundle computes the q-side from supplied finite bad-place data and positive weights. It does not construct a q-pilot object. No selected command fixes the weights to local degrees, requires their sum to be one, or proves the arithmetic identity of logQ.',
'QPilotData and its numerical definitions feed Corollary312VariantData, the comparison definition, and later logQ decomposition.',
['I-local-q-root','IV-global-degree','IV-fiber-degree','IV-q-normalization','III-q-volume']),
'Iut.Cor312.RightHandSide':(
'Corollary 3.12 starts with the union of possible theta-pilot images under three indeterminacies. It takes a holomorphic hull and its procession-normalized mono-analytic log-volume. The paper defines this value in R ∪ {+∞} before asserting finiteness.',
'The source supplies the regions, their hull-admissibility, containment in log-shells, and compatibility with the standard procession. The selected commands apply the supplied hull and volume operations. They do not construct the paper multiradial representation. The source returns a real number under its interface assumptions.',
'RHSData and rhs feed the assembled comparison and the later LocalEstimate upper-bound argument.',
['III-theta-volume','III-volume-inequality','IV-local-objective','IV-normalized-weights']),
'Iut.Cor312.Statement':(
'Mochizuki’s Corollary 3.12 compares the theta-side with the negative positive q-pilot quantity. Its inequality is -|log(Theta)| ≥ -|log(q)|. The statement also asserts finiteness and derives a lower bound on every upper-bound coefficient C_Theta.',
'The source collects supplied inputs and defines lhs ≤ rhs as a proposition. It supplies no proof of this proposition. The source variant does not establish correspondence with the paper construction or reproduce all paper hypotheses. The unselected corollary312Variant_iff is outside this 27-command packet.',
'The assembled data and proposition serve later implication theorems. Their names do not provide a proof of the paper Corollary 3.12.',
['III-theta-volume','III-q-volume','III-volume-inequality','IV-q-normalization']),
'Iut.Implication.Invariants':(
'IUT IV turns the theta-pilot estimate into explicit arithmetic bounds. Theorem 1.10 uses the field-of-moduli degree, maximal ramification, a tripodal field, different and conductor degrees. Steps (ii) and (iii) bound these quantities and introduce distinguished primes. Proposition 1.6 supplies prime-counting control.',
'The source derives dmod from its field of moduli and groups logQ summands as logQAt. Other arithmetic quantities and certificate bounds remain supplied data or hypotheses. PrimeCountingBound uses 3/2, while the paper uses 4/3. The selected bundle constructs no tripodal field, different ideal, ramification locus, prime-counting witness, or Theorem110Certificate witness.',
'The supplied invariants and certificate feed the later local estimates and theorem110 argument. The selected definitions lstar and logSle have later numerical consumers.',
['IV-invariants','IV-global-degree','IV-fiber-degree','IV-prime-counting','IV-distinguished','IV-indicator','IV-certificate-ii','IV-certificate-iii']),
'Iut.Implication.LogVolumeBound':(
'The proof of IUT IV, Theorem 1.10, estimates one rational place and one capsule at a time. Step (v) gives a weighted finite-place bound. Steps (vi) and (vii) give zero away from distinguished primes and (j+1)·log π at infinity. The proof then averages over the half-order procession.',
'The selected commands define capsuleBound, LocalEstimate, placeBound, and dstPlaces. Local containments, finite and infinite volume estimates, and monotonicity remain fields of LocalEstimate. This packet does not include rhs_le or its proof lemmas. A formula match alone does not identify source packet volumes or grouped q-contributions with the paper quantities.',
'These four commands serve the remaining source proof chain ending in LocalEstimate.rhs_le and the later theorem110 argument. Their source consumers are recorded per command.',
['IV-local-objective','IV-normalized-weights','IV-fiber-degree','IV-capsule-bound','IV-zero-bound','IV-infinite-bound'])}

bundles=[]
for mod in small['modules']:
 name=mod['module']; src=Path(mod['source']);data=src.read_bytes(); prov=next(x for x in provenance['sources'] if x['module']==name)
 assert sha(src)==mod['sourceSha256']==prov['effectiveSourceSha256']
 context,scope,consumer,qids=bundle_text[name]
 bindings=[]
 for c in selection['commands']:
  if c['module']!=name:continue
  root=c['rootOriginalName'];r=c['actualParserRange'];sl=data[r['start']['offset']:r['end']['offset']];assert hashlib.sha256(sl).hexdigest()==c['wholeCommandSha256']
  note,ids=entries[root]
  binding=dict(name=root,parser_command_index=c['commandIndex'],syntax_kind=c['commandKind'],actual_parser_range=r,source_text=sl.decode(),source_text_sha256=c['wholeCommandSha256'],source_byte_length=len(sl),source_name_expr=c['rootActualSourceNameExpr'],paper_relation_en=note,quotation_ids=ids,actual_consumers=c['actualConsumers'],selected_compiler_declarations=c['selectedRangedDeclarations'],scope_at_command=c['scopeAtCommand'],target_identity=c['targetIdentity'],target_identity_status=c['targetIdentityStatus'])
  fields=re.findall(r'^  ([\w]+)\s*:',re.sub(r'/\*.*?\*/|/-.*?-/', '', sl.decode(), flags=re.S),re.M) if re.search(r'^structure ',sl.decode(),re.M) else []
  if fields:binding['complete_structure_fields']=fields
  candidate=next(x for m in inventory['modules'] if m['module']==name for x in m['sourceCommandCandidates'] if x['name']==root)
  binding['consumer_paths']={k:candidate[k] for k in ['pathToTheorem110','pathToC2'] if k in candidate}
  bindings.append(binding)
 b=dict(module=name,source_path=str(src),source_sha256=sha(src),source_provenance=prov,selected_source_commands=[x['name'] for x in bindings],selected_command_bindings=bindings,structure_fields={x['name']:x['complete_structure_fields'] for x in bindings if 'complete_structure_fields' in x},source_context_en=context,implementation_scope_en=scope,consumer_scope_en=consumer,quotation_ids=qids,attribution_status='Original Mochizuki paper background. Source descriptions and missing bridges are editorial. This packet is not an independent code-only readback.',blocks_definition_delivery=False)
 def citation(q):
  p=papers[q['paper_id']];return f"Shinichi Mochizuki, *{p['title']}* ({p['version']}), {q['locator']}; printed page(s) {', '.join(map(str,q['printed_pages']))}; PDF file page(s) {', '.join(map(str,q['file_pages']))}. Official original: {p['official_url']}."
 b['publication_markdown']='**Paper source context.** '+context+'\n\n**Selected source interface and limits.** '+scope+'\n\n'+ '\n\n'.join(citation(x)+'\n\n> '+x['quote_markdown'].replace('\n','\n> ') for x in q if x['id'] in qids)+'\n\n**Actual consumer.** '+consumer
 bundles.append(b)

packet=dict(schema='prove2me-reference-main-bound-paper-context-v1',language='en',purpose='Original Mochizuki paper background for exactly five bundles and 27 complete parser-selected source commands. This is author/source context, not a formal type readback or independent blind audit.',created_date='2026-11-15',author_model='The task requested gpt-6.1-sol. This subagent does not have an independent runtime model receipt.',selection_inventory=str(SRC/'inventory.json'),selection_inventory_sha256=sha(SRC/'inventory.json'),selection_status='27 full source commands, grouped 5/3/2/13/4. Their 173 selected original compiler declarations include generated support items. No new compilation, adapted kernel acceptance, paper identity, or platform acceptance is asserted.',parser_selection_evidence=dict(path=str(SRC/'source-only-small-metadata/selected-command-map.json'),sha256=sha(SRC/'source-only-small-metadata/selected-command-map.json'),parser_job_id=selection['parserJobId'],expr_job_id=selection['exprJobId'],source_command_count=27,selected_compiler_declaration_count=173),input_evidence=[dict(path=str(p),sha256=sha(p)) for p in [SRC/'inventory.json',SRC/'source-provenance-audit.json',SRC/'source-only-small-metadata/selected-command-map.json',SRC/'source-only-small-metadata/small-source-metadata.json',SRC/'source-only-small-metadata/remaining-lemma-consumers.json',BASE/'docs/三语自然语言读回原则.md',BASE/'prove2me_workspace/.local/adaptation/reference-initial-theta-carriers-20261115/paper-context.json']],paper_sources=papers,quotations=q,bundles=bundles,normalization_distinctions=normalizations,evidence_policy=dict(visual_check_date='2026-11-15',new_original_pages_visually_checked=['I-001','I-071','III-001','III-173','III-174','IV-001','IV-016','IV-017','IV-018','IV-021','IV-022','IV-023','IV-024','IV-025','IV-026','IV-027','IV-028','IV-029','IV-030'],rendering='Ghostscript png16m at 95 dpi and txtwrite. IV-022-detail.png at 150 dpi resolves the exact normalized E-degree numerator. No proof compiler.',raw_text_is_search_evidence_only=True,quote_policy='Only original Mochizuki passages appear in quotations. KaTeX transcribes visible mathematics. Omissions are explicit. No secondary author supplies mathematical evidence.',no_network_requests=True),platform_field_guidance=dict(natural_language_statement='Use bundle.publication_markdown as English author/source context after the independent readback is frozen. Keep normalization distinctions and open bridges with that context.',readback='Do not use this packet as independent readback or place its source context in a blind audit.',readback_model='Use the actual independent auditor model; this packet is not that audit.'),no_main_or_external_mutations=True,preparation_state='Draft files written only under /tmp/p2m-main-bound-paper-context-v6-20261115. No compiler, MCP-CI call, network request, API submission, or Git operation.',validation={'status':'pending offline validation'})
dump(OUT/'paper-context.json',packet)
dump(OUT/'quotations-and-evidence.json',dict(paper_sources=papers,quotations=q,evidence_policy=packet['evidence_policy']))
lines=['# Paper source context: main-bound carriers','',packet['purpose'],'',packet['selection_status'],'','## Normalization distinctions','']
for n in normalizations:
 lines += [f"**{n['id']}.** {n['statement_en']}",'',('$$'+n['formula']+'$$') if 'formula' in n else '','',n.get('formula_status',''),'',n['paper_relation'],'']
for b in bundles:
 lines += [f"## {b['module']}",'',b['publication_markdown'],'','**Exact selected command coverage.**','']
 for c in b['selected_command_bindings']:
  r=c['actual_parser_range'];lines += [f"- `{c['name']}` (source lines {r['start']['line']}–{r['end']['line']}, parser command {c['parser_command_index']}): {c['paper_relation_en']}"]
 lines += ['','**All fields of selected structure commands.**','']
 for name,fields in b['structure_fields'].items():lines += [f"- `{name}`: "+', '.join('`'+f+'`' for f in fields)+'.']
 lines += ['','Source bytes, exact parser ranges, source provenance, actual consumers, and quotation references are stored in `paper-context.json`.','']
lines+=['## Use and proof status','',packet['platform_field_guidance']['natural_language_statement'],'',packet['platform_field_guidance']['readback'],'','This packet does not prove Corollary 3.12, Theorem 1.10, ABC, local arithmetic certificates, or correspondence between arbitrary source interfaces and paper objects.','',packet['preparation_state'],'']
(OUT/'PAPER-CONTEXT.en.md').write_text('\n'.join(lines))
(OUT/'quotations.en.md').write_text('\n\n'.join('## '+x['id']+'\n\n'+citation(x)+'\n\n> '+x['quote_markdown'].replace('\n','\n> ')+'\n\nScope: '+x['quote_scope'] for x in q)+'\n')
print('Wrote',len(bundles),'bundles',sum(len(b['selected_source_commands']) for b in bundles),'commands',len(q),'quotes')
