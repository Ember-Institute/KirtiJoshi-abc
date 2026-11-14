Original-source quotations for the Legendre height comparison. All quoted English below is from the original PDFs, checked against rendered pages. Mathematical notation is transcribed into KaTeX. Printed and one-based PDF page numbers coincide.

**Source iut4.** Shinichi Mochizuki, *Inter-universal Teichmüller Theory IV: Log-volume Computations and Set-theoretic Foundations*. [Official PDF](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20IV.pdf). SHA-256: `5bf4b1e0a8c2686562a6859e5009d301335044cfb5efec5d3a9edf764e4af87f`. The official download matches the repository PDF byte for byte.

**Source genell.** Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position*. [Official PDF](https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf). SHA-256: `b9dc115af61dca7fe434332ebafddf6a376a9e2926dad4e1ea2dcc0d2441f768`. The official download matches the repository PDF byte for byte.

**Corollary 2.2, setup and hypotheses through “Then:” — iut4, p.41.**

Corollary 2.2. (Construction of Suitable Initial $\Theta$-Data) Suppose that $X=\mathbb{P}^1_{\mathbb{Q}}$ is the projective line over $\mathbb{Q}$, and that $D\subseteq X$ is the divisor consisting of the three points “$0$”, “$1$”, and “$\infty$”. We shall regard $X$ as the “$\lambda$-line” — i.e., we shall regard the standard coordinate on $X=\mathbb{P}^1_{\mathbb{Q}}$ as the “$\lambda$” in the Legendre form “$y^2=x(x-1)(x-\lambda)$” of the Weierstrass equation defining an elliptic curve — and hence as being equipped with a natural classifying morphism $U_X\to(\mathcal{M}_{\mathrm{ell}})_{\mathbb{Q}}$ [cf. the discussion preceding Proposition 1.8]. Let

$$
\mathcal{K}_V\subseteq U_X(\overline{\mathbb{Q}})
$$

be a compactly bounded subset [i.e., regarded as a subset of $X(\overline{\mathbb{Q}})$ — cf. Remark 2.3.1, (vi), below; [GenEll], Example 1.3, (ii)] whose support contains the nonarchimedean prime “$2$”. Suppose further that $\mathcal{K}_V$ satisfies the following condition:

$(\ast_{j\text{-inv}})$ If $v\in\mathbb{V}(\mathbb{Q})$ denotes the nonarchimedean prime “$2$”, then the image of the subset $\mathcal{K}_v\subseteq U_X(\overline{\mathbb{Q}}_v)$ associated to $\mathcal{K}_V$ [cf. the notational conventions of [GenEll], Example 1.3, (ii)] via the $j$-invariant $U_X\to(\mathcal{M}_{\mathrm{ell}})_{\mathbb{Q}}\to\mathbb{A}^1_{\mathbb{Q}}$ is a bounded subset of $\mathbb{A}^1_{\mathbb{Q}}(\overline{\mathbb{Q}}_v)=\overline{\mathbb{Q}}_v$, i.e., is contained in a subset of the form $2^{N_{j\text{-inv}}}\cdot\mathcal{O}_{\overline{\mathbb{Q}}_v}\subseteq\overline{\mathbb{Q}}_v$, where $N_{j\text{-inv}}\in\mathbb{Z}$, and $\mathcal{O}_{\overline{\mathbb{Q}}_v}\subseteq\overline{\mathbb{Q}}_v$ denotes the ring of integers.

Then:

**Corollary 2.2(i), complete statement — iut4, p.41.**

(i) Write “$\log(\mathfrak{q}^{\forall}_{(-)})$” (respectively, “$\log(\mathfrak{q}^{\nmid 2}_{(-)})$”) for the $\mathbb{R}$-valued function on $\mathcal{M}_{\mathrm{ell}}(\overline{\mathbb{Q}})$, hence also on $U_X(\overline{\mathbb{Q}})$, obtained by forming the normalized degree “$\underline{\deg}(-)$” of the effective arithmetic divisor determined by the q-parameters of an elliptic curve over a number field at arbitrary nonarchimedean primes (respectively, at the nonarchimedean primes that do not divide $2$) [cf. the invariant “$\log(\mathfrak{q})$” associated, in the statement of Theorem 1.10, to the elliptic curve $E_F$]. Also, we shall write $\mathrm{ht}_{\infty}$ for the [normalized] height function on $U_X(\overline{\mathbb{Q}})$ — a function which is well-defined up to a “bounded discrepancy” [cf. the discussion preceding [GenEll], Proposition 3.4] — determined by the pull-back to $X$ of the divisor at infinity of the natural compactification $(\overline{\mathcal{M}}_{\mathrm{ell}})_{\mathbb{Q}}$ of $(\mathcal{M}_{\mathrm{ell}})_{\mathbb{Q}}$. Then we have an equality of “bounded discrepancy classes” [cf. [GenEll], Definition 1.2, (ii), as well as Remark 2.3.1, (ii), below]

$$
\frac{1}{6}\cdot\log(\mathfrak{q}^{\nmid 2}_{(-)})\approx\frac{1}{6}\cdot\log(\mathfrak{q}^{\forall}_{(-)})\approx\frac{1}{6}\cdot\mathrm{ht}_{\infty}\approx\mathrm{ht}_{\omega_X(D)}
$$

of functions on $\mathcal{K}_V\subseteq U_X(\overline{\mathbb{Q}})$.

**Proof of Corollary 2.2(i), complete proof — iut4, p.43.**

Proof. First, we consider assertion (i). We begin by observing that, in light of the condition $(\ast_{j\text{-inv}})$ that was imposed on $\mathcal{K}_V$, it follows immediately from the various definitions involved that

$$
\log(\mathfrak{q}^{\nmid 2}_{(-)})\approx\log(\mathfrak{q}^{\forall}_{(-)})
$$

— where we observe that the function “$\log(\mathfrak{q}^{\forall}_{(-)})$” may be identified with the function “$\underline{\deg}_{\infty}$” of the discussion preceding [GenEll], Proposition 3.4 — on $\mathcal{K}_V\subseteq U_X(\overline{\mathbb{Q}})$. In a similar vein, since the support of $\mathcal{K}_V$ contains the unique archimedean prime of $\mathbb{Q}$, it follows immediately from the various definitions involved [cf. also Remark 2.3.1, (vi), below] that

$$
\log(\mathfrak{q}^{\forall}_{(-)})\approx\mathrm{ht}_{\infty}
$$

on $\mathcal{K}_V\subseteq U_X(\overline{\mathbb{Q}})$ [cf. the argument of the final paragraph of the proof of [GenEll], Lemma 3.7]. Thus, we conclude that $\log(\mathfrak{q}^{\nmid 2}_{(-)})\approx\log(\mathfrak{q}^{\forall}_{(-)})\approx\mathrm{ht}_{\infty}$ on $\mathcal{K}_V\subseteq U_X(\overline{\mathbb{Q}})$. Finally, since [as is well-known] the pull-back to $X$ of the divisor at infinity of the natural compactification $(\overline{\mathcal{M}}_{\mathrm{ell}})_{\mathbb{Q}}$ of $(\mathcal{M}_{\mathrm{ell}})_{\mathbb{Q}}$ is of degree $6$, while the line bundle $\omega_X(D)$ is of degree $1$, the equality of BD-classes $\frac{1}{6}\cdot\mathrm{ht}_{\infty}\approx\mathrm{ht}_{\omega_X(D)}$ on $\mathcal{K}_V\subseteq U_X(\overline{\mathbb{Q}})$ follows immediately from [GenEll], Proposition 1.4, (i), (iii). This completes the proof of assertion (i).

**Proposition 3.4, complete statement — genell, p.17.**

Proposition 3.4. (Faltings Heights and the Divisor at Infinity) For any $\epsilon\in\mathbb{R}_{>0}$, we have

$$
\underline{\deg}_{\infty}\lesssim\mathrm{ht}_{\infty}\lesssim12(1+\epsilon)\cdot\mathrm{ht}^{\mathrm{Falt}}\lesssim(1+\epsilon)\cdot\mathrm{ht}_{\infty}
$$

on $\mathcal{M}_{\mathrm{ell}}(\overline{\mathbb{Q}})$. In particular, if $C\in\mathbb{R}$, then the set of points $[E]\in\mathcal{M}_{\mathrm{ell}}(\overline{\mathbb{Q}})^{\leq d}$ such that $\mathrm{ht}^{\mathrm{Falt}}([E])\leq C$ is finite.

**Proof of Lemma 3.7, paragraph beginning “Now suppose that condition (b)”, first two sentences — genell, p.19.**

Now suppose that condition (b) is satisfied. Recall that by definition $\mathrm{ht}_{\infty}([E_L])$ may be computed as the sum of $\underline{\deg}_{\infty}([E_L])$ and an archimedean term which, in the present situation, is bounded, since $[E_L]\in\mathcal{K}_V$.

**Fidelity limits and relation to the Lean unit.**

- The exact source match for legendreHeight is the parent bounded-discrepancy comparison in IUT IV Corollary 2.2(i), with its proof identifying log(q^forall) with normalized degree at infinity and using the degrees 6 and 1. The chosen normalized Weil-height representative htCan is an implementation choice.

- The constants log(2)/3 and c*|V|+c+log(2)/3 in legendreHeight are supplied by the Lean proof. They are not printed in the cited original passages.

- The three-term archimedean estimate logHeight_1(y)<=finHeight(y)+c*d for y=lambda,lambda^(-1),(lambda-1)^(-1) has only a parent-level source in the bounded archimedean term described in [GenEll] Lemma 3.7 and the compact-bounded comparison in IUT IV. No exact three-term estimate or constant c*d was found in these passages.

- The finite-part inequalities in finHeight_legendreJ_le and finHeight_legendreJ_ge, including factors 2 and 6*c*|V|*d, are implementation-specific elementary estimates under the parent comparison. They must not be presented as verbatim statements of Corollary 2.2(i) or Proposition 3.4.

- The elementary auxiliary lemma j(lambda)=0 implies lambda^6=1 is not stated in the cited original source passages. No direct original quotation for that lemma was located in the two PDFs. Cite the parent height-comparison obligation only, and label this step an auxiliary derivation.

- [GenEll] Proposition 3.4 is a Faltings-height comparison, not the direct statement of the Legendre finite-part estimates. The archimedean boundedness paragraph actually referenced by the IUT IV proof is [GenEll] Lemma 3.7, p.19.

- The quotations retain the paper hypotheses, including support containing 2 and the condition (*j-inv). These source quotations do not certify that each Lean structure has already been shown to imply every paper hypothesis.

**Typesetting normalization.**

- Original English words, sentence order, punctuation, bracketed comments, and quoted labels are retained; line wrapping and discretionary line-end hyphens are removed, and ligatures are expanded.

- Mathematical typesetting is transcribed into KaTeX. Fraktur q uses \mathfrak{q}; calligraphic moduli and bounding sets use \mathcal; normalized degree preserves the original underline as \underline{\deg}; Faltings height preserves the original superscript as \mathrm{ht}^{\mathrm{Falt}}.

- Italic/bold prose, equation spacing and display alignment are normalized; the relation printed as a less-than sign with a wavy underline is rendered with \lesssim.

- The q-parameter with superscript for primes not dividing 2 is rendered as \mathfrak{q}^{\nmid 2}; the all-primes symbol is rendered as \forall, as verified visually.

- No explicit Lean constants or local inequalities have been inserted into any quotation.
