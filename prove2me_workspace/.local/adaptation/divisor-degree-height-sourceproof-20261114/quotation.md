Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position*, February 2009.

Official PDF: https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf

Local PDF: `/home/admin-wsl/Coq/abc/refer/Mochizuki/Arithmetic Elliptic Curves in General Position.pdf`

SHA-256: `b9dc115af61dca7fe434332ebafddf6a376a9e2926dad4e1ea2dcc0d2441f768`

Theorem 2.1(i) — printed page 11 / PDF page 11:

> Write $\omega_X$ for the canonical sheaf on $X$. Suppose that $U_X$ is a hyperbolic curve — i.e., that the degree of the line bundle $\omega_X(D)$ is positive.

Theorem 2.1(ii), opening clauses — printed page 11 / PDF page 11:

> Let $P \overset{\mathrm{def}}{=} \mathbb{P}^1_{\mathbb{Q}}$ be the projective line over $\mathbb{Q}$; $C \subseteq P$ the divisor consisting of the three points “0”, “1”, and “$\infty$”;

A selected opening clause; the original sentence continues with further data.

Proof of Theorem 2.1 — printed page 12 / PDF page 12:

> Now set $E \overset{\mathrm{def}}{=} \phi^{-1}(C)_{\mathrm{red}} \subseteq X$ [so $\phi^*\omega_P(C) \cong \omega_X(E)$].

Proposition 1.4(i) — printed page 6 / PDF page 6:

> (i) We have
> $$
> \operatorname{ht}_{\overline{\mathcal{L}}\otimes\overline{\mathcal{M}}}(x)=\operatorname{ht}_{\overline{\mathcal{L}}}(x)+\operatorname{ht}_{\overline{\mathcal{M}}}(x)
> $$
> for $x \in X(\overline{\mathbb{Q}})$.

Proposition 1.4(iii) — printed page 6 / PDF page 6:

> (iii) The BD-class of $\operatorname{ht}_{\overline{\mathcal{L}}}$ depends only on the isomorphism class of the line bundle $\mathcal{L}_{\mathbb{Q}}$ on $X_{\mathbb{Q}}$. In particular, it makes sense to write $[\operatorname{ht}_{\mathcal{L}}]$ or $[\operatorname{ht}_{\mathcal{L}_{\mathbb{Q}}}]$ for the BD-class $[\operatorname{ht}_{\overline{\mathcal{L}}}]$ of $\operatorname{ht}_{\overline{\mathcal{L}}}$.

Definition 1.2(ii), opening segment — printed page 5 / PDF page 5:

> (ii) Fix a subset $\mathcal{F} \subseteq X(\overline{\mathbb{Q}})$. If $\alpha,\beta : \mathcal{F} \to \mathbb{R}$ are functions, then we shall write
> $$
> \alpha \lesssim_{\mathcal{F}} \beta\quad (\text{respectively, }\alpha \gtrsim_{\mathcal{F}} \beta;\ \alpha \approx_{\mathcal{F}} \beta)
> $$
> if there exists a [“constant”] $C \in \mathbb{R}$ such that $\beta(x)-\alpha(x)\leq C$ (respectively, $\alpha(x)-\beta(x)\leq C;\ |\alpha(x)-\beta(x)|\leq C$) for all $x \in \mathcal{F}$;

Opening segment ends at the original semicolon. The order of the two one-sided inequalities is transcribed as printed; the two-sided absolute-value condition is the relevant one here.

Proof of Theorem 2.1, lead-in and first line of displayed calculation — printed page 13 / PDF page 13:

> Thus, by Proposition 1.4, (i), (iii), we compute to find that
> $$
> \operatorname{ht}_{\omega_X}\ \approx\ \operatorname{ht}_{\omega_X(E)}-\operatorname{ht}_E\ \approx\ \operatorname{ht}_{\omega_P(C)}-\operatorname{ht}_E
> $$

Only the first line of the displayed calculation is selected. The display continues with inequalities. The source uses the height on P along the map phi in this calculation; no pullback/composition symbol has been inserted into the quotation.

These passages supply the original-paper parent context: the three-cusp divisor C, the log-canonical pullback isomorphism for the reduced inverse-image divisor E, additive heights, invariance of height BD-classes under line-bundle isomorphism, and the resulting height decomposition in the proof of Theorem 2.1. The exact auxiliary identity canonical+cusp = polar(phi)+div(r), with an explicit rational-function witness r, is a statement to be proved in the formal Genl/Heights/Belyi source; it is not quoted verbatim from this paper. Likewise, a uniform bound for arbitrary explicit polar presentations from a principal relation requires the precise quantifiers, presentation data, and constants established by the formal source. The paper states the parent relation using line bundles and BD-classes; it does not state those two auxiliary lemmas in their explicit presentation-level form.

GenEll directly supplies the required parent context. Definition 1.5 defines reduced divisors, log-different, and log-conductor; it is not a source of an explicit polar-presentation height decomposition. Noncritical Belyi Maps Theorem 2.5 is the existence premise for the map cited in GenEll; no additional quotation from it is needed for these height/divisor nodes.

English wording checked against the official PDF. Mathematics represented in LaTeX; line wrapping and typographic emphasis normalized. Selected clauses and display lines are explicitly marked. No formal theorem names or presentation-level quantifiers are inserted into the quotations.

Existing PDF reused; no main-workspace edits, downloads, or compilation.
