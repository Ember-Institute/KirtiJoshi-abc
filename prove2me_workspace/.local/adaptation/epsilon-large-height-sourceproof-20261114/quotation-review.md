Official source: Shinichi Mochizuki, *Inter-universal Teichmüller Theory IV*, [author’s PDF](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20IV.pdf). Retrieved 2026-11-14. The official download equals the repository PDF byte for byte. SHA-256: `5bf4b1e0a8c2686562a6859e5009d301335044cfb5efec5d3a9edf764e4af87f`. Printed and PDF page numbers coincide.

The following quotations are continuous original English passages, with mathematical typesetting transcribed to KaTeX. They were checked against rendered PDF pages. No independent natural-language readback was used.


**Corollary 2.2(iii), complete statement — p.43.**

(iii) The positive real number $H_{\mathrm{unif}}$ of (ii) [which is independent of $\mathcal{K}_V$!] may be chosen in such a way that the following property is satisfied: Let $d$ be a positive integer, $\epsilon_d$ and $\epsilon$ positive real numbers $\leq 1$. Then there exists a finite subset $\mathfrak{Exc}_{\epsilon,d}\subseteq U_X(\overline{\mathbb{Q}})^{\leq d}$ which depends only on $\mathcal{K}_V$, $\epsilon$, $d$, and $\epsilon_d$ such that, in the notation of (ii), the function “$\log(\mathfrak{q}^{\forall}_{(-)})$” of (i) is

$$
\leq H_{\mathrm{unif}}\cdot\epsilon^{-3}\cdot\epsilon_d^{-3}\cdot d^{4+\epsilon_d}+H_{\mathcal{K}}
$$

on $\mathfrak{Exc}_{\epsilon,d}$, and, moreover, the invariant $\epsilon_E$ associated to an elliptic curve $E_F$ as in (ii) [i.e., that satisfies certain conditions which depend on $\mathcal{K}_V$ and $d$] satisfies the inequality $\epsilon_E\leq\epsilon$ whenever the point $x_E\in U_X(F)$ satisfies the condition $x_E\notin\mathfrak{Exc}_{\epsilon,d}$.


**Proof of Corollary 2.2(ii), continuous passage beginning “Now let us set” — p.47.**

Now let us set

$$
\epsilon_E\overset{\mathrm{def}}{=}(60\delta)^2\cdot h^{-1/2}\cdot\log(2\delta\cdot h)\quad(\geq 5\cdot\delta\cdot h^{-1/2});
$$

$$
\epsilon_d^*\overset{\mathrm{def}}{=}\frac{1}{16}\cdot\epsilon_d\quad(<\tfrac{1}{2}\leq 1)
$$

— where we apply the estimates $h\geq 1$, $\log(2\delta\cdot h)\geq\log(2\delta)\geq\log(4)\geq 1$ [cf. the property (E6) in the proof of Theorem 1.10], and $\epsilon_d\leq 1$.


**Proof of Corollary 2.2(ii), final sentence on page 47 — p.47.**

Thus, by possibly enlarging the finite set $\mathfrak{Exc}_d$ [in a fashion that depends only on $\mathcal{K}_V$, $d$, and $\epsilon_d$ and in such a way that $h\leq H_{\mathrm{unif}}\cdot\epsilon_d^{-3}\cdot d^{4+\epsilon_d}+H_{\mathcal{K}}$ on $\mathfrak{Exc}_d$ for some positive real number $H_{\mathrm{unif}}$ that is independent of $\mathcal{K}_V$ and some positive real number $H_{\mathcal{K}}$ that depends only on $\mathcal{K}_V$], we may assume without loss of generality that $\epsilon_E\leq 1$.


**Proof of Corollary 2.2, final two sentences (excluding proof-end symbol) — p.48.**

This completes the proof of assertion (ii). Finally, assertion (iii) follows immediately by applying the argument applied above in the proof of assertion (ii) in the case of the inequality “$1<\epsilon_E$” to the inequality “$\epsilon<\epsilon_E$”.


**Context and fidelity.** The paper sets $h=\log(\mathfrak{q}^{\forall})$ on p.44 and $\delta=2^{12}\cdot3^3\cdot5\cdot d$ on p.42. The general smallness claim is Corollary 2.2(iii), quoted above, under its full arithmetic hypotheses. It is stated outside a finite exceptional set, with a bound on the height on that set.

The explicit sufficient condition

$$
1\leq h,\qquad\left(\frac{(60\delta)^2(2\delta+4)}{\epsilon}\right)^4\leq h
$$

is **not a statement quoted from this paper**. If used in `epsilonE_le`, it must be identified as an auxiliary analytic sufficient bound supplied by the formalization. Proving that bound for the error expression does not alone prove Corollary 2.2(iii), its finite exceptional set, its uniform height bound, or its arithmetic prerequisites.

**Typesetting normalization.**


- Original English words, order, punctuation, bracketed comments, and exclamation marks are retained; PDF line breaks, page headers, and discretionary line-end hyphenation are removed.

- Ligatures are expanded to ordinary letters (e.g. “satisfied” rather than the PDF ligature in “satisﬁed”).

- Printed mathematical notation is transcribed into KaTeX: epsilon glyphs use \epsilon; Fraktur q and Exc use \mathfrak; calligraphic K uses \mathcal; roman labels use \mathrm; the printed def over the equality sign uses \overset{\mathrm{def}}{=}.

- Equation indentation, spacing, italic/bold prose, and display alignment are normalized; no mathematical factors, exponents, hypotheses, quantifiers, or English words are added to quotations.

- The definition quoted on p.47 uses h^{-1/2}; the equivalent quotient notation in the task, with denominator sqrt(h), is not substituted into that quote.
