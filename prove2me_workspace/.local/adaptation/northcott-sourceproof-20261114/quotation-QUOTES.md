# Mochizuki original quotations for the Northcott source unit

These quotations were checked against rendered original PDF pages.
Mathematical notation is transcribed into LaTeX. Line wrapping, end-of-line hyphenation, font emphasis, and ligatures are normalized.
The words, punctuation, hypotheses, and mathematical content are preserved. No ellipsis removes a hypothesis.

## N1 — Primary quotation: the whole bounded-degree finiteness paragraph

Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position*, February 2009,
Section 1, Proposition 1.4 (Basic Properties of Heights), (iv).
Printed page **6**; PDF page **6** (one-based).
Official URL: https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf
PDF SHA-256: `b9dc115af61dca7fe434332ebafddf6a376a9e2926dad4e1ea2dcc0d2441f768`.
Page image: `general-position-page-6.png`.

> (iv) Let (d) be a positive integer, (C\in\mathbb R). Suppose further that the line bundle (\mathcal L_{\mathbb Q}) is ample on (X_{\mathbb Q}). Then the set of points (x\in X(\overline{\mathbb Q})^{\leq d}) [cf. Example 1.3, (i)] such that (\mathrm{ht}_{\overline{\mathcal L}}(x)\leq C) is finite.

**Coverage.** This states bounded-degree and bounded-height finiteness over varying number fields.
It is not a fixed-field-only result. It supplies direct mathematical source context for `boundedDegreeFiniteness`.
The preceding proposition setup specifies arithmetic line bundles on the normal, proper, flat model (X).
The height is defined on page 4 using the degree divided by ([F:\mathbb Q]); see `general-position-page-4.png`.

**Limits.** The quotation does not name `AbcAdaptation.Tripod.htCan` or identify its exact Mathlib normalization.
The formal target specializes to algebraic λ outside 0 and 1 with the concrete minimal-field absolute logarithmic height.
An exact equality with a chosen metric height is not established by this quotation.
For finiteness, a justified bounded discrepancy between the two heights suffices.
The formal proof independently uses its fixed height definition and does not import that comparison as an extra premise.

## N2 — The complete bounded-degree and Galois-finite definition

Same work and official URL; Section 1, Example 1.3 (Various Natural Subsets of the Set of Points), (i).
Printed page **5**; PDF page **5**.
Same PDF SHA-256. Page image: `general-position-page-5.png`.

> (i) If (d\in\mathbb N\cup\{\infty\}), then we shall denote by
> \[
> X(\overline{\mathbb Q})^{\leq d}\subseteq X(\overline{\mathbb Q})
> \]
> the union of the subsets (X(F)\subseteq X(\overline{\mathbb Q})) as (F) ranges over the number fields such that ([F:\mathbb Q]\leq d) [so (X(\overline{\mathbb Q})^{\leq\infty}=X(\overline{\mathbb Q}))];
> \[
> X(\overline{\mathbb Q})^{=d}\overset{\mathrm{def}}{=}X(\overline{\mathbb Q})^{\leq d}\setminus X(\overline{\mathbb Q})^{\leq d-1}\subseteq X(\overline{\mathbb Q})
> \]
> [cf. the discussion in Definition 1.5, (i), below of “minimal fields of definition”]. More generally, if (\mathcal E\subseteq X(\overline{\mathbb Q})) is any subset, then we shall write (\mathcal E^{\leq d}\overset{\mathrm{def}}{=}\mathcal E\cap X(\overline{\mathbb Q})^{\leq d}), (\mathcal E^{=d}\overset{\mathrm{def}}{=}\mathcal E\cap X(\overline{\mathbb Q})^{=d}). If (\mathcal E\subseteq X(\overline{\mathbb Q})) is a subset such that each (\mathcal E^{\leq d}) [where (d) ranges over the positive integers] is finite, then we shall say that (\mathcal E) is Galois-finite.

**Coverage.** This fixes the varying-field scope and the meaning of Galois-finite exceptional sets.
**Limits.** A Galois-finite set need not be finite without fixing a degree bound. The Lean target fixes (d).

## N3 — Whole paragraph connecting bounded height to a finite exceptional set

Same work and official URL; Section 3, proof of Lemma 3.7 (Finite Exceptional Sets), first paragraph.
Printed page **18**; PDF page **18**.
Same PDF SHA-256. Page image: `general-position-page-18.png`.

> Proof. First, observe that if (v) is any local height of (E_L), then (d\cdot\underline{\mathrm{deg}}_{\infty}([E_L])\geq v\cdot\log(2)). Next, let us observe that by Proposition 3.4, for an appropriate choice of (C), we may assume that (\mathrm{ht}^{\mathrm{Falt}}([E_L])+C\cdot d^{\epsilon}\geq\mathrm{ht}^{\mathrm{Falt}}([E_L])+C\geq\frac1{14}\cdot\underline{\mathrm{deg}}_{\infty}([E_L])) [i.e., where we take “(12(1+\epsilon))” to be 14]. Thus, condition (a) implies that
> \[
> l\geq\frac{100d}{14}\cdot\underline{\mathrm{deg}}_{\infty}([E_L])\geq\left(\frac{100\cdot\log(2)}{14}\right)\cdot v>v
> \]
> — i.e., that (l) is (>\) the local heights of (E_L) at all the primes of multiplicative reduction. On the other hand, if condition (b) is satisfied, and, moreover (E_L) has no primes of multiplicative reduction [so (\underline{\mathrm{deg}}_{\infty}([E_L])=0)], then the fact that ([E_L]\in\mathcal K_V) implies that (\mathrm{ht}_{\infty}([E_L])) is bounded [independently of (L,E_L,l)], so, by Proposition 1.4, (iv), ([E_L]) belongs to some [fixed] finite exceptional set (\mathfrak{Exc}_d) [which we think of as (\mathfrak{Exc}\cap\mathcal M_{\mathrm{ell}}(\overline{\mathbb Q})^{\leq d})], as desired.

**Coverage.** This is a direct use of N1 for finite exceptional sets in the general-position argument.
The named conditions remain those of Lemma 3.7; the page image includes their complete statement.
**Limits.** It concerns elliptic-curve moduli and auxiliary hypotheses. It is not the exact tripod theorem.

## N4 — Whole Statement (ii) paragraph for the eventual general-position consumer

Same work and official URL; Section 2, Theorem 2.1 (Compactly Bounded Subsets and the ABC Conjecture), (ii).
Printed page **11**; PDF page **11**.
Same PDF SHA-256. Page image: `general-position-page-11.png`.

> (ii) (ABC Conjecture for Σ-Supported Compactly Bounded Subsets) Let (P\overset{\mathrm{def}}{=}\mathbb P^1_{\mathbb Q}) be the projective line over (\mathbb Q); (C\subseteq P) the divisor consisting of the three points “0”, “1”, and “∞”; (U_P\overset{\mathrm{def}}{=}P\setminus C); (d) a positive integer; (\epsilon\in\mathbb R_{>0}) a positive real number; (\mathcal K_V\subseteq U_P(\overline{\mathbb Q})) a compactly bounded subset [i.e., regarded as a subset of (P(\overline{\mathbb Q})) — cf. Example 1.3, (ii)] whose support contains Σ. Write (\omega_P) for the canonical sheaf on (P). Then the inequality of BD-classes of functions
> \[
> \mathrm{ht}_{\omega_P(C)}\lesssim(1+\epsilon)(\mathrm{log\text{-}diff}_P+\mathrm{log\text{-}cond}_C)
> \]
> holds on (\mathcal K_V\cap U_P(\overline{\mathbb Q})^{\leq d}).

**Coverage.** This gives the paper context of the downstream `StatementII` consumer.
It is a statement in an equivalence theorem, not an unconditional assertion of ABC in this paper.
**Limits.** N1 alone does not prove N4. The explicit height, conductor and discriminant comparisons remain separate.
IUT IV Remark 2.3.1(ii), printed/PDF page 55, corrects the direction assigned to the original BD notation in Definition 1.2(ii).
Any formal inequality comparison must use that correction; quoting N4 does not supply the adaptation proof.

## N5 — Exact IUT IV sentence applying bounded height finiteness

Shinichi Mochizuki, *Inter-universal Teichmüller Theory IV: Log-volume Computations and Set-theoretic Foundations*, April 2020,
Section 2, proof of Corollary 2.2, discussion of (P5).
Printed page **46**; PDF page **46**.
Official URL: https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20IV.pdf
PDF SHA-256: `5bf4b1e0a8c2686562a6859e5009d301335044cfb5efec5d3a9edf764e4af87f`.
Page image: `iut-iv-page-46.png`.

> On the other hand, [by assertion (i); [GenEll], Proposition 1.4, (iv)] this implies that there is only a finite number of possibilities for the (j)-invariant of (E_F).

This is one complete sentence, not a whole paragraph. The preceding displayed estimate makes (h^{1/4}), hence (h), bounded.
The complete surrounding page is retained for context.
**Coverage.** IUT IV itself explicitly consumes the same Proposition 1.4(iv) in its finite-exception argument.
**Limits.** This sentence counts possible (j)-invariants, not all twists or all tripod points, and it does not implement the integer-polynomial proof.

## N6 — Complete proof paragraph linking IUT IV to Statement (ii)

Same IUT IV work and official URL; Section 2, proof of Corollary 2.3.
Printed pages **54–55**; PDF pages **54–55**.
Same IUT IV PDF SHA-256. Page images: `iut-iv-page-54.png`, `iut-iv-page-55.png`.

> Proof. One verifies immediately that the content of the statement of Corollary 2.3 coincides precisely with the content of [GenEll], Theorem 2.1, (i). Thus, it follows from the equivalence of [GenEll], Theorem 2.1, that, in order to complete the proof of Corollary 2.3, it suffices to verify that [GenEll], Theorem 2.1, (ii), holds. That is to say, we may assume without loss of generality that:
>
> · (X=\mathbb P^1_{\mathbb Q}) is the projective line over (\mathbb Q);
>
> · (D\subseteq X) is the divisor consisting of the three points “0”, “1”, and “∞”;
>
> · (\mathcal K_V\subseteq U_X(\overline{\mathbb Q})) is a compactly bounded subset [cf. Remark 2.3.1, (vi), below] whose support contains the nonarchimedean prime “2”;
>
> · (\mathcal K_V) satisfies the condition “((\ast_{j\text{-}\mathrm{inv}}))” of Corollary 2.2.

**Coverage.** This identifies the original-paper consumer of the bounded-discrepancy argument.
**Limits.** It is not a proof of the Northcott theorem and does not number the two formal child lemmas.
