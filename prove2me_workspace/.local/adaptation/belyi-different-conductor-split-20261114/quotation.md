# Mochizuki original-paper context for the different/conductor route

Author: Shinichi Mochizuki. Title: *Arithmetic Elliptic Curves in General Position*. PDF title-page date: **February 2009**.

Official PDF: https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf

Local PDF: `/home/admin-wsl/Coq/abc/refer/Mochizuki/Arithmetic Elliptic Curves in General Position.pdf`

SHA-256: `b9dc115af61dca7fe434332ebafddf6a376a9e2926dad4e1ea2dcc0d2441f768`

HTTP HEAD 200; application/pdf; Content-Length 262332; 2026-11-14. Existing local PDF used; not downloaded.

Printed page numbers coincide with 1-based PDF page numbers.

Ghostscript txtwrite, followed by visual checking of the rasterized PDF pages. Line wrapping and typographic ligatures normalized; mathematical typography transcribed as LaTeX. Words and mathematical relation signs preserved.

**Version warning:** The existing Markdown transcription is not this PDF version: it says March 2008, while the actual PDF title page says February 2009; its Theorem 2.1 proof also differs. Do not use it as an exact-quotation source.

## Mochizuki-GenEll-Prop1.7i

Proposition 1.7(i), statement; printed/PDF pages: [9, 10].

(i) If we restrict functions on $Z(\overline{\mathbb{Q}})$, $U_Z(\overline{\mathbb{Q}})$ to $U_Y(\overline{\mathbb{Q}})$ via $\phi$, then
\[
\mathrm{log\text{-}cond}_E-\mathrm{log\text{-}cond}_D\lesssim\mathrm{log\text{-}diff}_Y-\mathrm{log\text{-}diff}_Z\lesssim\left(1-\frac{1}{e}\right)\cdot\mathrm{log\text{-}cond}_E
\]
on $U_Y(\overline{\mathbb{Q}})$.

Context (not quotation): Here φ:Y→Z is a generically finite morphism of normal Z-proper Z-flat dimension-two schemes; D and E are effective Z-flat Cartier divisors with reduced generic fibers, D_Q=φ_Q^{-1}(E_Q)_red, finite étale restriction off the divisors, and ramification indices along D_Q dividing e. The statement uses BD-class comparisons (≲), not an exact numerical finite-set inequality.

## Mochizuki-GenEll-Prop1.7-localClaim

Proposition 1.7(i), proof, indented elementary claim; printed/PDF pages: [10].

Fix a prime number $p$ and a positive integer $d$. Then there exists a positive integer $n$ such that for any finite Galois extension $L/K$ of finite extensions of $\mathbb{Q}_p$ with $[L:K]\leq d$, the different ideal of $L/K$ contains $p^n\cdot\mathcal{O}_L$ [where we write $\mathcal{O}_L$ for the ring of integers of $L$].

Context (not quotation): The preceding proof paragraph reduces boundedness of the portion over a finite set Σ of log-diff_Y−log-diff_Z to this elementary local claim. This is supporting background, not the exact new finite-set conductor-extension child.

## Mochizuki-GenEll-Thm2.1-BelyiDescent

Theorem 2.1, proof, first paragraph on printed page 13 (selected complete sentences); printed/PDF pages: [13].

On the other hand, by choosing appropriate normal, $\mathbb{Z}$-proper, $\mathbb{Z}$-flat models for $P$, $X$, we may apply Proposition 1.7, (i) [where we take “$e$” to be 1], to conclude that $\mathrm{log\text{-}diff}_P+\mathrm{log\text{-}cond}_C\lesssim\mathrm{log\text{-}diff}_X+\mathrm{log\text{-}cond}_E$ on $\Xi$. Also, we recall from Proposition 1.6 that $\mathrm{log\text{-}cond}_E\lesssim\mathrm{ht}_E\stackrel{\mathrm{def}}{=}\mathrm{ht}_{\mathcal{O}_X(E)}$ on $\Xi$. Thus, by Proposition 1.4, (i), (iii), we compute to find that

Context (not quotation): On printed page 12, φ:X→P is the noncritical Belyi map unramified over U_P, C={0,1,∞}, and E=φ^{-1}(C)_red. The paragraph continues with the displayed height calculation. The first complete quoted sentence is sufficient for the different/conductor comparison route; the additional sentences show its immediate height consumer.

## Scope and fidelity

Proposition 1.7(i) and its use in Theorem 2.1 establish the paper-level geometric/BD-class different–conductor comparison used by Belyi descent.

BelyiActualFieldConductorExtension fixes F=Tripod.fieldOf(belyiImage M φ x).1 and L=x.fieldOf, finite element sets S⊂F, T⊂L, and the actual field inclusion. Under inclusion(S)⊆T it asks for finiteSetLogCond(S)≤finiteSetLogCond(T)+log(absNorm(differentIdeal(O_F,O_L)))/[L:Q].

The paper does not state this exact finite-set formula or these Lean field definitions. Treat the quoted paragraph as original-paper context, and identify the finite-set inequality as an explicit field-level arithmetic auxiliary lemma implementing that context. Do not put the exact new numeric statement inside quotation marks or claim it is a verbatim theorem of Mochizuki.

BelyiActualFieldDifferentTower separately identifies the full-field log-different with the image-field log-different plus the normalized relative different. The paper quotation does not by itself prove either current Lean child.

Recommended short citation: Mochizuki, *Arithmetic Elliptic Curves in General Position*, February 2009 PDF, Theorem 2.1 proof, printed/PDF p. 13; supporting statement Proposition 1.7(i), pp. 9–10.
