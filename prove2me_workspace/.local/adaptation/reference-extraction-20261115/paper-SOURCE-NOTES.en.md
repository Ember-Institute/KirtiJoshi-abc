# Original-paper source notes for IUT IV Theorem 1.10 and Corollary 2.2

Purpose: source descriptions for three declarations in `refer/iut`. This is a source comparison, not a proof, a compilation result, or an independent mathematical review. Only original papers by Shinichi Mochizuki supply mathematical source claims. No other author's exposition is substituted for the source.

`source-descriptions.en.json` contains ready-to-use English paragraphs. Each entry separates `source_description_en` from `formal_readback_en`, and includes exact source locations and short quotations. `pdf-manifest.json` records each local PDF's SHA-256, version, page count, metadata, and extraction method. Per-page text files retain the inspected extraction. The extraction collapses some fractions and superscripts; the normalized formulas below must not be labelled verbatim PDF text.

## PDF provenance

| Key | Original paper/version shown on title page | Local PDF | SHA-256 | File pages |
|---|---|---|---|---:|
| iut4 | Shinichi Mochizuki, *Inter-universal Teichmüller Theory IV: Log-volume Computations and Set-theoretic Foundations*, April 2020 | `refer/Mochizuki/Inter-universal Teichmuller Theory IV.pdf` | `5bf4b1e0a8c2686562a6859e5009d301335044cfb5efec5d3a9edf764e4af87f` | 87 |
| iut1 | Shinichi Mochizuki, *Inter-universal Teichmüller Theory I: Construction of Hodge Theaters*, May 2020 | `refer/Mochizuki/Inter-universal Teichmuller Theory I.pdf` | `7360e3ed27c235b5497a0743d3ed1646fbb97688547d16b7c784fc7f127f1f03` | 186 |
| genell | Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position*, February 2009 | `refer/Mochizuki/Arithmetic Elliptic Curves in General Position.pdf` | `b9dc115af61dca7fe434332ebafddf6a376a9e2926dad4e1ea2dcc0d2441f768` | 25 |

All page references below use the printed page numbers in these local versions. The corresponding **1-based PDF file page number is the same** on every cited page; do not add an offset. The PDFs were already present, so no download was necessary. The mathematical material quoted or paraphrased comes from the PDFs; the repository Markdown transcriptions were used only to locate candidate passages, then checked against extraction from the PDF pages.

## Theorem 1.10: original statement and formal adaptation

**Source.** IUT IV, Theorem 1.10 begins on p. 22 and ends on p. 23. Its proof runs through p. 31. Its hypotheses specify initial Θ-data as in IUT I, Definition 3.1, the situation of IUT III, Corollary 3.12, good reduction away from 2ℓ at the stated good places, and the specified field obtained by adjoining √−1 and torsion points. In the theorem, `F_tpd = F_mod(E[2])`, `d_mod = [F_mod : ℚ]`, and `e*_mod = 2^12·3^3·5·e_mod`. The different, q-divisor, and conductor are actual effective arithmetic divisors; the logarithmic invariants are their normalized degrees (p. 23).

The first inequality in the final unnumbered display on p. 23 is, in normalized mathematical transcription,

`(1/6)·log(q) ≤ (1 + 20·d_mod/ℓ)·(log(d_{F_tpd}) + log(f_{F_tpd})) + 20·(e*_mod·ℓ + η_prm)`.

The following inequality replaces the tripodal-field terms by the corresponding terms for F. The formal declaration in this task has the **first** inequality as its conclusion. It does not include the preceding explicit formula for `C_Θ`, nor the following comparison with F, as its own conclusion. On p. 23, the paper identifies the Corollary 3.12 quantity `|log(q)|` with `log(q)/(2ℓ)` and invokes `C_Θ ≥ −1` to obtain the estimate.

The proof's local estimates refer to Proposition 1.4 (statement pp. 13–14), Proposition 1.5 (statement begins p. 14, parts (iii)–(iv) pp. 15–16), and Proposition 1.7 (statement begins p. 16). Its arithmetic field/different inputs refer to Proposition 1.3 (begins p. 11), Proposition 1.8 (begins p. 18), and proof Steps (ii)–(iii). Proposition 1.6 is on p. 16 and prints the factor `4/3` in the prime-counting bound. The formal `PrimeCountingBound` has `3/2`; this is a documented formal adaptation, not a literal transcription of Proposition 1.6.

**Formal readback.** `Theorem110Invariants.theorem110` assumes `cert`, `est`, `pnt`, and `h312` for an existing `X` and `inv`. It derives the displayed scalar inequality. In `Theorem110Invariants`, `emod`, `logDtpd`, `logFtpd`, `dst`, and `logDK` are supplied data. Their names explain the intended mathematical interpretation; their presence does not show that the tripodal field, its different/conductor divisors, or the ramification invariants have been constructed. The arithmetic relations are supplied by `Theorem110Certificate`; local geometry and bounds are supplied by `LocalEstimate`. `d_mod` and the q-pilot expression are derived from the existing abstract bundle. A source description must retain these premises.

## Corollary 2.2: original hypotheses and conclusions

**Source.** Corollary 2.2 spans pp. 41–43; its proof spans pp. 43–48. The ambient curve is the λ-line `X = ℙ¹_ℚ` with `D = {0,1,∞}` and `U_X = X \ D`. The compactly bounded subset `K_V` has support containing the nonarchimedean prime 2, and satisfies `(∗j-inv)`, the boundedness of the image under j at 2 (p. 41). Assertion (i) compares bounded discrepancy classes of `log(q_{∤2})/6`, `log(q_∀)/6`, `ht_∞/6`, and `ht_{ω_X(D)}`.

Assertion (ii) has a finite exceptional subset depending on `K_V`, degree d and ε_d; it includes the stated exceptional automorphism points and comes with an explicit uniform height bound. With `δ = 2^12·3^3·5·d`, (C1) and (C2) are on p. 42:

`√h ≤ ℓ ≤ 10δ√h·log(2δh)`, where `h = log(q_∀)`,

`(1/6)log(q) ≤ (1/6)log(q_{∤2}) ≤ (1/6)h ≤ (1 + ε_E)(log-diff_X(x_E) + log-cond_D(x_E)) + C_K`,

`ε_E = (60δ)^2·h^(−1/2)·log(2δh)`.

The source specifies the torsion-field hypotheses on F and the tripodal field on p. 42. On p. 43, it records

`log-diff_X(x_E) = log(d_{F_tpd})`,

`log(f_{F_tpd}) ≤ log-cond_D(x_E) ≤ log(f_{F_tpd}) + log(2ℓ)`.

These relations recur at the conclusion of the proof, p. 48. Assertion (iii), p. 43, gives a further finite exceptional set and uniform bound so that `ε_E ≤ ε` outside it.

**Formal readback.** `Corollary22Inputs.c2` proves the final upper bound in (C2), `ε_E ≤ 1`, and nonnegativity of the sum `logDiff + logCond`, at a point above its explicit formal threshold and outside `I.excCore`. It assumes the input package, theta-data existence, the prime bounds, and `h312` on produced bundles satisfying the predicate P. It does not itself output the initial Θ-data, state the complete chain of inequalities in (C2), or establish the full uniform exceptional-set statements in parts (ii)–(iii). It does internally choose a suitable prime and invoke the supplied existence field.

The paper's p. 47 uses `C_K := 40η_prm + 2B_K`, where `B_K` bounds `log(q_∀)/6 − log(q_{∤2})/6`. The formal theorem uses `40·pnt.η + I.B/3`, where `I.B` bounds the unscaled height contribution supported over 2. These normalizations are compatible after scaling the bound, but the two symbols are not literally the same definition.

## Conditions (P1)–(P7) in the proof

The following is a normalized transcription/paraphrase, not a sequence of verbatim quotations. `h_v` is the local height of E_F and `p_v` its residue characteristic; the notation and sum expression for h appear in the proof on p. 44.

| Label | Printed/PDF page | Original mathematical content and role |
|---|---:|---|
| (P1) | 45 | Prime `ℓ` satisfies `(5 ≤)√h ≤ ℓ ≤ 10δ√h·log(2δh) ≤ 20δ²h²`. This supplies (C1). |
| (P2) | 45 | `ℓ` divides no nonzero local height `h_v`. |
| (P3) | 45 | If `ℓ = p_v`, then `h_v < √h`. |
| (P4) | 45 | `E_F` has no ℓ-cyclic subgroup scheme, after enlarging the finite exceptional set; the argument cites Mochizuki's [GenEll], Lemma 3.5 and Proposition 3.4. |
| (P5) | 46 | The set of bad multiplicative places of F_mod away from `2ℓ` is nonempty, after enlarging the exceptional set. |
| (P6) | 46 | The Galois image on ℓ-torsion contains `SL₂(𝔽_ℓ)`; the argument uses (P2), (P4), (P5), and [GenEll], Lemma 3.1(iii). |
| (P7) | 46 | The resulting initial Θ-data satisfy the hypotheses of Theorem 1.10. The preceding paragraph asserts existence of `C̲_K`, V, ε satisfying IUT I, Definition 3.1(a)–(f); the following paragraph explains the role of full SL₂ image in obtaining V and ε. |

In [GenEll], Lemma 3.1 begins on p. 13 and part (iii) is on p. 14: a subgroup of `GL₂(𝔽_ℓ)` containing the standard unipotent matrix and a matrix that is not upper triangular contains `SL₂(𝔽_ℓ)`. Lemma 3.5 and Proposition 3.4 are on p. 17. Lemma 3.5 assumes an ℓ-cyclic subgroup and the coprimality of ℓ with local multiplicative heights; it bounds `ℓ·deg_∞(E)/(12(1+ε))` by `ht_Falt(E) + 2logℓ + C`. These are citations to Mochizuki's original paper, not replacements by subsequent authors.

The formal `cyclic_bound` has `((ℓ−2)/24)·(h − heightEq(2))` on the left, whereas the displayed argument after (P4) uses `((ℓ−2)/24)·h`. The formal version deliberately works away from 2 and absorbs the bounded contribution into its threshold. The formal package supplies that adapted bound; source descriptions must not present it as the exact displayed inequality in the original paper. The formal existence field assumes (P2), (P3), (P5), (P6), with `ℓ ≥ 7`; it does not require (P4) separately because the caller has already used the cyclic-subgroup argument to obtain the SL₂ input. The paper has ℓ ≥ 5 and, through its torsion assumptions, ℓ ≠ 5; the formal branch works directly with ≥ 7.

## What initial Θ-data contain in IUT I

IUT I, Definition 3.1 is on pp. 61–63. Part (a), p. 61, fixes the number field and algebraic closure. Part (b), pp. 61–62, fixes the once-punctured elliptic curve, nonempty bad valuation set, and field/torsion conditions. Part (c), p. 62, fixes the prime, full SL₂ Galois image, and local coprimality conditions. Part (d), p. 62, specifies the hyperbolic orbicurve of type `(1,ℓ-tors)±`, its K-core, and associated covers. Part (e), pp. 62–63, specifies the section of valuations over F_mod and the local type at bad valuations. Part (f), p. 63, specifies the cusp with its compatibility at bad places.

Thus the paper's (P7) is an existence statement about geometric objects with compatibility conditions. `ThetaDataExistence` adapts that step into an abstract data-bundle existence interface plus numerical readback. Defining this structure does not prove it inhabited or supply the geometric construction. The source description should cite (P7) as the mathematical source and describe the formal structure as an explicit input.

IUT I points to *The Étale Theta Function*, §2, in parts (d)–(f). That paper was not separately inspected for this source-description task. No direct quotation or independently verified page claim about it is made here; the verified direct sources are IUT IV (P7) and IUT I Definition 3.1.
