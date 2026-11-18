The three trilingual drafts read the current temporary Lean files under `/tmp/p2m-provider-legendre-height-next-20261118`. They use only Mochizuki's original papers for paper context. They do not use Joshi material or later secondary accounts.

The exact statement sources are `refer/iut/Iut/Tripod/CurveFacts.lean:403` (`LegendreHeightHyp`) and `refer/iut/Iut/Tripod/Height.lean:791` (`legendreHeight`). The canonical consumer is the new draft `Solutions/Source_TripodProviderLegendreComparison.lean:20`. The source reference points to line 402 in several comments, but the declaration itself is at line 403 in the current file.

The paper anchors are:

Shinichi Mochizuki, *Inter-universal Teichmüller Theory IV: Log-volume Computations and Set-theoretic Foundations*, April 2020. Corollary 2.2(i), printed and PDF page 41; proof on page 43; Remark 2.3.1(ii) on page 55. [Official PDF](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20IV.pdf). Local copy: `refer/Mochizuki/Inter-universal Teichmuller Theory IV.pdf` (SHA-256 `5bf4b1e0a8c2686562a6859e5009d301335044cfb5efec5d3a9edf764e4af87f`).

> Then we have an equality of “bounded discrepancy classes” [cf. [GenEll], Definition 1.2, (ii), as well as Remark 2.3.1, (ii), below]
>
> $$\frac16\log(\mathfrak q_{(-)}^{\nmid 2})\approx\frac16\log(\mathfrak q_{(-)}^{\forall})\approx\frac16\mathrm{ht}_{\infty}\approx\mathrm{ht}_{\omega_X(D)}$$
>
> of functions on $\mathcal K_V\subseteq U_X(\overline{\mathbb Q})$.

In the adapted proof the all-primes logarithm is `P.h`, the selected representative on the right is `htCan`, and `K.set` is the point set. The comparison does not establish the separate prime-2 comparison in the quoted display.

- `refer/Mochizuki/Arithmetic_Elliptic_Curves_in_General_Position.md:95`–`:103`: Definition 1.2(ii), bounded discrepancy and its equivalence classes. The symmetric relation means that the absolute difference is uniformly bounded.
- The same file at `:121`–`:133`: Example 1.3(ii), compactly bounded subsets with local bounding domains and finite support including archimedean places.
- The same file at `:399`–`:427`: the normalized degree of the moduli divisor at infinity, its height class, and Proposition 3.4. Proposition 3.4 itself compares this height with Faltings height; it is not a verbatim statement of the explicit Legendre constants in the Lean proof.
- `refer/Mochizuki/Inter-universal_Teichmuller_Theory_4.md:1147`–`:1167`: Corollary 2.2 sets up the Legendre line and states the bounded discrepancy chain. The selected component is `(1/6) log(q_all) ≈ ht_{ω_X(D)}`. The paper also states the comparison excluding the prime 2, under its stated support and bounded-j conditions. The three draft Lean units cover the all-primes comparison and its numerical consumer.
- The same IUT IV file at `:1225`–`:1241`: the proof of Corollary 2.2(i). It identifies the all-primes q-degree with the degree at infinity, compares it with `ht_infinity` on the compactly bounded set, and derives the factor `1/6` from the pullback degree six and `deg(ω_X(D)) = 1`.

Mochizuki corrects the one-sided notation from [GenEll] in IUT IV, Remark 2.3.1(ii), local markdown line 1543. The correction says that `alpha ≲ beta` means `alpha(x) - beta(x) ≤ C`; the first two cases in [GenEll], Definition 1.2(ii), were reversed. The adapted `DiscrepancyLE` follows this corrected direction. Its symmetric `DiscrepancyEquiv` and the two inequalities in these readbacks agree with the original-paper correction.

The explicit constants in `legendreHeight` are `C1 = log 2 / 3` and `C2 = K.c * K.V.card + K.c + log 2 / 3`. Their directions are `P.h/6 ≤ htCan + C1` and `htCan ≤ P.h/6 + C2`. The canonical consumer obtains `C1` and `C2` from the theorem and chooses their maximum. The drafts preserve the actual supplied provider argument and impose no point-degree bound.

The provider normalization is `P.h x = finHeight (legendreJ (gen x.1)) / deg x.1`. The fixed numerical height `auxiliaryHeight` is this same expression. The Weil height `htCan` is Mathlib's relative logarithmic height divided by the same degree. The words “canonical height” here refer to this fixed Weil-height expression, not a Néron–Tate height on an elliptic curve.

The temporary parent theorem retains the original statement and proof text. Its four private source-name aliases reuse the existing numerical upper bound, lower bound, archimedean triple bound, and the zero-j sixth-power theorem. The last alias specializes the original generic statement to the actual tripod generator and retains the two nonzero premises. The canonical consumer uses `providerHeight_eq_auxiliaryHeight` and the two one-sided inequalities only.

The independent drafts were prepared before compilation and are archived with the editorial terminology and citation adjustments. The Chinese term for “compactly bounded subset” remains pending. Compilation receipts are recorded separately in the source ledger.
