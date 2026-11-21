# Joshi II's normalized square exponents

Kirti Joshi, *Construction of Arithmetic Teichmuller spaces II: Proof of a local prototype of Mochizuki's Corollary 3.12*, arXiv:2303.01662v3, 24 February 2025. Theorem 9.2.1 starts on printed and PDF page 27. Its coefficient calculation follows equation (9.2.4) on printed and PDF page 28. The repository TeX is at `refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.tex`, lines 1147–1166. [Author's preprint](https://arxiv.org/abs/2303.01662v3) · [PDF, page 28](https://arxiv.org/pdf/2303.01662v3#page=28)

The unversioned PDF URL returned HTTP 200 directly on 21 November 2026. Its SHA-256 is `a25e58456673d905f6be328773926ec8a5dbb419fe278ca478827f163ccdf4af`. The local TeX SHA-256 is `9d8ccfbb1711e2b7f4fe1b9e44636ebad03a823506c55d47b2e5df6e6b97b7d6`. [PDF download](https://arxiv.org/pdf/2303.01662)

## Paper source

> Using \(\ell^*=\frac{\ell-1}{2}\), or equivalently \(2\ell^*+1=\ell\) and canceling factors this simplifies to
> \[
> \frac{1}{12}\left(1+\frac{1}{\ell^*}\right)\log(|q|_{\mathbb C_p}).
> \]
> If \(\ell\) is sufficiently large then
> \[
> \frac{1}{12}\left(1+\frac{1}{\ell^*}\right)<\frac14\left(1-\frac{1}{\ell}\right)=\frac{\ell^*}{2\ell},
> \]
> and as \(\log(|q|_{\mathbb C_p})<0\) one gets
> \[
> \frac{1}{12}\left(1+\frac{1}{\ell^*}\right)\cdot\log(|q|_{\mathbb C_p})>
> \frac14\left(1-\frac{1}{\ell}\right)\cdot\log(|q|_{\mathbb C_p})
> =\log\left(|q^{1/2\ell}|_{\mathbb C_p}^{\ell^*}\right).
> \]

## Lean correspondence

Use \(m=\ell^*\), \(k=j+1\) for each Lean index \(j:\mathrm{Fin}\,m\), and \(a=\log|q|_{\mathbb C_p}\). Specialize the existing `AbcAdaptation.Reference.Iut.sum_affine_quadratic` to coefficients \(0,1,0\). For \(m>0\), the gap in the sum of normalized squares is
\[
m-\sum_{k=1}^m(k/m)^2=\frac{(m-1)(4m+1)}{6m}.
\]
The gap is positive for \(m\ge2\) and zero for \(m=1\). Thus the arithmetic step holds for every odd \(\ell\ge5\). The same exponents appear in `ThetaWitnessProduct.scale` in Scene1. Its finite product with a constant place weight gives the corresponding sum of real logarithms. [Existing square-sum proof](/home/admin-wsl/Coq/abc/prove2me_workspace/Theorems/Thm_AbcAdaptation_Reference_Iut_sum_affine_quadratic.lean:25) · [Scene1 exponents](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/ThetaWitnessProduct.lean:23)

The P7 specialization uses the same section, torsion roots and moduli degree weights as the verified P7 formula. The global degree in the denominator equals the sum of the local degrees on the full moduli fiber. The stored moduli algebra map agrees with the composite inclusion for the pointwise P7 construction. The remaining geometric input for the conditional Lean theorem is the bound of the normalized witness average by the hull log volume in that same concrete data. The combined project and axiom review checks both numerical declarations and their same-P7 consequences. [P7 representative weights](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCor312PointRepresentativeWeight.lean:21) · [P7 algebra map](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutPointModuliMap.lean:16)

The exact specialization on `IsSourceP7Variant` keeps the point, prime, q-root family, section and q-pilot inputs from the same witness. The fixed rational Legendre family gives `rhsData.rhs < qPilot.lhs`. The strict numerical comparison on that same bundle gives `qPilot.lhs < normalizedWitnessLogAverage`. The concrete hull therefore fails the needed average-to-volume inequality on this family. [Lean specialization and counterexample](Source_JoshiIISourceP7WitnessCounterexample.lean) · [Independent trilingual readback](independent-readback.md)

| Exclusive MCP-CI review | Source SHA-256 prefix | Exit | Elapsed seconds | CPU seconds (user + system) | Peak process-tree RSS GiB |
| --- | --- | ---: | ---: | ---: | ---: |
| [ci-026524-eff346a4](ci-026524-eff346a4.result.json) | `bb66ec1398f52dfd` | 0 | 87.90 | 84.71 (1.32 + 83.39) | 1.99 |
| [ci-026552-a85c494c](ci-026552-a85c494c.result.json) | `43edf3741afe055d` | 0 | 145.30 | 145.48 (7.95 + 137.53) | 8.14 |
| [ci-026601-d98f8f66](ci-026601-d98f8f66.result.json) | `8ba6cd3fcfe98e35` | 0 | 88.53 | 89.11 (7.29 + 81.82) | 8.20 |

The final review imports Checks, ImportAudit, Act1Scene1 and AxiomAudit. Its eight axiom reports list only `propext`, `Classical.choice` and `Quot.sound`. The compiler reports unused tactics and a local `letI` style warning. MCP-CI supplies process-tree RSS. PSS and the degraded flag are unknown. [Combined review source](ReviewJoshiIISourceP7WitnessCounterexample.lean)
