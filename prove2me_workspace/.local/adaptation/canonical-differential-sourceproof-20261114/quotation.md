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

These quotations give the original-paper canonical and log-canonical context. The arbitrary-transcendental differential-change statement and the explicit Belyi coefficient identity are exact formal-source auxiliaries from Belyi/CurveField/Canonical.lean:144,159 and BelyiRelation.lean:85; they are not quoted verbatim from this paper. The current statements retain every supplied canonical divisor and cusp-finiteness proof and all proper places, including poles. The formal source uses positive principal orders in this geometric composition.
