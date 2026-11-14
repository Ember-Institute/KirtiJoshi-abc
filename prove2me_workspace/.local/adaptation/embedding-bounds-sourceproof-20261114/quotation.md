Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position*, February 2009.

Official PDF: https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf

Local PDF: `/home/admin-wsl/Coq/abc/refer/Mochizuki/Arithmetic Elliptic Curves in General Position.pdf`

SHA-256: `b9dc115af61dca7fe434332ebafddf6a376a9e2926dad4e1ea2dcc0d2441f768`

Primary quotation — Example 1.3(ii), printed page 6 / PDF page 6:

> Then let us write
> $$
> \mathcal{K}_V \subseteq X(\overline{\mathbb{Q}})
> $$
> for the subset of points $x \in X(F) \subseteq X(\overline{\mathbb{Q}})$, where $[F : \mathbb{Q}] < \infty$, such that for each $v \in V^{\mathrm{arc}}$ (respectively, $v \in V^{\mathrm{non}}$), the set of $[F : \mathbb{Q}]$ points of $X^{\mathrm{arc}}$ (respectively, $X(\overline{\mathbb{Q}}_v)$) determined by $x$ is contained in $\mathcal{K}_v$. We shall refer to a subset $X(\overline{\mathbb{Q}})$ obtained [i.e., as a “$\mathcal{K}_V$”] in this fashion as a compactly bounded subset, to $V$ as the support of the compactly bounded subset, and to the “$\mathcal{K}_v$” as the bounding domains of the compactly bounded subset.

Bounding-domain setup — Example 1.3(ii), printed pages 5–6 / PDF pages 5–6:

> (ii) Let us refer to a compact subset of a topological space which is equal to the closure of its interior as a compact domain. Let $V \subseteq \mathbb{V}(\mathbb{Q})$ be a finite subset that contains $\mathbb{V}(\mathbb{Q})^{\mathrm{arc}}$. For each $v \in V^{\mathrm{arc}} \overset{\mathrm{def}}{=} V \bigcap \mathbb{V}(\mathbb{Q})^{\mathrm{arc}}$ (respectively, $v \in V^{\mathrm{non}} \overset{\mathrm{def}}{=} V \bigcap \mathbb{V}(\mathbb{Q})^{\mathrm{non}}$), let
> $$
> \mathcal{K}_v \subseteq X^{\mathrm{arc}} \quad (\text{respectively, }\mathcal{K}_v \subseteq X(\overline{\mathbb{Q}}_v))
> $$
> be a nonempty $\iota_X$-stable compact domain (respectively, a nonempty $\operatorname{Gal}(\overline{\mathbb{Q}}_v/\mathbb{Q}_v)$-stable subset whose intersection with each $X(K) \subseteq X(\overline{\mathbb{Q}}_v)$, for $K \subseteq \overline{\mathbb{Q}}_v$ a finite extension of $\mathbb{Q}_v$, is a compact domain in $X(K)$) such that $\mathcal{K}_v \neq X^{\mathrm{arc}}$ (respectively, $\mathcal{K}_v \neq X(\overline{\mathbb{Q}}_v)$).

Related terminology — Definition 1.2(ii), printed page 5 / PDF page 5:

> The relation “$\approx$” clearly defines an equivalence relation on the set of functions $\mathcal{F} \to \mathbb{R}$; we shall refer to an equivalence class relative to this equivalence relation as a(n) [$\mathcal{F}$-]BD-class [i.e., “bounded discrepancy class”].

Example 1.3(ii) supplies the original-paper compactness context: the condition concerns every local point determined by x, expressed by the paper as the set of [F : Q] points. Interpreting these points as the images under all embeddings F → Qbar_v is an explanation of the quotation, not additional quoted wording. The exact arithmetic finite-place exponent bridge for the current auxiliary lemma is supplied by the Heights source code; this paper passage does not state that bridge or the auxiliary lemma verbatim. Definition 1.2(ii) concerns bounded discrepancy classes and does not itself define the all-embeddings compactness condition.

Transcription: English wording checked visually against the PDF; mathematics rendered as LaTeX; line breaks and emphasis normalized. The apparent missing “of” in “a subset X(Qbar)” is present in the original and is preserved. The PDF title page says February 2009; do not inherit the March 2008 version label from the local Markdown. Existing official PDF was reused; no network download or compilation was performed.
