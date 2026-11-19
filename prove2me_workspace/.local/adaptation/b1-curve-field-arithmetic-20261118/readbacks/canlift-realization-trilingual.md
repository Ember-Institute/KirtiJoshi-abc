# Realizing a cover in a fixed algebraic closure

Upstream orbicurve-cores revision `61616dcd77fbe45c083a8ebfa7cc80728f86e841`. Adapted source SHA-256 `8c25ec780b34cebb7db8ead4e018dc10e5c50339c7e38a32dd47378f2692327b`. The MCP-CI leaf check and the build with Lean object output both exited with code 0 and reported four tactic suggestions each. [Adapted source](../../../../Solutions/Source_ReferenceIutCanLiftRealization.lean#L6) · [Leaf check ci-022870-3c9c8d72](../receipts/round-ci-022870-3c9c8d72-result.json) · [Leaf build ci-022877-123f64ff](../receipts/round-ci-022877-123f64ff-result.json)

## English

For a field $k$, take $\Omega=\overline{\operatorname{Frac}(k[X])}$ and let $t$ be the image of $X$ in $\Omega$. The element $t$ is transcendental over $k$. For an intermediate field $F$ of $\Omega/k(t)$, let $R_F$ be the integral closure of $k[t]$ in $F$. The normalization ring for the bottom field $k(t)$ is $k[t]$ because $k[t]$ is integrally closed. [Ambient field and parameter](../../../../Solutions/Source_ReferenceIutCanLiftRealization.lean#L38) · [Bottom normalization](../../../../Solutions/Source_ReferenceIutCanLiftRealization.lean#L61)

Let $\phi:Z\to C$ be a cover of affine orbicurve presentations over $k$, with coordinate-ring map $\phi^\#:C.A\to Z.A$. The theorem `exists_realization` gives intermediate fields $F\subseteq L$, both finite over $k(t)$. It gives $k$-algebra isomorphisms $\psi_C:C.A\simeq R_F$ and $\psi_Z:Z.A\simeq R_L$. The isomorphisms make the coordinate-ring square commute. For every $a\in C.A$,

$$
\psi_Z(\phi^\#(a))=\iota_{F,L}(\psi_C(a)),
$$

where $\iota_{F,L}:R_F\hookrightarrow R_L$ is the inclusion induced by $F\subseteq L$. The adapted theorem works over any field $k$. The original theorem gives the same square over $\mathbb C$. [Cover structure](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/AffineOrbicurvePresentation.lean#L54) · [Realization theorem](../../../../Solutions/Source_ReferenceIutCanLiftRealization.lean#L133) · [Original theorem](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/U2/Realize.lean#L105)

Noether normalization gives $c_0\in C.A$ transcendental over $k$ such that $C.A$ is integral over $k[c_0]$. Evaluation at $c_0$ gives the injective, integral map `gBase` from $k[t]$ to $C.A$. The normalization embedding lemma uses this map to realize $C.A$ as $R_F$. It embeds the fraction field in $\Omega$ and uses finite generation to show that the image field is finite over $k(t)$. Integral closedness identifies the image of the ring with the integral closure of $k[t]$. Apply the same lemma to $\phi^\#\circ\psi_C^{-1}:R_F\to Z.A$. This realizes $Z.A$ as $R_L$ and identifies the last map with $\iota_{F,L}$. [Noether normalization](../../../../Solutions/Source_ReferenceIutCanLiftNoether.lean#L34) · [Evaluation map](../../../../Solutions/Source_ReferenceIutCanLiftRealization.lean#L88) · [Normalization embedding](../../../../Solutions/Source_ReferenceIutCanLiftNormalizationEmbed.lean#L67) · [Second application](../../../../Solutions/Source_ReferenceIutCanLiftRealization.lean#L145)

The image of each rational function is a ratio of polynomials evaluated at $t$ and belongs to $k(t)$ inside $\Omega$. Transfer the algebraicity equations along this map to obtain algebraicity of $\Omega$ over the realized $k(t)$. All the minimal polynomials split in the algebraically closed field $\Omega$, which gives `normal_ratFuncClosure`. The unramified Galois closure construction uses the realization square to take the normal closure of $L$ inside this ambient field. [Normality](../../../../Solutions/Source_ReferenceIutCanLiftRealization.lean#L177) · [Original normality argument](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/U2/CoreMap.lean#L69) · [Use in the Galois closure](../../../../Solutions/Source_ReferenceIutCanLiftUnramifiedClosure.lean#L118)

MCP-CI review `ci-022884-1f96e82a` printed only `propext`, `Classical.choice`, and `Quot.sound` for `exists_realization` and `normal_ratFuncClosure`. [Review source](../ReviewCanLiftRealizationAndQuadraticModel.lean#L10) · [Review receipt](../receipts/round-ci-022884-1f96e82a-result.json)

## 中文

对域 $k$，取 $\Omega=\overline{\operatorname{Frac}(k[X])}$，令 $t$ 为 $X$ 在 $\Omega$ 中的像。$t$ 在 $k$ 上超越。对 $\Omega/k(t)$ 的中间域 $F$，记 $R_F$ 为 $k[t]$ 在 $F$ 中的整闭包。由于 $k[t]$ 整闭，底域 $k(t)$ 的归一化环就是 $k[t]$。 [环境域与参数](../../../../Solutions/Source_ReferenceIutCanLiftRealization.lean#L38) · [底域的归一化环](../../../../Solutions/Source_ReferenceIutCanLiftRealization.lean#L61)

设 $\phi:Z\to C$ 是 $k$ 上仿射轨形曲线表示之间的覆盖，坐标环映射为 $\phi^\#:C.A\to Z.A$。定理 `exists_realization` 给出中间域 $F\subseteq L$，两者均在 $k(t)$ 上有限。定理也给出 $k$-代数同构 $\psi_C:C.A\simeq R_F$ 和 $\psi_Z:Z.A\simeq R_L$。这些同构使坐标环方块交换。对每个 $a\in C.A$，

$$
\psi_Z(\phi^\#(a))=\iota_{F,L}(\psi_C(a)),
$$

其中 $\iota_{F,L}:R_F\hookrightarrow R_L$ 是 $F\subseteq L$ 诱导的包含映射。适配定理适用于任意域 $k$。原定理在 $\mathbb C$ 上给出同一方块。 [覆盖结构](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/AffineOrbicurvePresentation.lean#L54) · [实现定理](../../../../Solutions/Source_ReferenceIutCanLiftRealization.lean#L133) · [原定理](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/U2/Realize.lean#L105)

Noether 归一化给出在 $k$ 上超越的 $c_0\in C.A$，使 $C.A$ 在 $k[c_0]$ 上整。在 $c_0$ 处求值给出从 $k[t]$ 到 $C.A$ 的整且单射的映射 `gBase`。归一化嵌入引理利用此映射将 $C.A$ 实现为 $R_F$。引理把分式域嵌入 $\Omega$，并利用有限生成性证明像域在 $k(t)$ 上有限。整闭性将原环的像识别为 $k[t]$ 的整闭包。再将同一引理用于 $\phi^\#\circ\psi_C^{-1}:R_F\to Z.A$，得到 $Z.A$ 的实现 $R_L$，并将这个复合映射识别为 $\iota_{F,L}$。 [Noether 归一化](../../../../Solutions/Source_ReferenceIutCanLiftNoether.lean#L34) · [求值映射](../../../../Solutions/Source_ReferenceIutCanLiftRealization.lean#L88) · [归一化嵌入](../../../../Solutions/Source_ReferenceIutCanLiftNormalizationEmbed.lean#L67) · [第二次应用](../../../../Solutions/Source_ReferenceIutCanLiftRealization.lean#L145)

每个有理函数的像都是在 $t$ 处求值的两个多项式之比，因而属于 $\Omega$ 中的 $k(t)$。沿此映射传递代数方程，得到 $\Omega$ 在该 $k(t)$ 上代数。所有极小多项式在代数闭域 $\Omega$ 中分裂，由此得到 `normal_ratFuncClosure`。非分歧 Galois 闭包的构造使用实现方块，在同一环境域中取 $L$ 的正规闭包。 [正规性](../../../../Solutions/Source_ReferenceIutCanLiftRealization.lean#L177) · [原正规性证明](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/U2/CoreMap.lean#L69) · [Galois 闭包中的使用](../../../../Solutions/Source_ReferenceIutCanLiftUnramifiedClosure.lean#L118)

MCP-CI 审查 `ci-022884-1f96e82a` 对 `exists_realization` 和 `normal_ratFuncClosure` 各自仅列出公理 `propext`、`Classical.choice` 和 `Quot.sound`。 [审查源码](../ReviewCanLiftRealizationAndQuadraticModel.lean#L10) · [审查回执](../receipts/round-ci-022884-1f96e82a-result.json)

## 日本語

体 $k$ に対し $\Omega=\overline{\operatorname{Frac}(k[X])}$ とし、$\Omega$ における $X$ の像を $t$ とする。$t$ は $k$ 上超越的である。$\Omega/k(t)$ の中間体 $F$ に対し、$R_F$ を $k[t]$ の $F$ における整閉包とする。$k[t]$ は整閉なので、基礎体 $k(t)$ の正規化環は $k[t]$ である。 [周囲の体とパラメータ](../../../../Solutions/Source_ReferenceIutCanLiftRealization.lean#L38) · [基礎体の正規化環](../../../../Solutions/Source_ReferenceIutCanLiftRealization.lean#L61)

$\phi:Z\to C$ を $k$ 上のアフィン・オービ曲線表示の間の被覆とし、座標環の写像を $\phi^\#:C.A\to Z.A$ とする。定理 `exists_realization` は $k(t)$ 上でともに有限な中間体 $F\subseteq L$ を与える。また $k$-代数同型 $\psi_C:C.A\simeq R_F$、$\psi_Z:Z.A\simeq R_L$ を与える。この同型により座標環の図式は可換となる。各 $a\in C.A$ について

$$
\psi_Z(\phi^\#(a))=\iota_{F,L}(\psi_C(a))
$$

が成り立つ。ここで $\iota_{F,L}:R_F\hookrightarrow R_L$ は $F\subseteq L$ が誘導する包含である。適応版の定理は任意の体 $k$ に適用できる。参照元の定理は $\mathbb C$ 上で同じ図式を与える。 [被覆の構造](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/AffineOrbicurvePresentation.lean#L54) · [実現定理](../../../../Solutions/Source_ReferenceIutCanLiftRealization.lean#L133) · [参照元の定理](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/U2/Realize.lean#L105)

Noether 正規化により、$C.A$ が $k[c_0]$ 上整となる $k$ 上超越的な元 $c_0\in C.A$ を取る。$c_0$ での評価は、$k[t]$ から $C.A$ への整かつ単射な写像 `gBase` を与える。正規化の埋め込み補題はこの写像を使って $C.A$ を $R_F$ として実現する。分数体を $\Omega$ に埋め込み、有限生成性から像の体が $k(t)$ 上有限であることを示す。整閉性により、環の像は $k[t]$ の整閉包と一致する。同じ補題を $\phi^\#\circ\psi_C^{-1}:R_F\to Z.A$ に適用し、$Z.A$ を $R_L$ として実現すると、この合成写像は $\iota_{F,L}$ に対応する。 [Noether 正規化](../../../../Solutions/Source_ReferenceIutCanLiftNoether.lean#L34) · [評価写像](../../../../Solutions/Source_ReferenceIutCanLiftRealization.lean#L88) · [正規化の埋め込み](../../../../Solutions/Source_ReferenceIutCanLiftNormalizationEmbed.lean#L67) · [二回目の適用](../../../../Solutions/Source_ReferenceIutCanLiftRealization.lean#L145)

各有理関数の像は $t$ で評価した多項式の商であり、$\Omega$ の中の $k(t)$ に属する。この写像で代数方程式を移すと、$\Omega$ はその $k(t)$ 上代数的である。すべての最小多項式は代数閉体 $\Omega$ で分解するので、`normal_ratFuncClosure` が従う。不分岐 Galois 閉包の構成では、この実現図式を使って同じ周囲の体の中で $L$ の正規閉包を取る。 [正規性](../../../../Solutions/Source_ReferenceIutCanLiftRealization.lean#L177) · [参照元の正規性の証明](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/U2/CoreMap.lean#L69) · [Galois 閉包での使用](../../../../Solutions/Source_ReferenceIutCanLiftUnramifiedClosure.lean#L118)

MCP-CI レビュー `ci-022884-1f96e82a` は、`exists_realization`、`normal_ratFuncClosure` の公理としてそれぞれ `propext`、`Classical.choice`、`Quot.sound` だけを出力した。 [レビューのソース](../ReviewCanLiftRealizationAndQuadraticModel.lean#L10) · [レビュー結果](../receipts/round-ci-022884-1f96e82a-result.json)
