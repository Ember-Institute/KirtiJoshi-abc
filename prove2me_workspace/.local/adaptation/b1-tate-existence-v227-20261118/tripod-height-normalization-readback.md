# Tripodal field and provider height

## English

- Let $x$ be a tripod point with parameter $\lambda\ne0,1$. Given finiteness proofs for its $3$- and $5$-torsion sets, form the Legendre curve $E_\lambda$ over $F_\lambda$. The $F_\lambda$-rational affine points killed by multiplication by $2$ have coordinates $(0,0)$, $(1,0)$ and $(\lambda,0)$. The invariant $j(E_\lambda)$ is a rational expression in $\lambda$. Thus `tripodalFieldOf_eq` identifies two subfields inside $F_\lambda$, namely the field $\mathbb Q(j(E_\lambda),0,1,\lambda)$ and $\mathbb Q(\lambda)$.
- For a supplied curve provider $P$ and a tripod point $x$, let $j_T$ be the Legendre $j$ expression in the tripodal field of the curve supplied by $P$ at $x$. The $\mathbb Q$-algebra isomorphism `tpdEquiv P x` sends this field to the point field $\mathbb Q(\lambda)$ and sends its chosen generator to $\lambda$. The theorem `tpdEquiv_jT` gives the image $j(\lambda)$ of $j_T$ under this same isomorphism.
- The theorem `h_eq_finHeight_div` gives $P.h(x)=h_{\mathrm{fin}}^{\mathbb Q(\lambda)}(j(\lambda))/[\mathbb Q(\lambda):\mathbb Q]$ for every such $P$ and $x$. The finite height of $j$ in $F_\lambda$ equals $[F_\lambda:\mathbb Q]P.h(x)$. Finite height is invariant under the isomorphism of the tripodal field with $\mathbb Q(\lambda)$. The extension to $F_\lambda$ multiplies the finite height and absolute degree by the same relative degree. After cancellation, the quotient is the project's `auxiliaryHeight`.

## 简体中文

- 设 $x$ 为参数 $\lambda\ne0,1$ 的三足点，给定该点的 $3$ 阶、$5$ 阶挠点集的有限性证明，以此在 $F_\lambda$ 上构造 Legendre 曲线 $E_\lambda$。其被倍乘 $2$ 消去的 $F_\lambda$-有理仿射点为 $(0,0)$、$(1,0)$ 和 $(\lambda,0)$，$j(E_\lambda)$ 又是 $\lambda$ 的有理式。`tripodalFieldOf_eq` 因此给出 $F_\lambda$ 内两个子域的等式 $\mathbb Q(j(E_\lambda),0,1,\lambda)=\mathbb Q(\lambda)$。
- 给定曲线供应数据 $P$ 与三足点 $x$，令 $j_T$ 为 $P$ 在 $x$ 处提供的曲线的三足域中的 Legendre $j$ 表达式。$\mathbb Q$-代数同构 `tpdEquiv P x` 将该域映到点域 $\mathbb Q(\lambda)$，并将选定生成元映到 $\lambda$。`tpdEquiv_jT` 证明在同一个同构下，$j_T$ 的像为 $j(\lambda)$。
- 对每个这样的 $P$ 和 $x$，`h_eq_finHeight_div` 给出 $P.h(x)=h_{\mathrm{fin}}^{\mathbb Q(\lambda)}(j(\lambda))/[\mathbb Q(\lambda):\mathbb Q]$。$j$ 在 $F_\lambda$ 中的有限高度等于 $[F_\lambda:\mathbb Q]P.h(x)$。有限高度在三足域与 $\mathbb Q(\lambda)$ 的同构下保持不变，扩张到 $F_\lambda$ 则使有限高度和绝对次数乘上同一个相对扩张次数。约去该次数后即得项目中的 `auxiliaryHeight`。

## 日本語

- $x$ をパラメータ $\lambda\ne0,1$ をもつ三脚の点とする。$3$ と $5$ で消える点の集合の有限性を仮定し、$F_\lambda$ 上の Legendre 曲線 $E_\lambda$ を作る。二倍すると零点になる $F_\lambda$ 上のアフィン有理点は $(0,0)$、$(1,0)$、$(\lambda,0)$ である。また $j(E_\lambda)$ は $\lambda$ の有理式である。`tripodalFieldOf_eq` は $F_\lambda$ の中で $\mathbb Q(j(E_\lambda),0,1,\lambda)=\mathbb Q(\lambda)$ となることを示す。
- 曲線の供給データ $P$ と三脚の点 $x$ に対し、$j_T$ を $P$ が $x$ に与える曲線の三脚体における Legendre の $j$ の式とする。$\mathbb Q$-代数同型 `tpdEquiv P x` はその体を点の体 $\mathbb Q(\lambda)$ に移し、選んだ生成元を $\lambda$ に写す。`tpdEquiv_jT` によると、同じ同型による $j_T$ の像は $j(\lambda)$ である。
- このようなすべての $P$ と $x$ について、`h_eq_finHeight_div` は $P.h(x)=h_{\mathrm{fin}}^{\mathbb Q(\lambda)}(j(\lambda))/[\mathbb Q(\lambda):\mathbb Q]$ を与える。$F_\lambda$ での $j$ の有限高さは $[F_\lambda:\mathbb Q]P.h(x)$ に等しい。三脚体と $\mathbb Q(\lambda)$ の間の同型は有限高さを保つ。$F_\lambda$ への拡大では有限高さと絶対拡大次数に同じ相対拡大次数が掛かる。これを約分すると、プロジェクトの `auxiliaryHeight` を得る。

Paper context appears in Mochizuki’s *Inter-universal Teichmüller Theory IV*, Theorem 1.10 and Proposition 1.8, and *Arithmetic Elliptic Curves in General Position*, Definition 3.3. [IUT IV](../../../../refer/Mochizuki/Inter-universal_Teichmuller_Theory_4.md) · [GenEll](../../../../refer/Mochizuki/Arithmetic_Elliptic_Curves_in_General_Position.md)

[Local tripodal field](../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FieldIdentification.lean#L82) · [Local j-invariant transport](../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_JTransport.lean#L44) · [Local normalized height](../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_HeightNormalization.lean#L23) · [Source tripodal field](../../../../refer/iut/Iut/Tripod/CurveFacts.lean#L241) · [Source j-invariant transport](../../../../refer/iut/Iut/Tripod/Height.lean#L554) · [Source normalized height](../../../../refer/iut/Iut/Tripod/Height.lean#L603)
