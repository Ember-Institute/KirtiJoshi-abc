# English

Fix a point of the projective line with $0,1,\infty$ removed, with algebraic coordinate $\lambda$. Assume the sets of $3$-torsion points and $5$-torsion points of the Legendre curve over $\overline{\mathbb Q}$ are finite. Let $E_\lambda/F_\lambda$ be the curve chosen by `curveOf` with those finiteness proofs. Write $L$ for the intermediate field generated over $\mathbb Q$ by the image of $\lambda$ in $F_\lambda$. Write $M=\mathbb Q(j(E_\lambda))$ for the field of moduli in $F_\lambda$ and $\deg(\lambda)$ for the degree of the minimal polynomial of $\lambda$ over $\mathbb Q$.

- `fieldOfModuli_le` gives the inclusion $M\subseteq L$.
- `isIntegral_genC` states that the image of $\lambda$ in $F_\lambda$ satisfies a monic polynomial over $\mathbb Q$.
- `finrank_adjoin_genC` gives $[L:\mathbb Q]=\deg(\lambda)$.
- `dmod_le` gives $[M:\mathbb Q]\leq\deg(\lambda)$.

# 简体中文

固定射影直线去掉 $0,1,\infty$ 后的一个点，将其代数坐标记作 $\lambda$。假设该 Legendre 曲线在 $\overline{\mathbb Q}$ 上的 $3$ 阶挠点集和 $5$ 阶挠点集均有限。令 $E_\lambda/F_\lambda$ 为 `curveOf` 使用这两个有限性证明选定的曲线。设 $L$ 是 $F_\lambda$ 中由 $\lambda$ 的像在 $\mathbb Q$ 上生成的中间域，$M=\mathbb Q(j(E_\lambda))$ 是 $F_\lambda$ 中的模域，$\deg(\lambda)$ 是 $\lambda$ 在 $\mathbb Q$ 上的极小多项式次数。

- `fieldOfModuli_le` 给出包含关系 $M\subseteq L$。
- `isIntegral_genC` 断言 $\lambda$ 在 $F_\lambda$ 中的像满足一个系数在 $\mathbb Q$ 中的首一多项式。
- `finrank_adjoin_genC` 给出 $[L:\mathbb Q]=\deg(\lambda)$。
- `dmod_le` 给出 $[M:\mathbb Q]\leq\deg(\lambda)$。

# 日本語

射影直線から $0,1,\infty$ を除いた曲線上の点を一つ固定し、その代数的な座標を $\lambda$ とする。この Legendre 曲線の $\overline{\mathbb Q}$ 上の $3$ 等分点の集合と $5$ 等分点の集合がともに有限であると仮定する。これらの有限性の証明を用いて `curveOf` が定める曲線を $E_\lambda/F_\lambda$ とする。$L$ を $F_\lambda$ における $\lambda$ の像が $\mathbb Q$ 上生成する中間体とし、$M=\mathbb Q(j(E_\lambda))$ を $F_\lambda$ 内のモジュライ体とする。$\deg(\lambda)$ は $\lambda$ の $\mathbb Q$ 上の最小多項式の次数とする。

- `fieldOfModuli_le` は包含関係 $M\subseteq L$ を与える。
- `isIntegral_genC` は $F_\lambda$ における $\lambda$ の像が $\mathbb Q$ 係数のモニック多項式を満たすことを述べる。
- `finrank_adjoin_genC` は $[L:\mathbb Q]=\deg(\lambda)$ を与える。
- `dmod_le` は $[M:\mathbb Q]\leq\deg(\lambda)$ を与える。
