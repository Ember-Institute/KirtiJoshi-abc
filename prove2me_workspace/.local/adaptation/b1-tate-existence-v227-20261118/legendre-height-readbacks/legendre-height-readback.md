# English

For every supplied Legendre curve provider $P$ and compactly bounded set $K$, `legendreHeight P K` proves `LegendreHeightHyp P K`. Put $c=K.c$, $V=K.V$, and $H=\mathrm{htCan}$. Its explicit bounds, valid for every $x\in K$, are

$$P.h(x)/6\leq H(x)+\log(2)/3,$$
$$H(x)\leq P.h(x)/6+c|V|+c+\log(2)/3.$$

To prove them, write $\lambda=\mathrm{gen}(x)$ and $d=[\mathbb Q(\lambda):\mathbb Q]$. Let $h$ denote the relative logarithmic height. The provider normalization gives $P.h(x)=h_{\mathrm{fin}}(j(\lambda))/d$, while $H(x)=h(\lambda)/d$. The proof compares $h_{\mathrm{fin}}(j(\lambda))$ with twice the sum of the finite heights of $\lambda$, $\lambda^{-1}$, and $(\lambda-1)^{-1}$. Compact bounds control the finite places over $V$ and the archimedean contributions. Height inversion and the height bound for addition introduce the term $\log(2)/3$. If $j(\lambda)=0$, the proof uses $\lambda^6=1$, so both normalized heights vanish. Division by $d>0$ gives the stated constants without a degree bound.

Mochizuki's IUT IV, Corollary 2.2(i), supplies the paper context. Its proof compares the normalized degree of the q-divisor with the height of the moduli divisor at infinity on a compactly bounded set. The degree-six pullback to the Legendre line then gives the factor $1/6$. The Lean theorem establishes this component through explicit finite and archimedean estimates; its conclusion is the height comparison for the supplied $P$.

# 简体中文

对每个给定的 Legendre 曲线供应数据 $P$ 和【译名待定：compactly bounded subset】 $K$，`legendreHeight P K` 证明 `LegendreHeightHyp P K`。令 $c=K.c$、$V=K.V$、$H=\mathrm{htCan}$。对每个 $x\in K$，证明给出的显式界为

$$P.h(x)/6\leq H(x)+\log(2)/3,$$
$$H(x)\leq P.h(x)/6+c|V|+c+\log(2)/3.$$

证明中记 $\lambda=\mathrm{gen}(x)$、$d=[\mathbb Q(\lambda):\mathbb Q]$。记相对对数高度为 $h$。供应数据的归一化给出 $P.h(x)=h_{\mathrm{fin}}(j(\lambda))/d$，且 $H(x)=h(\lambda)/d$。先将 $h_{\mathrm{fin}}(j(\lambda))$ 与 $\lambda$、$\lambda^{-1}$、$(\lambda-1)^{-1}$ 的有限高度之和的两倍比较。紧有界条件控制 $V$ 上方的有限处与阿基米德部分。高度的取逆不变性及加法估计给出 $\log(2)/3$ 项。若 $j(\lambda)=0$，则利用 $\lambda^6=1$ 说明两个归一化高度均为零。最后除以正数 $d$，得到上述常数，无需次数上界。

论文背景来自 望月新一《集合论多宇宙间算术 Teichmüller 理论》第四篇推论 2.2(i)。原文证明在【译名待定：compactly bounded subset】上比较 q-除子的归一化次数与模空间无穷远除子的高度，再利用 Legendre 参数直线上次数为六的拉回得到 $1/6$。Lean 定理通过显式的有限处与阿基米德估计证明其中这一部分，结论是给定 $P$ 的高度比较。

# 日本語

与えられた任意の Legendre 曲線の供給データ $P$ とコンパクト有界集合 $K$ に対し、`legendreHeight P K` は `LegendreHeightHyp P K` を証明する。$c=K.c$、$V=K.V$、$H=\mathrm{htCan}$ とおく。すべての $x\in K$ に対して、次の明示的な評価を得る。

$$P.h(x)/6\leq H(x)+\log(2)/3,$$
$$H(x)\leq P.h(x)/6+c|V|+c+\log(2)/3.$$

証明では $\lambda=\mathrm{gen}(x)$、$d=[\mathbb Q(\lambda):\mathbb Q]$ とおく。相対対数高さを $h$ とする。供給データの正規化により $P.h(x)=h_{\mathrm{fin}}(j(\lambda))/d$ となり、$H(x)=h(\lambda)/d$ である。まず $h_{\mathrm{fin}}(j(\lambda))$ を、$\lambda$、$\lambda^{-1}$、$(\lambda-1)^{-1}$ の有限高さの和の二倍と比較する。コンパクト有界性は $V$ の上の有限素点とアルキメデス部分を制御する。逆数による高さの不変性と加法の評価から $\log(2)/3$ の項を得る。$j(\lambda)=0$ の場合は $\lambda^6=1$ を用い、二つの正規化された高さが零であることを示す。最後に正数 $d$ で割ることで上の定数を得る。次数の上限は必要ない。

論文上の背景は 望月新一の「宇宙際 Teichmüller 理論」第 IV 論文、系 2.2(i) にある。その証明は、コンパクト有界集合上で q-因子の正規化次数とモジュライ空間の無限遠因子の高さを比較する。Legendre パラメータ直線への引き戻しの次数が六であることから、係数 $1/6$ を得る。Lean の定理は、有限素点とアルキメデス部分の明示的な評価によって、この高さ比較を与えられた $P$ に対して証明する。
