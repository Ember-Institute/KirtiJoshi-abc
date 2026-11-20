# English

Fix an actual Legendre curve provider $P$ and a compactly bounded set $K$. Write $h_P(x)=P.h(x)$ for the provider's normalized Tate height and $H(x)=\mathrm{htCan}(x)$ for the absolute logarithmic Weil height. `LegendreHeightHyp P K` means that $h_P/6$ and $H$ have bounded discrepancy on $K$. In Lean, this is a pair of statements: there exist real constants $C_1,C_2$ such that, for every $x\in K$, $h_P(x)/6\leq H(x)+C_1$ and $H(x)\leq h_P(x)/6+C_2$. The constants are uniform in $x$; the definition imposes no bound on the degree of $x$.

This is the all-primes Tate-height comparison in Mochizuki's IUT IV, Corollary 2.2(i). Its proof explains the factor $1/6$: the pullback of the moduli divisor at infinity to the Legendre line has degree $6$, whereas $\omega_X(D)$ has degree $1$. The definition records this comparison for a supplied provider. It does not assert the existence of that provider.

# 简体中文

固定一个实际的 Legendre 曲线供应数据 $P$ 和一个紧致有界子集 $K$。记 $h_P(x)=P.h(x)$ 为该供应数据 的归一化 Tate 高度，$H(x)=\mathrm{htCan}(x)$ 为绝对对数 Weil 高度。`LegendreHeightHyp P K` 表示 $h_P/6$ 与 $H$ 在 $K$ 上具有有界差异。在 Lean 中，它是两条陈述的合取：存在实常数 $C_1,C_2$，使每个 $x\in K$ 都满足 $h_P(x)/6\leq H(x)+C_1$ 和 $H(x)\leq h_P(x)/6+C_2$。常数对 $x$ 一致；定义没有限制 $x$ 的次数。

这对应 望月新一《集合论多宇宙间算术 Teichmüller 理论》第四篇推论 2.2(i) 中包含全部有限处的 Tate 高度比较。原文证明解释了 $1/6$ 的来源：模空间无穷远除子在 Legendre 参数直线上的拉回次数为 $6$，而 $\omega_X(D)$ 的次数为 $1$。该定义针对给定的 供应数据记录此比较，并未断言这组供应数据存在。

# 日本語

実際の Legendre 曲線の供給データ $P$ とコンパクト有界集合 $K$ を固定する。$h_P(x)=P.h(x)$ を 供給データの正規化された Tate 高さ、$H(x)=\mathrm{htCan}(x)$ を絶対対数 Weil 高さとする。`LegendreHeightHyp P K` は、$h_P/6$ と $H$ の差が $K$ 上で有界であることを表す。Lean では、実数定数 $C_1,C_2$ が存在し、すべての $x\in K$ に対して $h_P(x)/6\leq H(x)+C_1$ および $H(x)\leq h_P(x)/6+C_2$ が成り立つ、という二つの命題の連言である。定数は $x$ に依存せず、この定義は $x$ の次数に上限を設けない。

これは 望月新一の「宇宙際 Teichmüller 理論」第 IV 論文、系 2.2(i) における、すべての有限素点を含む Tate 高さの比較に対応する。その証明では、係数 $1/6$ の理由が説明される。モジュライ空間の無限遠因子を Legendre パラメータ直線へ引き戻すと次数は $6$ であり、$\omega_X(D)$ の次数は $1$ である。この定義は与えられた供給データ に対する比較を記録し、その 供給データの存在自体は主張しない。

[Local LegendreHeightHyp](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_LegendreHeightHyp.lean#L22) · [Source LegendreHeightHyp](../../../../../refer/iut/Iut/Tripod/CurveFacts.lean#L403)
