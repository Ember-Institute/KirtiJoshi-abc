# English

Fix an actual Legendre curve provider $P$ and a compactly bounded subset $K$. `curveInputs_htCan_equiv P K` proves that $P.h/6$ and the fixed absolute logarithmic Weil height $\mathrm{htCan}$ have bounded discrepancy on all of $K$. Equivalently, there are real constants $C_1,C_2$ such that every $x\in K$ satisfies

$$P.h(x)/6\leq\mathrm{htCan}(x)+C_1,\qquad \mathrm{htCan}(x)\leq P.h(x)/6+C_2.$$

The proof is `legendreHeight P K`. This field has no degree-bound input. Its exact target uses `tripodTheory.cbsSet K` and `tripodTheory.htCan tripodTheory.tripod`; these reduce to the existing set and height.

The source `curveInputs` stores this proof as `htCan_equiv`, and `toCorollary22Inputs` forwards it unchanged. The Northcott field uses its second inequality to transfer a bound on $P.h$ to a Weil-height bound. `statementII_of_cor312` uses that same inequality to transfer its high-height estimate to $\mathrm{htCan}$ outside the finite exceptional set. Mochizuki's IUT IV, Corollary 2.2(i), supplies the paper comparison. Its proof derives the factor $1/6$ from the degree-six pullback of the divisor at infinity to the Legendre line and the degree-one bundle $\omega_X(D)$.

# 简体中文

固定一个实际的 Legendre 曲线供应数据 $P$ 和一个【译名待定：compactly bounded subset】$K$。`curveInputs_htCan_equiv P K` 证明 $P.h/6$ 与固定的绝对对数 Weil 高度 $\mathrm{htCan}$ 在整个 $K$ 上的差异有界。等价地，存在实常数 $C_1,C_2$，使每个 $x\in K$ 都满足

$$P.h(x)/6\leq\mathrm{htCan}(x)+C_1,\qquad \mathrm{htCan}(x)\leq P.h(x)/6+C_2.$$

证明直接使用 `legendreHeight P K`。该字段没有次数上界输入。其精确目标使用 `tripodTheory.cbsSet K` 与 `tripodTheory.htCan tripodTheory.tripod`，二者分别归约为既有的集合与高度。

源码的 `curveInputs` 将此证明存入 `htCan_equiv`，再由 `toCorollary22Inputs` 原样传递。Northcott 字段使用第二条不等式，将 $P.h$ 的上界转换为 Weil 高度的上界。`statementII_of_cor312` 也使用这一方向，将有限例外集外的高高度估计转换为 $\mathrm{htCan}$ 的估计。论文比较来自 望月新一《集合论多宇宙间算术 Teichmüller 理论》第四篇推论 2.2(i)。其证明利用无穷远除子在 Legendre 参数直线上的拉回次数为六、而 $\omega_X(D)$ 的次数为一，得到系数 $1/6$。

# 日本語

実際の Legendre 曲線の供給データ $P$ とコンパクト有界部分集合$K$ を固定する。`curveInputs_htCan_equiv P K` は、$P.h/6$ と固定された絶対対数 Weil 高さ $\mathrm{htCan}$ の差が、$K$ 全体で有界であることを証明する。同値な表現として、実数定数 $C_1,C_2$ が存在し、すべての $x\in K$ に対して

$$P.h(x)/6\leq\mathrm{htCan}(x)+C_1,\qquad \mathrm{htCan}(x)\leq P.h(x)/6+C_2$$

が成り立つ。証明は `legendreHeight P K` を用いる。このフィールドには次数上限の入力がない。正確な型には `tripodTheory.cbsSet K` と `tripodTheory.htCan tripodTheory.tripod` が現れ、それぞれ既存の集合と高さに帰着する。

ソースの `curveInputs` はこの証明を `htCan_equiv` に格納し、`toCorollary22Inputs` がそのまま渡す。Northcott フィールドは第二の不等式により、$P.h$ の上限を Weil 高さの上限に移す。`statementII_of_cor312` も同じ方向を使い、有限例外集合の外で高さに関する評価を $\mathrm{htCan}$ の評価へ移す。論文上の比較は 望月新一の「宇宙際 Teichmüller 理論」第 IV 論文、系 2.2(i) にある。その証明は、Legendre パラメータ直線に引き戻した無限遠因子の次数が六であり、$\omega_X(D)$ の次数が一であることから係数 $1/6$ を得る。
