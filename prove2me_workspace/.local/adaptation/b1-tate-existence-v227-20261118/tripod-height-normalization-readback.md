# English

For the Legendre curve with parameter $\lambda$, the affine rational points killed by multiplication by two have $y=0$ and $x\in\{0,1,\lambda\}$. Its $j$-invariant is a rational expression in $\lambda$. The tripodal field, generated over $\mathbb Q$ by those three coordinates and $j$, therefore identifies with $\mathbb Q(\lambda)$, and the field isomorphism sends the curve's $j$ to that same expression in the parameter field.

The sum of local contributions equals the finite height of $j$ divided by the absolute degree of the curve's field of definition. Transporting $j$ from the tripodal field to the curve's field multiplies its finite height by the relative field degree. The same degree occurs in the denominator, so it cancels. The resulting height is exactly `auxiliaryHeight`.

Paper context: Mochizuki, *Inter-universal Teichmüller Theory IV*, Theorem 1.10 and Proposition 1.8; *Arithmetic Elliptic Curves in General Position*, Definition 3.3. Formal sources: `Iut/Concrete/Invariants.lean:198`, `Iut/Tripod/Legendre.lean:30`, `Iut/Tripod/CurveFacts.lean:164`, `Iut/Tripod/TwoAdic.lean:384` and `Iut/Tripod/Height.lean:249,540,603`. The equalities with `auxiliaryHeight` are project adapters.

# 简体中文

在参数为 $\lambda$ 的 Legendre 曲线上，倍乘二得到零的仿射有理点恰好是纵坐标为零、横坐标为 $0$、$1$ 或 $\lambda$ 的点。曲线的 $j$ 不变量是 $\lambda$ 的有理式。因此，由三个横坐标与 $j$ 在有理数域上生成的三足域同构于 $\mathbb Q(\lambda)$；该同构把曲线的 $j$ 不变量送到参数域中的同一有理式。

局部贡献之和等于 $j$ 的有限高度除以曲线定义域在有理数域上的次数。把 $j$ 从三足域送入曲线定义域时，有限高度乘以相对扩张次数。分母也乘以同一次数，约去之后就得到项目中已定义的辅助高度。

论文背景见望月新一《集合论多宇宙间算术 Teichmüller 理论》第四篇定理 1.10、命题 1.8，以及《处于一般位置的算术椭圆曲线》定义 3.3。形式证明的位置见英文段落；与辅助高度的等式由本项目接入。

# 日本語

パラメータ $\lambda$ の Legendre 曲線において、二倍すると零点になるアフィン有理点は、$y$ 座標が零で $x$ 座標が $0$、$1$ または $\lambda$ である点に限る。曲線の $j$ 不変量は $\lambda$ の有理式である。したがって、これらの $x$ 座標と $j$ 不変量が有理数体上で生成する体は $\mathbb Q(\lambda)$ と同型であり、この同型による $j$ 不変量の像はパラメータの体における同じ有理式で表される。

局所寄与の和は、$j$ 不変量の有限高さを曲線の定義体の絶対拡大次数で割った値に等しい。$j$ 不変量を生成体から定義体に移すと、有限高さと分母に同じ相対拡大次数が掛かる。これを約分すると、既に定義した補助高さを得る。

論文の背景については、望月新一の *Inter-universal Teichmüller Theory IV* の定理 1.10 および命題 1.8 と、*Arithmetic Elliptic Curves in General Position* の定義 3.3 を参照。形式証明の出典は英語節のとおりである。補助高さとの等式は本プロジェクトで接続したものである。
