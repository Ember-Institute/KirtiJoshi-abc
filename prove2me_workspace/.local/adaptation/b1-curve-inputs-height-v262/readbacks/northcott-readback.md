# English

`NorthcottHyp` states that, for every natural number $d$ and real number $H$, there are finitely many tripod points $x$ with $[\mathbb Q(x):\mathbb Q]\leq d$ and $\mathrm{htCan}(x)\leq H$. The points range over the fixed algebraic closure; their fields of definition may vary. The draft theorem `northcottHyp` obtains this statement from the existing concrete `boundedDegreeFiniteness` theorem.

For a compactly bounded subset $K$, `northcott` restricts this finite set to $K$. The generic theorem `northcott_of_equiv` also accepts a function $h$ whose one-sixth multiple has bounded discrepancy from $\mathrm{htCan}$ on $K$. It uses the inequality $\mathrm{htCan}(x)\leq h(x)/6+C$. If $h(x)\leq H$, then $\mathrm{htCan}(x)\leq H/6+C$, so the required set is a subset of a Northcott finite set. The projection `DiscrepancyEquiv.ge` supplies this direction of the comparison.

For an actual provider $P$, `curveInputs_northcott P K d H` applies this argument with $h=P.h$ and `legendreHeight P K`. It proves finiteness of

$$\{x\in K:[\mathbb Q(x):\mathbb Q]\leq d,\ P.h(x)\leq H\}.$$

This is the exact type of `CurveInputs.northcott` when the constructor chooses `h := P.h`. The source forwards it to `Corollary22Inputs.northcott`. `statementII_of_cor312` uses it to make the low-height part of its exceptional set finite. The provider $P$ remains an input; no single field of definition is fixed, and no positivity assumption on $H$ is required. Mochizuki's *Arithmetic Elliptic Curves in General Position*, Proposition 1.4(iv), gives the original bounded-degree height-finiteness context.

# 简体中文

`NorthcottHyp` 表示：对每个自然数 $d$ 和实数 $H$，满足 $[\mathbb Q(x):\mathbb Q]\leq d$ 及 $\mathrm{htCan}(x)\leq H$ 的 三足点 $x$ 只有有限多个。点取自固定的代数闭包，其定义域可以变化。定理 `northcottHyp` 由既有的具体定理 `boundedDegreeFiniteness` 得到这一陈述。

对一个【译名待定：compactly bounded subset】$K$，`northcott` 将上述有限集限制到 $K$。一般定理 `northcott_of_equiv` 还接收函数 $h$，要求 $h/6$ 与 $\mathrm{htCan}$ 在 $K$ 上的差异有界。它使用 $\mathrm{htCan}(x)\leq h(x)/6+C$ 这一方向。若 $h(x)\leq H$，则 $\mathrm{htCan}(x)\leq H/6+C$，因此目标集合包含于一个 Northcott 有限集中。投影 `DiscrepancyEquiv.ge` 提供所需方向。

给定实际的曲线供应数据 $P$，`curveInputs_northcott P K d H` 取 $h=P.h$，并使用 `legendreHeight P K`，证明

$$\{x\in K:[\mathbb Q(x):\mathbb Q]\leq d,\ P.h(x)\leq H\}$$

是有限集。这恰是构造器选取 `h := P.h` 时 `CurveInputs.northcott` 的字段类型。源码将它传给 `Corollary22Inputs.northcott`，随后 `statementII_of_cor312` 用它证明例外集中低高度部分的有限性。$P$ 仍是输入；这里没有固定单一的定义域，也不要求 $H$ 为正。望月新一《处于一般位置的算术椭圆曲线》命题 1.4(iv) 提供原文中次数与高度同时有界时的有限性背景。

# 日本語

`NorthcottHyp` は、任意の自然数 $d$ と実数 $H$ に対し、$[\mathbb Q(x):\mathbb Q]\leq d$ かつ $\mathrm{htCan}(x)\leq H$ を満たす tripod の点 $x$ が有限個であることを表す。点は固定された代数閉包内を動き、定義体は変化してよい。定理 `northcottHyp` は、既存の具体的な定理 `boundedDegreeFiniteness` からこの命題を得る。

コンパクト有界部分集合$K$ に対し、`northcott` はこの有限集合を $K$ に制限する。一般定理 `northcott_of_equiv` は、$h/6$ と $\mathrm{htCan}$ の差が $K$ 上で有界となる関数 $h$ も受け取る。必要な方向は $\mathrm{htCan}(x)\leq h(x)/6+C$ である。$h(x)\leq H$ ならば $\mathrm{htCan}(x)\leq H/6+C$ となるため、対象の集合は Northcott の有限集合に含まれる。射影 `DiscrepancyEquiv.ge` がこの方向の比較を与える。

実際の曲線の供給データ $P$ が与えられると、`curveInputs_northcott P K d H` は $h=P.h$ と `legendreHeight P K` を用いて、集合

$$\{x\in K:[\mathbb Q(x):\mathbb Q]\leq d,\ P.h(x)\leq H\}$$

の有限性を証明する。これは構成子が `h := P.h` とした場合の `CurveInputs.northcott` の正確な型である。ソースはこれを `Corollary22Inputs.northcott` に渡す。その後、`statementII_of_cor312` が例外集合のうち高さが低い部分の有限性に用いる。$P$ は入力として必要である。単一の定義体は固定せず、$H$ の正値性も要求しない。望月新一の *Arithmetic Elliptic Curves in General Position*、命題 1.4(iv) が、次数と高さを同時に制限した有限性の原文上の背景を与える。
