# Corollary 2.2 with a uniform lower bound on the selected prime

## English

`c2_of_prime_lower_bound` fixes a natural number $N$ in the original height and geometry context. It takes the original hypotheses on the point $x$ and on the height $h=I.h(x)$, and it requires $N\le\sqrt h$. The prime selection theorem gives a prime $\ell$ in this interval. [Theorem and height hypotheses](Corollary22Inputs_c2.lean#L89) · [Prime selection](../../../../Theorems/Thm_AbcAdaptation_Reference_Iut_LocalHeightData_exists_prime_selection.lean#L124)

$$\sqrt h\le\ell\le10\delta\sqrt h\,\log(2\delta h),\qquad \delta=552960\,d.$$

The proof uses the same prime for (P2)–(P6). It combines the left inequality with $N\le\sqrt h$ to get $N\le\ell$. `ThetaDataExistenceAtLeast` covers each point in $K$ of degree at most $d$ outside `excCore`. For each such point, the prime $\ell$ must satisfy $\ell\ge7$, $N\le\ell$, and the following conditions. [P7 data type](Corollary22Inputs_c2.lean#L69) · [Use of the selected prime](Corollary22Inputs_c2.lean#L233)

- (P2) The prime $\ell$ divides none of the Tate parameter orders at bad places.
- (P3) At each bad place of residue characteristic $\ell$, the Tate parameter order is less than $\sqrt h$.
- (P5) Some bad place has residue characteristic different from $2$ and $\ell$.
- (P6) The mod-$\ell$ representation has image containing $\mathrm{SL}_2(\mathbb F_\ell)$.

For each such point and prime, one witness gives $X$ satisfying the supplied predicate $P$. It gives the invariants of $X$, a Theorem 1.10 certificate, and a local estimate for those invariants. The same witness gives the following relations.

- The prime of $X$ is $\ell$, and its moduli field has degree at most $d$.
- Its $\log Q$ equals the normalized height contribution from places of residue characteristic other than $2$ and $\ell$.
- Its different invariant equals the normalized logarithmic degree of the different for $x$. The logarithmic conductor of $x$ lies between the conductor invariant and that invariant plus $\log(2\ell)$.

The hypothesis `h312` gives `Corollary312Variant X` for each $X$ that satisfies $P(X)$ and $N\le X.\ell$. The proof uses $X.\ell=\ell$ to pass the bound to `h312`. It gives Theorem 1.10 that comparison, the certificate, and the local estimate for the same $X$. The three original conclusions use $\eta$ from the prime-counting certificate and $B=I.B$. [Theorem 1.10 call](Corollary22Inputs_c2.lean#L242) · [The three conclusions](Corollary22Inputs_c2.lean#L100)

$$\frac h6\le(1+\varepsilon_E(\delta,h))(\log\operatorname{Diff}(x)+\log\operatorname{Cond}(x))+40\eta+\frac B3,\qquad
\varepsilon_E(\delta,h)\le1,\qquad
0\le\log\operatorname{Diff}(x)+\log\operatorname{Cond}(x).$$

The original `c2` specializes this proof to $N=0$. The original P7 hypothesis supplies the restricted witness because $0\le\ell$ holds for every natural number $\ell$. Conversely, a restricted P7 witness at $N=0$ supplies the original witness when given $0\le\ell$. The old and restricted comparisons are equivalent at $N=0$ because $0\le X.\ell$ always holds. The nonnegativity of $\sqrt h$ discharges the extra height condition. This specialization recovers the full original `c2` statement. [Original P7 type](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Corollary22.lean#L112) · [Upstream c2](../../../../../refer/iut/Iut/Implication/Corollary22.lean#L386) · [Zero-bound specialization](Corollary22Inputs_c2.lean#L272)

For each compactly bounded set $K$ and positive degree bound $d$, the canonical consumer takes a bound $N(K,d)$ uniform in $x$. It restricts to points in $K$ of degree at most $d$. In that set, it joins the core exceptions with all points of height $h\le N(K,d)^2$. The two sets are finite by the core finiteness assumption and Northcott finiteness. Outside their union, $h>N(K,d)^2$ gives the required square-root bound. The canonical estimate uses the original height threshold and the constant $40\eta+B/3$. [Northcott field](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Corollary22.lean#L53) · [Canonical consumer](Source_TripodCanonicalCorollary22PrimeBound.lean#L31)

The proof uses the fixed comparison between the auxiliary and canonical heights. It chooses a final threshold at least as large as the canonical heights of the finite exceptional set. The existing `StatementII` proof bounds the discrepancy on points at or below that threshold by Northcott finiteness. Thus for each $K$, degree bound $d$, and $\varepsilon>0$, one constant $C$ works for all points in $K$ of degree at most $d$. [Height comparison and threshold](../../../../Definitions/Def_TripodCanonicalHighHeightComposition.lean#L22) · [Finite low-height set](../../../../Definitions/Def_TripodStatementIIComposition.lean#L21) · [StatementII consumer](Source_TripodCanonicalCorollary22PrimeBound.lean#L73)

$$\operatorname{htCan}(x)\le(1+\varepsilon)(\operatorname{logDiff}(x)+\operatorname{logCond}(x))+C.$$

### Square exponents

For a positive integer $m$, the Lean sum runs over the labels $1,\ldots,m$. Put $\ell=2m+1$. For any real number $L$, multiplying by $L/(2\ell)$ gives the second identity below. At a Tate place, take $L=\log|q|$ and $r=|q^{1/(2\ell)}|$, so $L/(2\ell)=\log r$. [Lean identities](../joshi-ii-square-logs/Source_JoshiIINormalizedSquareLogs.lean#L19)

$$S_m=\sum_{j=1}^{m}\frac{j^2}{m^2}=\frac{(m+1)(2m+1)}{6m},\qquad
S_m\frac{L}{2\ell}=\frac{1}{12}\left(1+\frac{1}{m}\right)L.$$

For $m\ge2$, the gap $m-S_m=(m-1)(4m+1)/(6m)$ is positive. Thus $L<0$ gives $m L/(2\ell)<S_m L/(2\ell)$. Equivalently, for $0<r<1$ the comparison is $r^{S_m}>r^m$. Every odd prime $\ell\ge5$ gives $m\ge2$. [Lean log inequality](../joshi-ii-square-logs/Source_JoshiIINormalizedSquareLogs.lean#L52)

For a finite set of places with real weights $a_v$ and real root logs $R_v$, put $A=\sum_v a_vR_v$. The average over the labels of the sums $\sum_v a_v(j/m)^2 R_v$ is $(S_m/m)A$. If $m\ge2$ and $A<0$, this average is strictly greater than $A$. The strict bound uses the sign of the total. [Lean weighted comparison](../joshi-ii-square-logs/Source_JoshiIINormalizedSquareLogs.lean#L65)

### Application to Form 2

Joshi III, Theorem 9.9.1 (Form 1), uses the square exponents from Joshi II, Theorem 9.2.1. Theorem 9.11.1 (Form 2) follows that numerical argument after obtaining a volume bound from a tensor lattice in the theta region. Its statement requires an odd prime $\ell\gg0$ and the global initial theta data. [Form 1, equation (9.9.5)](https://arxiv.org/pdf/2401.13508v4#page=121) · [Form 2, theorem and proof](https://arxiv.org/pdf/2401.13508v4#page=127)

For each $K,d$, the application needs one $N(K,d)$ that works for the whole P7 family. Choose it before the point $x$ and before the data $X$. The comparison must hold for every $X$ with $P_{K,d}(X)$ and $N(K,d)\le X.\ell$. P7 must supply such data for every admissible point and prime with $\ell\ge\max(7,N(K,d))$. Outside the finite set with $h\le N(K,d)^2$, the selected prime satisfies $N(K,d)<\sqrt h\le\ell$. The application still needs the paper theta region, normalized hull volume, the signed $q$-pilot identification, and the Theorem 1.10 local estimate on the same P7 witness. [Canonical consumer](Source_TripodCanonicalCorollary22PrimeBound.lean#L24) · [Conditional volume estimate](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaPaperLogWitnessHull.lean#L125) · [Source comparison](../../b1-curve-field-arithmetic-20261118/readbacks/p7-cor312-source-comparison.md)

## 简体中文

`c2_of_prime_lower_bound` 在原有高度理论和几何接口下固定一个自然数 $N$。对点 $x$ 及其高度 $h=I.h(x)$，它接受原定理的前提，并要求 $N\le\sqrt h$。素数选择定理给出下列区间内的素数 $\ell$。 [定理与高度条件](Corollary22Inputs_c2.lean#L89) · [素数选择](../../../../Theorems/Thm_AbcAdaptation_Reference_Iut_LocalHeightData_exists_prime_selection.lean#L124)

$$\sqrt h\le\ell\le10\delta\sqrt h\,\log(2\delta h),\qquad \delta=552960\,d.$$

证明以同一个 $\ell$ 验证 (P2)–(P6)，并由左侧不等式和 $N\le\sqrt h$ 得到 $N\le\ell$。`ThetaDataExistenceAtLeast` 覆盖 $K$ 中次数至多为 $d$ 且不属于 `excCore` 的各点。对其中每个点，素数 $\ell$ 须满足 $\ell\ge7$、$N\le\ell$ 及下列条件。 [P7 数据类型](Corollary22Inputs_c2.lean#L69) · [选定素数的使用](Corollary22Inputs_c2.lean#L233)

- （P2）素数 $\ell$ 不整除任何坏处的 Tate 参数阶数。
- （P3）每个剩余特征为 $\ell$ 的坏处的 Tate 参数阶数小于 $\sqrt h$。
- （P5）存在一个坏处，其剩余特征既非 $2$ 也非 $\ell$。
- （P6）模 $\ell$ 表示的像包含 $\mathrm{SL}_2(\mathbb F_\ell)$。

对每组符合条件的点和素数，同一个见证给出满足指定谓词 $P$ 的数据 $X$。它还给出 $X$ 的不变量、定理 1.10 的证书及这组不变量的局部估计，并满足以下关系。

- $X$ 所用素数为 $\ell$，其模域次数至多为 $d$。
- $X$ 的 $\log Q$ 等于剩余特征非 $2$ 且非 $\ell$ 的各处的规范化高度贡献。
- $X$ 的不同理想不变量等于点 $x$ 的不同理想的规范化对数次数。$x$ 的对数导子介于导子不变量与该不变量加上 $\log(2\ell)$ 之间。

`h312` 对每个满足 $P(X)$ 且 $N\le X.\ell$ 的 $X$ 给出 `Corollary312Variant X`。证明通过 $X.\ell=\ell$ 把下界传给 `h312`。所得比较与同一个 $X$ 上的证书和局部估计一起进入定理 1.10。设 $\eta$ 为素数计数证书中的常数，$B=I.B$，则得到原来的三个结论。 [定理 1.10 的调用](Corollary22Inputs_c2.lean#L242) · [三个结论](Corollary22Inputs_c2.lean#L100)

$$\frac h6\le(1+\varepsilon_E(\delta,h))(\log\operatorname{Diff}(x)+\log\operatorname{Cond}(x))+40\eta+\frac B3,\qquad
\varepsilon_E(\delta,h)\le1,\qquad
0\le\log\operatorname{Diff}(x)+\log\operatorname{Cond}(x).$$

原 `c2` 取 $N=0$ 调用该证明。原 P7 见证直接给出带零下界的见证，因为额外前提 $0\le\ell$ 自动成立。反向可用 $0\le\ell$ 实例化带零下界的见证来恢复原 P7。两种 `h312` 的对应同样使用自动成立的 $0\le X.\ell$。由 $0\le\sqrt h$ 满足附加高度前提，因此该特化恢复原 `c2` 的完整陈述。 [原 P7 类型](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Corollary22.lean#L112) · [参考 c2](../../../../../refer/iut/Iut/Implication/Corollary22.lean#L386) · [零下界特化](Corollary22Inputs_c2.lean#L272)

对每个紧致有界集 $K$ 和正次数界 $d$，规范消费者取对点 $x$ 统一的下界 $N(K,d)$。在 $K$ 内次数至多为 $d$ 的点中，它将核例外集与满足 $h\le N(K,d)^2$ 的点集合并。核有限性与 Northcott 有限性分别给出这两个集合的有限性。在并集之外，$h>N(K,d)^2$ 蕴含所需的平方根下界。规范估计沿用原高度阈值和常数 $40\eta+B/3$。 [Northcott 字段](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Corollary22.lean#L53) · [规范消费者](Source_TripodCanonicalCorollary22PrimeBound.lean#L31)

证明使用固定的辅助高度与典范高度比较，将有限例外集的典范高度收到最终阈值以下。现有 `StatementII` 证明利用 Northcott 有限性控制典范高度不超过该阈值的点上的差值。于是，对每个 $K$、次数界 $d$ 和 $\varepsilon>0$，存在一个常数 $C$，使下列估计对 $K$ 内所有次数至多为 $d$ 的点成立。 [高度比较和阈值](../../../../Definitions/Def_TripodCanonicalHighHeightComposition.lean#L22) · [低高度有限集](../../../../Definitions/Def_TripodStatementIIComposition.lean#L21) · [StatementII 消费者](Source_TripodCanonicalCorollary22PrimeBound.lean#L73)

$$\operatorname{htCan}(x)\le(1+\varepsilon)(\operatorname{logDiff}(x)+\operatorname{logCond}(x))+C.$$

### 平方指数

对正整数 $m$，Lean 在标签 $1,\ldots,m$ 上求和。令 $\ell=2m+1$。对任意实数 $L$，乘以 $L/(2\ell)$ 即得下列第二个恒等式。在 Tate 处取 $L=\log|q|$ 和 $r=|q^{1/(2\ell)}|$，于是 $L/(2\ell)=\log r$。 [Lean 恒等式](../joshi-ii-square-logs/Source_JoshiIINormalizedSquareLogs.lean#L19)

$$S_m=\sum_{j=1}^{m}\frac{j^2}{m^2}=\frac{(m+1)(2m+1)}{6m},\qquad
S_m\frac{L}{2\ell}=\frac{1}{12}\left(1+\frac{1}{m}\right)L.$$

当 $m\ge2$ 时，差 $m-S_m=(m-1)(4m+1)/(6m)$ 为正。因此 $L<0$ 蕴含 $m L/(2\ell)<S_m L/(2\ell)$。等价地，若 $0<r<1$，则 $r^{S_m}>r^m$。任何奇素数 $\ell\ge5$ 均满足 $m\ge2$。 [Lean 对数不等式](../joshi-ii-square-logs/Source_JoshiIINormalizedSquareLogs.lean#L52)

给定有限处集、实数权重 $a_v$ 和实数根对数 $R_v$，令 $A=\sum_v a_vR_v$。将 $\sum_v a_v(j/m)^2R_v$ 按标签取平均，得到 $(S_m/m)A$。若 $m\ge2$ 且 $A<0$，该平均严格大于 $A$。严格不等式使用的是总和的符号。 [Lean 加权比较](../joshi-ii-square-logs/Source_JoshiIINormalizedSquareLogs.lean#L65)

### 接入 Form 2

Joshi III 定理 9.9.1（Form 1）使用 Joshi II 定理 9.2.1 的平方指数。定理 9.11.1（Form 2）先使用 theta 区域内的张量格子取得体积下界，再沿用该数值估计。Form 2 的原文假设是奇素数 $\ell\gg0$ 及全局初始 theta 数据。 [Form 1 公式 (9.9.5)](https://arxiv.org/pdf/2401.13508v4#page=121) · [Form 2 的定理和证明](https://arxiv.org/pdf/2401.13508v4#page=127)

应用时须为每个 $K,d$ 先固定一个适用于整个 P7 数据族的 $N(K,d)$，再量化点 $x$ 和数据 $X$。比较须对满足 $P_{K,d}(X)$ 且 $N(K,d)\le X.\ell$ 的所有 $X$ 成立，P7 须对每个适用点和每个满足 $\ell\ge\max(7,N(K,d))$ 的适用素数提供相应数据。在 $h\le N(K,d)^2$ 的有限点集之外，所选素数满足 $N(K,d)<\sqrt h\le\ell$。仍需在同一 P7 见证上给出论文的 theta 区域、归一化包络体积、带符号的 q-pilot 对应和定理 1.10 的局部估计。 [规范消费者](Source_TripodCanonicalCorollary22PrimeBound.lean#L24) · [条件性体积估计](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaPaperLogWitnessHull.lean#L125) · [来源比较](../../b1-curve-field-arithmetic-20261118/readbacks/p7-cor312-source-comparison.md)

## 日本語

`c2_of_prime_lower_bound` は、元の高さ理論と幾何学の設定に自然数 $N$ を指定する。点 $x$ とその高さ $h=I.h(x)$ に対する元の仮定に加え、$N\le\sqrt h$ を仮定する。素数選択の定理は、次の区間に属する素数 $\ell$ を与える。 [定理と高さの仮定](Corollary22Inputs_c2.lean#L89) · [素数選択](../../../../Theorems/Thm_AbcAdaptation_Reference_Iut_LocalHeightData_exists_prime_selection.lean#L124)

$$\sqrt h\le\ell\le10\delta\sqrt h\,\log(2\delta h),\qquad \delta=552960\,d.$$

証明は同じ $\ell$ で (P2)–(P6) を満たすことを示す。区間の下界と $N\le\sqrt h$ を合わせると $N\le\ell$ を得る。`ThetaDataExistenceAtLeast` は、$K$ に属し、次数が $d$ 以下で `excCore` の外にある各点を対象とする。各点に対して、素数 $\ell$ は $\ell\ge7$、$N\le\ell$ と次の条件を満たす。 [P7 のデータ型](Corollary22Inputs_c2.lean#L69) · [選んだ素数の使用](Corollary22Inputs_c2.lean#L233)

- (P2) 素数 $\ell$ はどの悪い素点のTate パラメータの位数も割り切らない。
- (P3) 剰余標数が $\ell$ の各悪い素点で、Tate パラメータの位数は $\sqrt h$ より小さい。
- (P5) 剰余標数が $2$ とも $\ell$ とも異なる悪い素点が存在する。
- (P6) mod $\ell$ 表現の像は $\mathrm{SL}_2(\mathbb F_\ell)$ を含む。

これらの条件を満たす点と素数の各組に対して、一つの存在証明が指定の述語 $P$ を満たすデータ $X$ を与える。同じ存在証明は、$X$ の不変量、定理 1.10 の証明書、およびその不変量に対する局所評価を与え、次の関係を満たす。

- $X$ の素数は $\ell$ であり、そのモジュライ体の次数は $d$ 以下である。
- $X$ の $\log Q$ は、剰余標数が $2$ とも $\ell$ とも異なる素点からの正規化した高さの寄与に等しい。
- $X$ の不同イデアルに関する不変量は、点 $x$ の不同イデアルの正規化した対数次数に等しい。点 $x$ の導手の対数次数は、導手の不変量以上であり、その不変量に $\log(2\ell)$ を加えた値以下である。

`h312` は $P(X)$ と $N\le X.\ell$ を満たす各 $X$ に対して `Corollary312Variant X` を与える。証明は $X.\ell=\ell$ を使って、この下界を `h312` に渡す。その比較を、同じ $X$ に対する証明書および局所評価と共に定理 1.10 に適用する。素数計数の証明書の定数を $\eta$、$B=I.B$ とすると、元の三つの結論を得る。 [定理 1.10 の適用](Corollary22Inputs_c2.lean#L242) · [三つの結論](Corollary22Inputs_c2.lean#L100)

$$\frac h6\le(1+\varepsilon_E(\delta,h))(\log\operatorname{Diff}(x)+\log\operatorname{Cond}(x))+40\eta+\frac B3,\qquad
\varepsilon_E(\delta,h)\le1,\qquad
0\le\log\operatorname{Diff}(x)+\log\operatorname{Cond}(x).$$

元の `c2` は $N=0$ としてこの証明を使う。$0\le\ell$ は常に成り立つため、元の P7 の存在証明から下界をゼロとした存在証明を得る。逆に、下界をゼロとした存在証明に $0\le\ell$ を渡すと元の P7 の存在証明を得る。二つの `h312` も同様に、自動的に成り立つ $0\le X.\ell$ を用いて対応する。$0\le\sqrt h$ により追加の高さの仮定を満たす。この特殊化は、元の `c2` の主張全体を与える。 [元の P7 の型](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Corollary22.lean#L112) · [参照元の c2](../../../../../refer/iut/Iut/Implication/Corollary22.lean#L386) · [下界をゼロとする特殊化](Corollary22Inputs_c2.lean#L272)

各コンパクト有界集合 $K$ と正の次数上界 $d$ に対し、標準高さの評価に用いる定理は、点 $x$ によらない下界 $N(K,d)$ を取る。$K$ に属し次数が $d$ 以下の点の範囲で、コア条件の例外集合と $h\le N(K,d)^2$ を満たす点の集合との和集合を取る。前者はコア条件の例外集合の有限性から、後者は Northcott の有限性から有限である。和集合の外では $h>N(K,d)^2$ から必要な平方根の下界を得る。評価には元の高さのしきい値と定数 $40\eta+B/3$ を使う。 [Northcott の有限性](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Corollary22.lean#L53) · [標準高さの評価に用いる定理](Source_TripodCanonicalCorollary22PrimeBound.lean#L31)

証明は、補助高さと標準高さの間の既存の比較を使う。有限例外集合の点の標準高さは、最終的なしきい値以下に収める。既存の `StatementII` の証明は、標準高さがそのしきい値以下の点における差を Northcott の有限性によって一様に抑える。したがって各 $K$、次数上界 $d$、および $\varepsilon>0$ に対して、$K$ に属し次数が $d$ 以下のすべての点で次の評価が成り立つ定数 $C$ が存在する。 [高さの比較としきい値](../../../../Definitions/Def_TripodCanonicalHighHeightComposition.lean#L22) · [高さが低い点の有限集合](../../../../Definitions/Def_TripodStatementIIComposition.lean#L21) · [StatementII への適用](Source_TripodCanonicalCorollary22PrimeBound.lean#L73)

$$\operatorname{htCan}(x)\le(1+\varepsilon)(\operatorname{logDiff}(x)+\operatorname{logCond}(x))+C.$$

### 平方で与えられる指数

正の整数 $m$ に対し、Lean ではラベル $1,\ldots,m$ にわたって和を取る。$\ell=2m+1$ とおく。任意の実数 $L$ に対して $L/(2\ell)$ を掛けると、次の二つ目の等式を得る。Tate パラメータをもつ素点では $L=\log|q|$、$r=|q^{1/(2\ell)}|$ と取ると $L/(2\ell)=\log r$ となる。 [Lean の等式](../joshi-ii-square-logs/Source_JoshiIINormalizedSquareLogs.lean#L19)

$$S_m=\sum_{j=1}^{m}\frac{j^2}{m^2}=\frac{(m+1)(2m+1)}{6m},\qquad
S_m\frac{L}{2\ell}=\frac{1}{12}\left(1+\frac{1}{m}\right)L.$$

$m\ge2$ では差 $m-S_m=(m-1)(4m+1)/(6m)$ が正である。したがって $L<0$ ならば $m L/(2\ell)<S_m L/(2\ell)$ となる。同値な形で、$0<r<1$ ならば $r^{S_m}>r^m$ となる。どの奇素数 $\ell\ge5$ でも $m\ge2$ を満たす。 [Lean の対数不等式](../joshi-ii-square-logs/Source_JoshiIINormalizedSquareLogs.lean#L52)

有限個の素点に実数の重み $a_v$ と根の実数対数 $R_v$ を与え、$A=\sum_v a_vR_v$ とおく。$\sum_v a_v(j/m)^2R_v$ をラベルについて平均すると $(S_m/m)A$ となる。$m\ge2$ かつ $A<0$ ならば、この平均は $A$ より真に大きい。狭義不等式には総和の符号を使う。 [Lean の重み付き比較](../joshi-ii-square-logs/Source_JoshiIINormalizedSquareLogs.lean#L65)

### Form 2 への適用

Joshi III の定理 9.9.1（Form 1）は、Joshi II の定理 9.2.1 にある平方で与えられる指数を使う。定理 9.11.1（Form 2）の証明では、テータ領域内のテンソル格子から体積の下界を得て、同じ数値評価を用いる。Form 2 の定理は奇素数 $\ell\gg0$ と大域的な初期テータデータを仮定する。 [Form 1 の式 (9.9.5)](https://arxiv.org/pdf/2401.13508v4#page=121) · [Form 2 の定理と証明](https://arxiv.org/pdf/2401.13508v4#page=127)

適用には、各 $K,d$ について、P7 のデータ族全体に共通の $N(K,d)$ が要る。この下界を点 $x$ とデータ $X$ より先に固定する。比較は $P_{K,d}(X)$ と $N(K,d)\le X.\ell$ を満たすすべての $X$ に対して成り立つ必要がある。P7 は、条件を満たす各点と $\ell\ge\max(7,N(K,d))$ を満たす各適用可能な素数にデータを与える必要がある。$h\le N(K,d)^2$ を満たす有限集合の外では、選ばれた素数は $N(K,d)<\sqrt h\le\ell$ を満たす。同じ P7 のデータ上で、論文のテータ領域、正規化した包絡の体積、符号付き q-pilot の同定、および定理 1.10 の局所評価を与えることが残る。 [標準高さの評価に用いる定理](Source_TripodCanonicalCorollary22PrimeBound.lean#L24) · [条件付き体積評価](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutInitialThetaPaperLogWitnessHull.lean#L125) · [原文との比較](../../b1-curve-field-arithmetic-20261118/readbacks/p7-cor312-source-comparison.md)

## Paper sources

Kirti Joshi, *Construction of Arithmetic Teichmuller spaces II: Proof of a local prototype of Mochizuki's Corollary 3.12*, arXiv:2303.01662v3, submitted 24 February 2025. Theorem 9.2.1 starts on printed and PDF page 27. The proof evaluates the coefficient on page 28. [Official PDF](https://arxiv.org/pdf/2303.01662v3#page=28) · [Local TeX](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.tex#L1157>)

> If $\ell$ is sufficiently large then
> $$\frac{1}{12}\left(1+\frac{1}{\ell^*}\right)<\frac14\left(1-\frac{1}{\ell}\right)=\frac{\ell^*}{2\ell},$$
> and as $\log(|q|_{\mathbb C_p})<0$ one gets […]

Kirti Joshi, *Construction of Arithmetic Teichmuller Spaces III: A ‘Rosetta Stone’ and a proof of Mochizuki's Corollary 3.12*, arXiv:2401.13508v4, submitted 24 February 2025. Theorem 9.9.1 starts on printed and PDF page 119. Equations (9.9.4) and (9.9.5) are on page 121. Theorem 9.11.1 and its tensor lattice argument are on page 127. [Form 1](https://arxiv.org/pdf/2401.13508v4#page=119) · [Form 2](https://arxiv.org/pdf/2401.13508v4#page=127) · [Local TeX](<../../../../../refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex#L3617>)

> For $X,C,L,L'$ satisfying §2.4, §3.1, §3.3, and for an odd prime $\ell\gg0$ one has
> $$\operatorname{Vol}(\widetilde\Theta_{\mathrm{Mochizuki}}^{\mathbf I})\ge
> \prod_{w\in\underline{\mathbb V}^{\mathrm{odd,ss}}}|q_w^{1/(2\ell)}|^{\ell^*},$$
> and also
> $$\operatorname{Vol}(\widetilde\Theta_{\mathrm{Joshi}}^{\mathbf I})\ge
> \prod_{w\in\underline{\mathbb V}^{\mathrm{odd,ss}}}|q_w^{1/(2\ell)}|^{\ell^*}.$$
