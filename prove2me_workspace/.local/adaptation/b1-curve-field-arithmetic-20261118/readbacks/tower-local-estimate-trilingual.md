# `TowerArithmetic.localEstimate`

## English

Fix anabelian geometry `AG`, tempered geometry `TG` over it, and `D : InitialThetaData AG TG`. Write $F=D.F$ for the field of definition, $K_t=D.Kt$ for the $\ell$-torsion number field, and $\ell=D.\ell$ for its admissible prime, which is at least $5$. Take `LT : LocalTheory.{u,v} D.Kt`, `TL : ThetaLocalData D LT`, `QI : QPilotInputs D`, and `TA : TowerArithmetic D LT TL`. The fields of `QI` give the finiteness of the bad places of $F$ above the selected bad moduli places and the positive residue degree of every finite place of $F$. Set $X=\mathrm{concreteVariantData}(D,LT,TL,QI)$ and $\mathrm{inv}=\mathrm{TL.invariants}(QI)$. The noncomputable construction gives a value of type $\mathrm{inv.LocalEstimate}$. [Construction](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteLocalEstimate.lean:416) · [Concrete invariants](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:151) · [q-pilot inputs](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutQPilot.lean:28)

Let $d_{\mathrm{mod}}$ be the degree of the field of moduli over $\mathbb Q$ and set $A=552960d_{\mathrm{mod}}\ell$. The finite set $S=\mathrm{TL.dst}$ is the union of $\{2,3,5,\ell\}$, `TL.badChars`, and the residue characteristics at finite places of $K_t$ with absolute ramification index different from $1$. Let $D_0$ and $C_0$ be the normalized log different and conductor degrees of the tripodal field, respectively. Both use its degree over $\mathbb Q$ as the denominator. The three fields of `TA` give these bounds. The first applies at every finite place $w$ of $K_t$, with residue characteristic $p$ and absolute ramification index $e_w$. The subtraction $p-2$ is in $\mathbb N$.

$$
\begin{aligned}
p-2<e_w &\ \Longrightarrow\ \bigl(p\le A \ \land\ \log e_w\le-3+4\log A\bigr),\\
\sum_{p\in S}\mathrm{LT.logDK}(p)&\le D_0+C_0+2\log\ell+21,\\
\sum_{p\in S}\log p&\le2d_{\mathrm{mod}}(D_0+C_0)+5+\log\ell.
\end{aligned}
$$

[Distinguished primes](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:62) · [Tower arithmetic](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:173) · [Normalized degrees](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean:24)

The standard procession has $N=\lfloor(\ell-1)/2\rfloor$ capsules. For every index $0\le i<N$, put $L_i=\{0,\ldots,i+1\}$ and $m_i=i+2$. For each rational place $r$, either a rational prime $p$ or $\infty$, a packet component $c$ assigns a place of $K_t$ above $r$ to every label in $L_i$. Its tensor space and integral region $O_c$ come from `LT`. The packet carrier is the product of those tensor spaces. Its packet log-volume $\operatorname{Vol}_{i,r}$ on a product region is the sum of the normalized component log-volumes, weighted by the product of the place weights of the tuple. The place weights are positive and sum to $1$ over the fiber at $r$. At a finite prime the weight of $w$ is $[(K_t)_w:\mathbb Q_p]/[K_t:\mathbb Q]$. At infinity the numerator is the local degree over $\mathbb R$. [Standard labels](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteLocalEstimate.lean:122) · [Packet volume](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteContainer.lean:202) · [Place weights](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean:76)

The field `cont` gives a set $C_{i,r}$ of the packet carrier for each $i,r$. At $p\in S$ it takes the product of $a_cO_c$, with a unit $a_c$ chosen for each tuple by the local containment and volume bound in `LT.prop14_iii`. At $p\notin S$ it takes the packet's integral region $\prod_c O_c$. At infinity it takes $\prod_c\pi^{m_i}O_c$, where $O_c$ is the region that `LT` supplies as its archimedean unit ball. The field `cont_mem_hullRegions` puts these sets in the hull system's class. At a finite prime this class uses multiplication by a unit in every component. At infinity it uses a positive real scale in each component. [Region construction](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteLocalEstimate.lean:198) · [Hull system class](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteContainer.lean:230)

The field `thetaPilot_subset` places the theta-pilot region inside $C_{i,r}$ for every $i,r$. The region is the product of its component sets. At a finite prime, multiply $O_c$ by the $(i+1)^2$-th power of the root in the factor of label $i+1$. Take the union of the images of that set under the supplied indeterminacy automorphisms. At infinity take the union of the images of the component log-shell under the automorphisms supplied there. The field `cont_eq_integral` gives the stated equality with the integral region for every $i$ and every $p\notin S$. The local normalization gives packet log-volume zero there. [Theta-pilot components](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteThetaRegion.lean:127) · [Containment](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteLocalEstimate.lean:287) · [Integral volume](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteContainer.lean:216)

The fields `vol_finite`, `vol_infinite`, and `packetVol_mono` give the following bounds for every $i$. In the last line, $r$ is any rational place and $U,V$ are any two regions in that packet of the form $\prod_c a_c O_c$ with every $a_c$ a unit, each region with its own scaling tuple.

$$
\begin{aligned}
\operatorname{Vol}_{i,p}(C_{i,p})
&\le m_i\,\mathrm{LT.logDK}(p)
-\frac{(m_i-1)^2}{2\ell}\,X.\mathrm{logQAt}(p)
+\log p+4m_i\log A\,\mathbf 1_{p\le A}
\qquad (p\in S),\\
\operatorname{Vol}_{i,\infty}(C_{i,\infty})&\le m_i\log\pi,\\
\operatorname{Vol}_{i,r}(U)&\le\operatorname{Vol}_{i,r}(V)\qquad(U\subseteq V).
\end{aligned}
$$

Here $\mathrm{LT.logDK}(p)$ is the sum of the normalized different exponents above $p$, weighted by their place weights and multiplied by $\log p$. A normalized exponent is the order of the different ideal at $w$ divided by $e_w$. The term $X.\mathrm{logQAt}(p)$ is the sum of $(f_w/[F:\mathbb Q])\,\operatorname{qOrder}(w)\log p$ over the q-pilot's bad places $w$ of residue characteristic $p$, where $f_w$ is the residue degree. The finite bound uses the base-change identity for this term and uses the first field of `TA` for the ramification correction. The infinite bound uses the local containment and volume laws of `LT`. [Seven fields and finite bound](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Implication_LogVolumeBound.lean:104) · [Different exponents](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean:96) · [q-pilot contribution](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Invariants.lean:189) · [Weighted estimates](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteLocalEstimate.lean:314)

## 简体中文

固定远 Abel 几何 `AG`、其缓和几何 `TG` 和 `D : InitialThetaData AG TG`。记 $F=D.F$ 为定义数域，$K_t=D.Kt$ 为 $\ell$ 挠点数域，$\ell=D.\ell$ 为不小于 $5$ 的可容许素数。给定 `LT : LocalTheory.{u,v} D.Kt`、`TL : ThetaLocalData D LT`、`QI : QPilotInputs D` 和 `TA : TowerArithmetic D LT TL`。`QI` 的字段给出 $F$ 中位于模域所选坏处上方的坏处的有限性，以及 $F$ 每个有限处的剩余次数正性。令 $X=\mathrm{concreteVariantData}(D,LT,TL,QI)$，$\mathrm{inv}=\mathrm{TL.invariants}(QI)$。不可计算构造返回 $\mathrm{inv.LocalEstimate}$ 类型的值。 [构造](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteLocalEstimate.lean:416) · [具体不变量](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:151) · [q-pilot 输入](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutQPilot.lean:28)

令 $d_{\mathrm{mod}}$ 为模域在 $\mathbb Q$ 上的次数，置 $A=552960d_{\mathrm{mod}}\ell$。有限集 $S=\mathrm{TL.dst}$ 是 $\{2,3,5,\ell\}$、`TL.badChars` 及 $K_t$ 中绝对分歧指数异于 $1$ 的有限处的剩余特征的并集。记 $D_0$ 和 $C_0$ 分别为三脚架域的归一化不同理想对数次数和导子对数次数，两者的分母均为三脚架域在 $\mathbb Q$ 上的次数。`TA` 的三个字段给出下列界。第一条适用于 $K_t$ 的每个有限处 $w$，其中 $p$ 为该处的剩余特征，$e_w$ 为绝对分歧指数。$p-2$ 在 $\mathbb N$ 中计算。

$$
\begin{aligned}
p-2<e_w &\ \Longrightarrow\ \bigl(p\le A \ \land\ \log e_w\le-3+4\log A\bigr),\\
\sum_{p\in S}\mathrm{LT.logDK}(p)&\le D_0+C_0+2\log\ell+21,\\
\sum_{p\in S}\log p&\le2d_{\mathrm{mod}}(D_0+C_0)+5+\log\ell.
\end{aligned}
$$

[指定素数](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:62) · [塔算术](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:173) · [归一化对数次数](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean:24)

标准标签集递增族有 $N=\lfloor(\ell-1)/2\rfloor$ 项。对每个指标 $0\le i<N$，令 $L_i=\{0,\ldots,i+1\}$，$m_i=i+2$。有理处 $r$ 为有理素数 $p$ 或无穷处 $\infty$。分量积包的每个分量 $c$ 为 $L_i$ 的每个标签选取 $K_t$ 中位于 $r$ 上方的处。该分量的张量空间与整区域 $O_c$ 由 `LT` 给出。分量积包的载体为这些张量空间的直积。在积区域上，包的对数体积 $\operatorname{Vol}_{i,r}$ 对各分量的归一化对数体积求加权和，每个元组的权重为各处权重的乘积。处权重为正，且在 $r$ 的纤维上和为 $1$。在有限素数处，$w$ 的权重为 $[(K_t)_w:\mathbb Q_p]/[K_t:\mathbb Q]$。在无穷处，分子为完备化在 $\mathbb R$ 上的次数。 [标准标签](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteLocalEstimate.lean:122) · [分量积包体积](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteContainer.lean:202) · [处权重](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean:76)

字段 `cont` 对每个 $i,r$ 在分量积包的载体中给出集合 $C_{i,r}$。当 $p\in S$ 时，取 $a_cO_c$ 的直积，各分量的可逆元 $a_c$ 由 `LT.prop14_iii` 的局部包含与体积界选得。当 $p\notin S$ 时，取包的整区域 $\prod_c O_c$。在无穷处取 $\prod_c\pi^{m_i}O_c$，此处 $O_c$ 是 `LT` 指定为无穷处单位球的区域。字段 `cont_mem_hullRegions` 给出这些集合属于包络系统指定的区域族。该族在有限素数处允许各分量由可逆元缩放，在无穷处允许各分量由正实数径向缩放。 [区域构造](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteLocalEstimate.lean:198) · [包络区域族](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteContainer.lean:230)

字段 `thetaPilot_subset` 给出每个 $i,r$ 处的 Θ-pilot 区域包含在 $C_{i,r}$ 中。该区域是各分量集合的直积。在有限素数处，先在标签 $i+1$ 对应的因子中用该处的根的 $(i+1)^2$ 次幂缩放整区域 $O_c$，再对所得集合在给定的不定性自同构下的像取并集。在无穷处，对分量对数壳在该处给定的不定性自同构下的像取并集。字段 `cont_eq_integral` 对每个 $i$ 和每个 $p\notin S$ 给出与整区域的等式。局部归一化使该处的包对数体积为零。 [Θ-pilot 分量](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteThetaRegion.lean:127) · [包含关系](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteLocalEstimate.lean:287) · [整区域体积](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteContainer.lean:216)

字段 `vol_finite`、`vol_infinite` 和 `packetVol_mono` 对每个 $i$ 给出下列界。最后一式中，$r$ 为任意有理处，$U,V$ 是包内任意两个形如 $\prod_c a_c O_c$ 的区域，每个区域有各自的缩放元组，且每个 $a_c$ 均可逆。

$$
\begin{aligned}
\operatorname{Vol}_{i,p}(C_{i,p})
&\le m_i\,\mathrm{LT.logDK}(p)
-\frac{(m_i-1)^2}{2\ell}\,X.\mathrm{logQAt}(p)
+\log p+4m_i\log A\,\mathbf 1_{p\le A}
\qquad (p\in S),\\
\operatorname{Vol}_{i,\infty}(C_{i,\infty})&\le m_i\log\pi,\\
\operatorname{Vol}_{i,r}(U)&\le\operatorname{Vol}_{i,r}(V)\qquad(U\subseteq V).
\end{aligned}
$$

其中 $\mathrm{LT.logDK}(p)$ 在 $p$ 上方对处权重乘以归一化不同理想指数求和，再乘以 $\log p$。归一化指数为不同理想在 $w$ 的阶数除以 $e_w$。$X.\mathrm{logQAt}(p)$ 在 q-pilot 中剩余特征为 $p$ 的坏处 $w$ 对 $(f_w/[F:\mathbb Q])\,\operatorname{qOrder}(w)\log p$ 求和，其中 $f_w$ 为剩余次数。有限处的界使用这一项的基变换恒等式，并用 `TA` 的第一字段控制分歧修正项。无穷处的界使用 `LT` 的局部包含与体积规律。 [七个字段及有限处界](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Implication_LogVolumeBound.lean:104) · [不同理想指数](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean:96) · [q-pilot 贡献](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Invariants.lean:189) · [加权估计](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteLocalEstimate.lean:314)

## 日本語

遠アーベル幾何学 `AG`、その緩和幾何学 `TG`、および `D : InitialThetaData AG TG` を固定する。$F=D.F$ を定義体、$K_t=D.Kt$ を $\ell$ ねじれ点数体とし、$\ell=D.\ell$ を $5$ 以上の許容素数とする。`LT : LocalTheory.{u,v} D.Kt`、`TL : ThetaLocalData D LT`、`QI : QPilotInputs D`、および `TA : TowerArithmetic D LT TL` を与える。`QI` のフィールドは、モジュライ体の指定された悪い素点の上にある $F$ の悪い素点の有限性と、$F$ の全有限素点の剰余次数の正値性を与える。$X=\mathrm{concreteVariantData}(D,LT,TL,QI)$、$\mathrm{inv}=\mathrm{TL.invariants}(QI)$ とする。非計算的な構成は $\mathrm{inv.LocalEstimate}$ 型の値を返す。 [構成](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteLocalEstimate.lean:416) · [具体的な不変量](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:151) · [q-pilot の入力](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutQPilot.lean:28)

$d_{\mathrm{mod}}$ をモジュライ体の $\mathbb Q$ 上の次数とし、$A=552960d_{\mathrm{mod}}\ell$ とする。有限集合 $S=\mathrm{TL.dst}$ は、$\{2,3,5,\ell\}$、`TL.badChars`、および絶対分岐指数が $1$ と異なる $K_t$ の有限素点の剰余標数の和集合である。$D_0$ と $C_0$ をそれぞれ三脚体の正規化した不同イデアルの対数次数と導手の対数次数とする。どちらの分母も三脚体の $\mathbb Q$ 上の次数である。`TA` の三つのフィールドは次の評価を与える。第一式は $K_t$ の各有限素点 $w$ に適用し、$p$ はその剰余標数、$e_w$ は絶対分岐指数である。$p-2$ は $\mathbb N$ で計算する。

$$
\begin{aligned}
p-2<e_w &\ \Longrightarrow\ \bigl(p\le A \ \land\ \log e_w\le-3+4\log A\bigr),\\
\sum_{p\in S}\mathrm{LT.logDK}(p)&\le D_0+C_0+2\log\ell+21,\\
\sum_{p\in S}\log p&\le2d_{\mathrm{mod}}(D_0+C_0)+5+\log\ell.
\end{aligned}
$$

[指定された素数](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:62) · [体の塔の算術条件](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteInvariants.lean:173) · [正規化した対数次数](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_TripodalInvariants.lean:24)

標準列は $N=\lfloor(\ell-1)/2\rfloor$ 個のカプセルを持つ。各添字 $0\le i<N$ に対し、$L_i=\{0,\ldots,i+1\}$、$m_i=i+2$ とする。有理素点 $r$ は有理素数 $p$ または無限素点 $\infty$ である。パケットの各成分 $c$ は $L_i$ の各ラベルに $r$ の上の $K_t$ の素点を割り当てる。そのテンソル空間と整領域 $O_c$ は `LT` が与える。パケット全体は、それらのテンソル空間の直積である。積領域のパケット対数体積 $\operatorname{Vol}_{i,r}$ は、正規化した各成分の対数体積の重み付き和である。各組の重みは素点の重みの積である。素点の重みは正であり、$r$ の上のファイバーでの和は $1$ になる。有限素点 $w$ の重みは $[(K_t)_w:\mathbb Q_p]/[K_t:\mathbb Q]$ である。無限素点では分子が完備化の $\mathbb R$ 上の次数となる。 [標準のラベル](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteLocalEstimate.lean:122) · [パケットの体積](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteContainer.lean:202) · [素点の重み](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean:76)

フィールド `cont` は、各 $i,r$ についてパケットの中の集合 $C_{i,r}$ を与える。$p\in S$ では $a_cO_c$ の直積を取り、各成分の単元 $a_c$ は `LT.prop14_iii` の局所包含と体積の評価から選ぶ。$p\notin S$ ではパケットの整領域 $\prod_c O_c$ を取る。無限素点では $\prod_c\pi^{m_i}O_c$ を取り、ここで $O_c$ は `LT` が無限素点の単位球として与える領域である。フィールド `cont_mem_hullRegions` は、これらの集合が包絡系で指定された領域の族に属することを与える。その族は、有限素点では各成分を単元で、無限素点では各成分を正の実数で動径方向に拡大縮小した領域からなる。 [領域の構成](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteLocalEstimate.lean:198) · [包絡領域の族](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteContainer.lean:230)

フィールド `thetaPilot_subset` は各 $i,r$ の Θ-pilot 領域が $C_{i,r}$ に含まれることを与える。その領域は各成分の集合の直積である。有限素点では、ラベル $i+1$ の因子にある根の $(i+1)^2$ 乗で $O_c$ を拡大縮小し、与えられた不定性自己同型によるその集合の像の和集合を取る。無限素点では、成分の対数殻について、その素点で与えられた不定性自己同型による像の和集合を取る。フィールド `cont_eq_integral` は各 $i$ と各 $p\notin S$ で整領域との等式を与える。局所正規化により、その素点でのパケット対数体積は零になる。 [Θ-pilot の成分](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteThetaRegion.lean:127) · [包含関係](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteLocalEstimate.lean:287) · [整領域の体積](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteContainer.lean:216)

フィールド `vol_finite`、`vol_infinite`、および `packetVol_mono` は各 $i$ について次の評価を与える。最終行の $r$ は任意の有理素点である。$U,V$ はそのパケットにおいて $\prod_c a_c O_c$ の形をもつ任意の二つの領域であり、それぞれの領域で各 $a_c$ は単元である。

$$
\begin{aligned}
\operatorname{Vol}_{i,p}(C_{i,p})
&\le m_i\,\mathrm{LT.logDK}(p)
-\frac{(m_i-1)^2}{2\ell}\,X.\mathrm{logQAt}(p)
+\log p+4m_i\log A\,\mathbf 1_{p\le A}
\qquad (p\in S),\\
\operatorname{Vol}_{i,\infty}(C_{i,\infty})&\le m_i\log\pi,\\
\operatorname{Vol}_{i,r}(U)&\le\operatorname{Vol}_{i,r}(V)\qquad(U\subseteq V).
\end{aligned}
$$

ここで $\mathrm{LT.logDK}(p)$ は、$p$ の上の素点における正規化した不同イデアルの指数に素点の重みを掛けた和と $\log p$ の積である。正規化した指数は $w$ における不同イデアルの位数を $e_w$ で割った値である。$X.\mathrm{logQAt}(p)$ は q-pilot に属する剰余標数 $p$ の悪い素点 $w$ に対する $(f_w/[F:\mathbb Q])\,\operatorname{qOrder}(w)\log p$ の和であり、$f_w$ は剰余次数である。有限素点での評価には、この項の底変換の恒等式と、分岐補正項に対する `TA` の第一フィールドを用いる。無限素点での評価には `LT` の局所包含則と体積則を用いる。 [七つのフィールドと有限素点での評価](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Implication_LogVolumeBound.lean:104) · [不同イデアルの指数](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean:96) · [q-pilot の寄与](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Implication_Invariants.lean:189) · [重み付き評価](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteLocalEstimate.lean:314)

## 消费者与存档回执

`ConcreteThetaDataExistence.toThetaDataExistence` 与 `sourceP7Existence` 都直接将该值包装为 `Nonempty inv.LocalEstimate`。定理 1.10 的证明通过 `LocalEstimate.rhs_le` 消费这一结构给出的包络区域、包含关系和体积界。 [通用 P7 转换](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteExistence.lean:64) · [来源 P7](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodP7.lean:106) · [定理 1.10](/home/admin-wsl/Coq/abc/prove2me_workspace/Theorems/Thm_AbcAdaptation_Reference_Iut_Theorem110Invariants_theorem110.lean:177)

`Source_ReferenceIutConcreteLocalEstimate.lean` 的现行 SHA-256 为 `3e242c2b3d4357bd3a94ec716940f37d14dde5c7eecc788795f426c88461d4f8`，与两次叶检查及直接公理审查所列散列一致。三份回执均为独占工作区、无快照、退出码 $0$、诊断为空。审查对本声明报告 `propext`、`Classical.choice` 和 `Quot.sound`，且 `no_sorryAx = true`。 [叶检查 ci-021338-71910910](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-021338-71910910-result.json) · [产物检查 ci-021368-04a24c77](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-021368-04a24c77-result.json) · [公理审查 ci-021405-7008ce12](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-021405-7008ce12-result.json) · [来源台账](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/SOURCE_LEDGER.md:315)
