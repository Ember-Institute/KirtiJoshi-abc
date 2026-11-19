# concreteLocalTheory

## English

For any number field $K$ with type `Type u`, `LocalConstruct.concreteLocalTheory (K := K)` gives a term of `LocalTheory.{u,u} K`. The inputs are the field and number-field instances on $K$. Each tensor type also lies in `Type u`. [Local definition](../../../../Solutions/Source_ReferenceIutConcreteLocalTheory.lean#L27) · [Record type](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L131) · [Pinned iut definition](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Concrete/LocalConstruct/Theory.lean#L60)

The theory uses the existing `concreteLocalTensor`. Fix a tuple $c$ of places of $K$ indexed by a finite type $I$. At the rational prime $p$, take the tensor product over $\mathbb Q_p$. Each entry contributes its completion if it is finite with residue characteristic $p$, and the zero ring otherwise. At the rational infinite place, take the tensor product over $\mathbb R$ of the real and complex factors selected by `archTuple`. An infinite entry keeps its place. A finite entry uses an arbitrarily chosen infinite place via `archPlace`. [Tensor packets](../../../../Solutions/Source_ReferenceIutConcreteLocalPacket.lean#L283) · [Finite-place condition](../../../../Solutions/Source_ReferenceIutConcreteLocalPacket.lean#L35) · [Infinite-place selection](../../../../Solutions/Source_ReferenceIutConcreteLocalPacket.lean#L209)

The arithmetic fields provide primality of finite residue characteristics, finiteness of each fiber, and finiteness of the set of ramified finite places. They provide positive local degrees and ramification indices, and zero absolute different exponent at places of index $1$. At a rational prime, the sum of the local degrees is $[K:\mathbb Q]$. The sum of the infinite-place multiplicities is also $[K:\mathbb Q]$. The valuation gives $\operatorname{ord}_p(p)=1$ and adds under multiplication of nonzero elements. [Arithmetic fields](../../../../Solutions/Source_ReferenceIutConcreteLocalTheory.lean#L29) · [Normalized valuation](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L87)

The integral region $R$ is the integral closure of $\mathbb Z_p$ in the finite tensor. The integral region $B_I$ at infinity is the closed projective tensor unit ball. Both contain $1$. A nonzero element in a specified finite factor maps to a tensor unit. If its normalized valuation is nonnegative, multiplication by its image takes $R$ into $R$. [Finite integral region](../../../../Solutions/Source_ReferenceIutConcreteLocalIntegral.lean#L147) · [Projective unit ball](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalArchimedeanTensor.lean#L120)

The finite log-shell is the transported normalization-module span of the tensor log-shell of the completions when every entry lies over $p$. It is $R$ in the zero-ring case. The infinite log-shell is $\pi^{|I|}B_I$. The closures of both log-shells are compact. The finite log-shell contains $R$. It equals $R$ at odd $p$ if each tuple entry that is a finite place has ramification index $1$. [Log-shell fields](../../../../Solutions/Source_ReferenceIutConcreteLocalTheory.lean#L48) · [Infinite log-shell](../../../../Solutions/Source_ReferenceIutConcreteLocalArchimedean.lean#L169)

For finite log-volume, convert both the Haar mass of the set and that of $R$ to real numbers using `toReal`. Take the logarithm of their ratio and divide by the $\mathbb Q_p$-dimension. The zero-ring case has log-volume zero for every set. At infinity, normalize Haar measure to mass $1$ on $B_I$. Take the logarithm of the real-valued mass of the set and divide by the real dimension. Each log-volume is zero on its integral region. For unit multiples of the integral region, log-volume is monotone under inclusion. For positive real $t$, the log-volume of $tB_I$ is $\log t$. [Volume fields](../../../../Solutions/Source_ReferenceIutConcreteLocalTheory.lean#L56) · [Finite normalization](../../../../Solutions/Source_ReferenceIutConcreteLocalHaar.lean#L80) · [Infinite normalization](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalArchimedeanTensorHaar.lean#L72)

At either rational place, an admissible set is nonempty and measurable, has compact closure, and has positive finite Haar measure. The integral region and each unit multiple are admissible. For an admissible finite set $U$ with all tuple entries over $p$, pullback under multiplication by $p$ adds $\log p$ to its log-volume. [Admissibility fields](../../../../Solutions/Source_ReferenceIutConcreteLocalTheory.lean#L66) · [Prime scaling](../../../../Solutions/Source_ReferenceIutConcreteLocalTheory.lean#L81)

Every admissible region at a prime has a least containing region $aR$ with $a$ a tensor unit, ordered by inclusion. At infinity, every admissible region has a least containing radial region $tB_I$ with $t>0$. Least here is in the order of the radii. For $0<t\le t'$, there is an inclusion $tB_I\subseteq t'B_I$. [Least finite hull](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteHull.lean#L124) · [Least radial hull](../../../../Solutions/Source_ReferenceIutConcreteLocalArchimedean.lean#L136)

The indeterminacy maps are induced by factor automorphisms. The finite branch uses $\mathbb Q_p$-algebra automorphisms of the completions when all entries lie over $p$, and the identity alone for a zero-ring tensor. The infinite branch uses $\mathbb R$-algebra automorphisms of the factors. Each map family contains the identity. Each map sends the corresponding log-shell into itself. The union of all images of any unit multiple of the integral region is admissible, as is the union of all images of the log-shell. [Indeterminacy fields](../../../../Solutions/Source_ReferenceIutConcreteLocalTheory.lean#L86) · [Finite maps](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteIndeterminacy.lean#L46) · [Infinite maps](../../../../Solutions/Source_ReferenceIutConcreteLocalArchimedean.lean#L176)

For Proposition 1.4(iii), require all entries to lie over $p$. Fix an index $j$ and a finite place $w$ with `c j = Place.finite w`. Take a nonzero $x\in K_w$ with $\lambda=\operatorname{ord}_p(x)\ge 0$. The supplied real numbers $d_i$ must equal the normalized different exponents of the corresponding finite places. Write $e_i$ for their absolute ramification indices. The field of `LocalTheory` supplies a unit $a$ such that every indeterminacy image of $\operatorname{incl}_j(x)R$ lies in $aR$. Its finite log-volume satisfies the following bound, where the subtraction $p-2$ is in $\mathbb N$.

$$
V(aR)\ \le\
\left(-\lambda+\sum_{i\in I}d_i+1\right)\log p+
\sum_{\substack{i\in I\\ p-2<e_i}}\bigl(3+\log e_i\bigr).
$$

[Proposition 1.4(iii)](../../../../Solutions/Source_ReferenceIutConcreteLocalProp14.lean#L103)

Proposition 1.4(iv) gives $\phi(R)\subseteq R$ for every finite indeterminacy map $\phi$. Proposition 1.5 gives $\phi(\pi^{|I|}B_I)\subseteq\pi^{|I|}B_I$ for each infinite indeterminacy map $\phi$. [Indeterminacy fields](../../../../Solutions/Source_ReferenceIutConcreteLocalTheory.lean#L86) · [Proposition 1.5](../../../../Solutions/Source_ReferenceIutConcreteLocalArchimedean.lean#L188)

`PointThetaData.localTheory` applies this construction to $K=P.\mathrm{data}.\mathrm{Kt}$, the torsion field carried by the same point data $P$. [Pointwise consumer](../../../../Solutions/Source_ReferenceIutPointLocalTheta.lean#L29)

## 中文

对任意载体类型为 `Type u` 的数域 $K$，`LocalConstruct.concreteLocalTheory (K := K)` 给出 `LocalTheory.{u,u} K` 的一个项。输入是 $K$ 的域和数域实例。各张量类型也属于 `Type u`。 [本地定义](../../../../Solutions/Source_ReferenceIutConcreteLocalTheory.lean#L27) · [记录类型](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L131) · [固定版本的 iut 定义](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Concrete/LocalConstruct/Theory.lean#L60)

该理论使用现有的 `concreteLocalTensor`。固定以有限类型 $I$ 为指标的 $K$ 的位的元组 $c$。在有理素数 $p$ 处，取 $\mathbb Q_p$ 上的张量积。若某一项是剩余特征为 $p$ 的有限位，则取其完备化，否则取零环。在有理无穷位处，取 `archTuple` 所选实或复因子在 $\mathbb R$ 上的张量积。无穷位保留原位。有限位经 `archPlace` 改用任取的无穷位。 [张量包](../../../../Solutions/Source_ReferenceIutConcreteLocalPacket.lean#L283) · [有限位条件](../../../../Solutions/Source_ReferenceIutConcreteLocalPacket.lean#L35) · [无穷位的选取](../../../../Solutions/Source_ReferenceIutConcreteLocalPacket.lean#L209)

算术字段给出有限位剩余特征的素性、各纤维的有限性及分歧有限位集合的有限性。各局部次数和分歧指数均为正，分歧指数为 $1$ 的位处绝对不同理想的指数为零。对每个有理素数，其上各局部次数之和为 $[K:\mathbb Q]$。无穷位重数之和也等于 $[K:\mathbb Q]$。归一化赋值满足 $\operatorname{ord}_p(p)=1$，并且在非零元素相乘时相加。 [算术字段](../../../../Solutions/Source_ReferenceIutConcreteLocalTheory.lean#L29) · [归一化赋值](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L87)

有限张量包的整区域 $R$ 是 $\mathbb Z_p$ 在该张量包中的整闭包。无穷处的整区域 $B_I$ 是射影张量范数的闭单位球。两种区域都包含 $1$。指定有限因子的非零元素映为张量包中的单位。若该元素的归一化赋值非负，则乘以其像将 $R$ 映入 $R$。 [有限处整区域](../../../../Solutions/Source_ReferenceIutConcreteLocalIntegral.lean#L147) · [射影张量单位球](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalArchimedeanTensor.lean#L120)

当各项都位于 $p$ 上方时，在各完备化的张量积中取张量对数壳在归一化环上生成的子模，再将其传到有限张量包，所得为有限处对数壳。零环情形的对数壳是 $R$。无穷处对数壳为 $\pi^{|I|}B_I$。两种对数壳的闭包均紧致。有限处对数壳包含 $R$。若 $p$ 为奇素数且元组中每个有限位的分歧指数均为 $1$，则它等于 $R$。 [对数壳字段](../../../../Solutions/Source_ReferenceIutConcreteLocalTheory.lean#L48) · [无穷处对数壳](../../../../Solutions/Source_ReferenceIutConcreteLocalArchimedean.lean#L169)

计算有限处对数体积时，用 `toReal` 将给定集合与 $R$ 的加法 Haar 测度各自转为实数，取两者之比的自然对数，再除以张量包的 $\mathbb Q_p$ 维数。零环情形中，每个集合的对数体积均为零。在无穷处，将加法 Haar 测度归一化为 $B_I$ 的测度等于 $1$，再对给定集合的实数值测度取自然对数并除以实维数。各自的整区域的对数体积为零。整区域的两个单位倍若有包含关系，则对数体积保持该顺序。对正实数 $t$，区域 $tB_I$ 的对数体积为 $\log t$。 [体积字段](../../../../Solutions/Source_ReferenceIutConcreteLocalTheory.lean#L56) · [有限处归一化](../../../../Solutions/Source_ReferenceIutConcreteLocalHaar.lean#L80) · [无穷处归一化](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalArchimedeanTensorHaar.lean#L72)

在这两类有理位上，可容许集合均为非空可测集，闭包紧致且 Haar 测度为正且有限。整区域及其各单位倍均可容许。若有限处的区域 $U$ 可容许且元组中所有项都位于 $p$ 上方，则取乘以 $p$ 的映射下的原像使对数体积增加 $\log p$。 [可容许性字段](../../../../Solutions/Source_ReferenceIutConcreteLocalTheory.lean#L66) · [素数倍乘](../../../../Solutions/Source_ReferenceIutConcreteLocalTheory.lean#L81)

有限处的每个可容许区域都包含在某个 $aR$ 中，其中 $a$ 为张量包中的单位。这样的区域中存在按包含关系最小的一个。无穷处的每个可容许区域都包含在某个 $tB_I$ 中，其中 $t>0$，并且存在最小的此类半径。若 $0<t\le t'$，则 $tB_I\subseteq t'B_I$。 [有限处最小包络](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteHull.lean#L124) · [径向最小包络](../../../../Solutions/Source_ReferenceIutConcreteLocalArchimedean.lean#L136)

不定性映射由因子自同构诱导。在有限处，若所有项都位于 $p$ 上方，则使用各完备化的 $\mathbb Q_p$-代数自同构。零环张量包只使用恒等映射。无穷处使用各因子的 $\mathbb R$-代数自同构。两类映射集都包含恒等映射，每个映射都将相应的对数壳映入自身。整区域的任一单位倍在这些映射下的像的并集可容许。对数壳的各像的并集也可容许。 [不定性字段](../../../../Solutions/Source_ReferenceIutConcreteLocalTheory.lean#L86) · [有限处映射](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteIndeterminacy.lean#L46) · [无穷处映射](../../../../Solutions/Source_ReferenceIutConcreteLocalArchimedean.lean#L176)

命题 1.4(iii) 要求所有项都位于 $p$ 上方。固定指标 $j$ 与满足 `c j = Place.finite w` 的有限位 $w$，并取非零元素 $x\in K_w$，使 $\lambda=\operatorname{ord}_p(x)\ge 0$。给定的实数 $d_i$ 必须等于相应有限位的归一化不同指数。记这些位的绝对分歧指数为 $e_i$。`LocalTheory` 中的字段给出单位 $a$，使 $\operatorname{incl}_j(x)R$ 在每个不定性映射下的像都包含于 $aR$。其有限处对数体积满足下列上界，其中 $p-2$ 在 $\mathbb N$ 中计算。

$$
V(aR)\ \le\
\left(-\lambda+\sum_{i\in I}d_i+1\right)\log p+
\sum_{\substack{i\in I\\ p-2<e_i}}\bigl(3+\log e_i\bigr).
$$

[命题 1.4(iii)](../../../../Solutions/Source_ReferenceIutConcreteLocalProp14.lean#L103)

命题 1.4(iv) 对每个有限处的不定性映射 $\phi$ 给出 $\phi(R)\subseteq R$。命题 1.5 对每个无穷处的不定性映射 $\phi$ 给出 $\phi(\pi^{|I|}B_I)\subseteq\pi^{|I|}B_I$。 [不定性字段](../../../../Solutions/Source_ReferenceIutConcreteLocalTheory.lean#L86) · [命题 1.5](../../../../Solutions/Source_ReferenceIutConcreteLocalArchimedean.lean#L188)

`PointThetaData.localTheory` 将此构造用于 $K=P.\mathrm{data}.\mathrm{Kt}$，即同一点数据 $P$ 所携带的挠点域。 [逐点使用处](../../../../Solutions/Source_ReferenceIutPointLocalTheta.lean#L29)

## 日本語

台の型が `Type u` である任意の数体 $K$ について、`LocalConstruct.concreteLocalTheory (K := K)` は `LocalTheory.{u,u} K` の項を与える。入力は $K$ の体と数体のインスタンスである。各テンソルの型も `Type u` に属する。 [ローカルの定義](../../../../Solutions/Source_ReferenceIutConcreteLocalTheory.lean#L27) · [レコード型](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L131) · [固定リビジョンの iut の定義](https://github.com/lana-agents/iut/blob/07cb1da58f6d428a670dbb5dd6093d428bcbcdd8/Iut/Concrete/LocalConstruct/Theory.lean#L60)

この局所理論は既存の `concreteLocalTensor` を用いる。有限型 $I$ で添字付けられた $K$ の素点の組 $c$ を固定する。有理素数 $p$ では、$\mathbb Q_p$ 上のテンソル積を取る。各成分が剰余標数 $p$ の有限素点ならばその完備化を因子とし、それ以外ならば零環を因子とする。有理無限素点では、`archTuple` が選ぶ実または複素の因子の $\mathbb R$ 上のテンソル積を取る。無限素点の成分はその素点を用いる。有限素点の成分には、`archPlace` により任意に選んだ無限素点を用いる。 [テンソル積](../../../../Solutions/Source_ReferenceIutConcreteLocalPacket.lean#L283) · [有限素点の条件](../../../../Solutions/Source_ReferenceIutConcreteLocalPacket.lean#L35) · [無限素点の選択](../../../../Solutions/Source_ReferenceIutConcreteLocalPacket.lean#L209)

算術のフィールドは、有限素点の剰余標数が素数であり、各ファイバーと分岐する有限素点の集合が有限であることを与える。局所次数と分岐指数は正であり、分岐指数が $1$ の素点で絶対ディファレントの指数は零である。有理素数の上にある有限素点の局所次数の和は $[K:\mathbb Q]$ である。無限素点の重複度の和も $[K:\mathbb Q]$ である。付値は $\operatorname{ord}_p(p)=1$ と正規化し、零でない元の積に対して加法的である。 [算術のフィールド](../../../../Solutions/Source_ReferenceIutConcreteLocalTheory.lean#L29) · [正規化付値](../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean#L87)

有限素点での整領域 $R$ はそのテンソルにおける $\mathbb Z_p$ の整閉包である。無限素点での整領域 $B_I$ は射影テンソルノルムの閉単位球である。どちらも $1$ を含む。指定された有限素点の因子の零でない元はテンソルの単元に移る。その元の正規化付値が非負ならば、像による乗法は $R$ を $R$ に移す。 [有限素点の整領域](../../../../Solutions/Source_ReferenceIutConcreteLocalIntegral.lean#L147) · [射影テンソルの単位球](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalArchimedeanTensor.lean#L120)

全成分が $p$ の上にあるとき、完備化のテンソル積の対数殻がその正規化環上で生成する部分加群を有限素点のテンソルに移す。これが有限素点での対数殻である。零環の場合は対数殻を $R$ とする。無限素点での対数殻は $\pi^{|I|}B_I$ である。どちらの対数殻も閉包はコンパクトである。有限素点での対数殻は $R$ を含む。$p$ が奇素数であり、素点の組に現れる各有限素点の分岐指数が $1$ ならば、対数殻は $R$ に等しい。 [対数殻のフィールド](../../../../Solutions/Source_ReferenceIutConcreteLocalTheory.lean#L48) · [無限素点の対数殻](../../../../Solutions/Source_ReferenceIutConcreteLocalArchimedean.lean#L169)

有限素点での対数体積は、集合と $R$ の加法的 Haar 測度を `toReal` でそれぞれ実数に移し、その比の自然対数を取って $\mathbb Q_p$ 上の次元で割った値である。零環の場合は各集合の対数体積は零である。無限素点では $B_I$ の測度が $1$ となる加法的 Haar 測度を用い、集合の測度を実数に移して自然対数を取り、実次元で割る。対数体積は対応する整領域上で零である。各整領域の単元倍の間では、対数体積は包含関係に関して単調である。正の実数 $t$ に対し、$tB_I$ の対数体積は $\log t$ である。 [体積のフィールド](../../../../Solutions/Source_ReferenceIutConcreteLocalTheory.lean#L56) · [有限素点での正規化](../../../../Solutions/Source_ReferenceIutConcreteLocalHaar.lean#L80) · [無限素点での正規化](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalArchimedeanTensorHaar.lean#L72)

いずれの有理素点でも、許容集合は空でなく可測であり、閉包がコンパクトで、Haar 測度が正かつ有限である。整領域とその各単元倍は許容である。有限素点で $U$ が許容で全成分が $p$ の上にあれば、$p$ 倍写像による逆像の対数体積は $\log p$ だけ増える。 [許容性のフィールド](../../../../Solutions/Source_ReferenceIutConcreteLocalTheory.lean#L66) · [素数倍写像](../../../../Solutions/Source_ReferenceIutConcreteLocalTheory.lean#L81)

有限素点では、許容領域を含む $aR$ で $a$ がテンソルの単元であるもののうち、包含関係に関して最小の領域が存在する。無限素点では、許容領域を含む正の半径の領域 $tB_I$ のうち、半径が最小のものが存在する。$0<t\le t'$ ならば $tB_I\subseteq t'B_I$ である。 [有限素点の最小包絡](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteHull.lean#L124) · [半径による最小包絡](../../../../Solutions/Source_ReferenceIutConcreteLocalArchimedean.lean#L136)

不定性の写像は因子の自己同型から誘導される。有限素点で全成分が $p$ の上にあるときは、各完備化の $\mathbb Q_p$-代数自己同型を用いる。零環のテンソルでは恒等写像のみを用いる。無限素点では各因子の $\mathbb R$-代数自己同型を用いる。いずれの写像の集合も恒等写像を含み、各写像は対応する対数殻をその中に移す。整領域の任意の単元倍について、これらの写像による像の和集合は許容である。対数殻の像の和集合も許容である。 [不定性のフィールド](../../../../Solutions/Source_ReferenceIutConcreteLocalTheory.lean#L86) · [有限素点での写像](../../../../Solutions/Source_ReferenceIutConcreteLocalFiniteIndeterminacy.lean#L46) · [無限素点での写像](../../../../Solutions/Source_ReferenceIutConcreteLocalArchimedean.lean#L176)

命題 1.4(iii) では全成分が $p$ の上にあると仮定する。添字 $j$ と `c j = Place.finite w` を満たす有限素点 $w$ を固定し、$\lambda=\operatorname{ord}_p(x)\ge 0$ を満たす零でない $x\in K_w$ を取る。与えられた実数 $d_i$ は対応する有限素点の正規化したディファレントの指数に等しいとする。それらの絶対分岐指数を $e_i$ と書く。`LocalTheory` のフィールドは、$\operatorname{incl}_j(x)R$ の各不定性の写像による像を $aR$ に含める単元 $a$ を与える。その対数体積は次の上界を満たす。$p-2$ の減法は $\mathbb N$ 上で行う。

$$
V(aR)\ \le\
\left(-\lambda+\sum_{i\in I}d_i+1\right)\log p+
\sum_{\substack{i\in I\\ p-2<e_i}}\bigl(3+\log e_i\bigr).
$$

[命題 1.4(iii)](../../../../Solutions/Source_ReferenceIutConcreteLocalProp14.lean#L103)

命題 1.4(iv) は有限素点での各不定性の写像 $\phi$ に対し $\phi(R)\subseteq R$ を与える。命題 1.5 は無限素点での各不定性の写像 $\phi$ に対し $\phi(\pi^{|I|}B_I)\subseteq\pi^{|I|}B_I$ を与える。 [不定性のフィールド](../../../../Solutions/Source_ReferenceIutConcreteLocalTheory.lean#L86) · [命題 1.5](../../../../Solutions/Source_ReferenceIutConcreteLocalArchimedean.lean#L188)

`PointThetaData.localTheory` は、この構成を同じ点データ $P$ のねじれ点体 $K=P.\mathrm{data}.\mathrm{Kt}$ に適用する。 [各点での使用箇所](../../../../Solutions/Source_ReferenceIutPointLocalTheta.lean#L29)
