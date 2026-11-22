# 对 Arithmetic Teichmuller Spaces 到 Joshi 3.12 的独立审计

**仓库所收版本没有给出正确证明。** 在满足假设的椭圆曲线上，第 III 篇的推论 9.11.1.1（`cor:cor312`）要求一个非正实数大于等于一个严格正数。即使改正末式的符号，前一定理所用的加权体积仍有独立的矛盾。在本文给出的同一组算术数据上，一个张量格按原文的定义同时具有体积 $1/5$ 和 $1/25$。[III，第 3649 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3649>) [III，第 3529 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3529>) [III，第 3554 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3554>)

“不可修补”在这里有明确的范围。保留原陈述，任何证明都会遇到第一处矛盾。保留原文对张量**子集**的体积定义及其权重，任何证明都会遇到第二处矛盾。对于更换定义并改正符号后的体积下界，现有论证缺少良定义的测度与比较定理。修订命题的真假仍待证明。

以下的 I、II、II.5、III、IV 对应 `refer/JoshiTeich` 中的五篇 `Arithmetic Teichmuller Spaces`。这里的“Joshi 3.12”取 III 的最终推论 `cor:cor312`。作者还把 II 的局部原型、III 在周期环上的上确界估计称作 3.12 的版本。三者的被估量不同。审计依据是两个指定目录的原文、文中调用的经典定理和下列直接计算。III 源文件的 SHA-256 前 16 位为 `b3df2cfb3107c171`。[II，第 1119 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.tex:1119>) [III，第 745 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:745>) [III，第 1747 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:1747>) [III，第 3647 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3647>)

## 1. 末式的两个符号

设 $\ell$ 为满足 III 假设的充分大奇素数，$m=\ell^*=(\ell-1)/2$。令 $S=\underline{\mathbb V}^{\mathrm{odd,ss}}$ 为选中的奇剩余特征分裂乘法约化处，$q_w$ 为该处的 Tate 参数，$a_w=|q_w^{1/(2\ell)}|_{L'_w}$。Tate 一致化给出 $0<|q_w|_{L'_w}<1$，故 $0<a_w<1$。选取另一支根或把局部绝对值取正次幂，都保持这个严格不等式。记 $\Theta=\widetilde\Theta_{\mathrm{Mochizuki}}^{\mathscr I}$，$V=\operatorname{Vol}(\Theta)$。[III，第 1009 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:1009>) [III，第 1042 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:1042>) [II，第 1187 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.tex:1187>)

III 定理 9.11.1（`th:moccor-Mochizuki-form2`）声称 $V\geq\prod_{w\in S}a_w^m$。暂且承认体积有定义且此定理成立。取实对数再除以 $m$，得到

$$
\frac1m\log V\ \geq\ \sum_{w\in S}\log a_w .
\tag{1}
$$

原文明确采用自然对数，并在最后一段用各局部 $\log V_p\leq0$ 解释 $-|\operatorname{LogVol}(\Theta)|=-\sum_p|\log V_p|$。在该约定和乘积公式 $V=\prod_p V_p$ 下，式 (1) 的左端可以写成 $-|\operatorname{LogVol}(\Theta)|/m$，右端也可以写成 $-\sum_w|\log a_w|$。第三篇最后印出的却是

$$
-\frac1m|\operatorname{LogVol}(\Theta)|
\ \geq\ -\sum_{w\in S}\log a_w .
\tag{2}
$$

只要 $S\neq\varnothing$，式 (2) 的右端严格正，左端至多为零。这甚至与 $V$ 的具体数值无关。若 $S=\varnothing$，右端等于零，式 (2) 要求左端也等于零。作者在 IV 证明初始数据存在性时明确指定了 $S\neq\varnothing$ 的情形。[III，第 3500 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3500>) [III，第 3617 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3617>) [III，第 3635 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3635>) [III，第 3649 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3649>) [IV，第 2030 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 4.tex:2030>)

最小的符号勘误是保留式 (1) 右端的 $\sum_w\log a_w$，或者在式 (2) 右端的各个对数上加绝对值。II 的局部版本确实写作两个负绝对值之间的比较。IV 调用 III 时也把下界写作负绝对值，但 IV 后来又用 $\sum_w\log a_w$ 定义一个带绝对值的量。前后用法能解释勘误的来由，不能代替对 $V$ 的估计。[II，第 1189 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.tex:1189>) [IV，第 2308 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 4.tex:2308>) [IV，第 2498 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 4.tex:2498>)

## 2. 一组满足算术假设的实例

取 $k=\mathbb Q(\alpha)$，$\alpha^3=2$，再取 $J=\alpha/5$。多项式 $T^3-2$ 在 $\mathbb Q$ 上由 Eisenstein 判别法不可约，判别式为 $-108$。模 5 有

$$
T^3-2=(T-3)(T^2+3T+4).
$$

二次因子的判别式为 $3\bmod 5$，是非平方。因此 5 在 $k$ 中有两个素位 $v_1,v_2$，局部次数分别是 $1,2$，两处均不分歧。$\alpha$ 在两处均为单位，所以 $\operatorname{ord}_{v_i}(J)=-1$。

在 $k$ 上取曲线 $C$ 和穿孔曲线 $X$ 为

$$
 C:\quad y^2+xy=x^3-\frac{36}{J-1728}x-\frac{1}{J-1728},
 \qquad X=C-\{O\}.
$$

由 Weierstrass 不变量得 $c_4=J/(J-1728)$、$\Delta=J^2/(J-1728)^3$，故 $j(C)=J$，模域恰为 $\mathbb Q(J)=k$。在两个 $v_i$ 处，此方程整，$c_4$ 是单位，$\operatorname{ord}_{v_i}(\Delta)=1$。约化方程为 $y^2+xy=x^3$，节点的两条切线是 $y=0$ 和 $y=-x$，均在剩余域上有定义。因此两处都是分裂乘法约化，且在任意有限扩张后仍然如此。

取 $L=k(i,C[6])$。这是 $k$ 的有限 Galois 扩张，无实嵌入，且全部 6 阶挠点在 $L$ 上有定义。$X$ 属于 III 所取的数域上单穿孔椭圆曲线的严格 Belyi 型情形。$J$ 在 5 处有极点，而复乘椭圆曲线的 $j$ 是代数整数，故 $C$ 没有复乘。由 Serre 对数域上无复乘椭圆曲线的开像定理，对一切充分大的素数 $\ell$，$G_L$ 的模 $\ell$ 像包含 $\mathrm{SL}_2(\mathbb F_\ell)$。取这样的 $\ell>5$ 且 $\ell\nmid[L:k]$，令 $L'=L(C[\ell])$，并为 $k$ 的每一素位选择一个 $L'$ 上方的素位。这逐项给出了 III 的初始数据，特别是 $v_i$ 上方选取的 $w_i$ 均在 $S$ 内。这个存在性论证也独立于 IV 中针对一族曲线选择 $\ell$ 的有效界。[II，第 595 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.tex:595>) [III，第 997 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:997>) [III，第 1023 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:1023>) [IV，第 1888 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 4.tex:1888>) [Serre，Inventiones 15 (1972), 259–331](https://doi.org/10.1007/BF01405086)

## 3. 同一张量格得到两个不同体积

III 对每个 $p$ 进域 $E_i$ 取加法 Haar 测度 $\mu_i(\mathcal O_{E_i})=1$，然后规定张量空间 $T=\bigotimes_{\mathbb Q_p}E_i$ 中的格满足

$$
 \operatorname{Vol}^{\Gamma}
 \left(\bigotimes_{\mathbb Z_p} V_i\right)
       =\prod_i\mu_i(V_i)^{\gamma_i},
 \qquad \gamma_i=\frac1{[L'_{w_i}:k_{v_i}]} .
\tag{3}
$$

III 将左端称为张量空间的可测子集上的函数，并把它用于子集的 hull。这里直接取定义中的中心为零的整格。III 的有理张量空间以 $\bigoplus_{w\mid p}L'_w$ 为因子，展开含有 $L'_{w_1}\otimes_{\mathbb Q_p}L'_{w_2}$ 这样的混合分量。[III，第 3053 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3053>) [III，第 3123 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3123>) [III，第 3495 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3495>) [III，第 3522 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3522>) [III，第 3533 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3533>) [III，第 3553 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3553>)

令 $E_i=L'_{w_i}$，$d_i=[E_i:\mathbb Q_p]$，$M=\mathcal O_{E_1}\otimes_{\mathbb Z_p}\mathcal O_{E_2}\subset T$。在 $T$ 内有同一个子集

$$
 (p\mathcal O_{E_1})\otimes_{\mathbb Z_p}\mathcal O_{E_2}
 =pM
 =\mathcal O_{E_1}\otimes_{\mathbb Z_p}(p\mathcal O_{E_2}).
$$

因为 $\mathcal O_{E_i}$ 是秩 $d_i$ 的自由 $\mathbb Z_p$ 模，$p\mathcal O_{E_i}$ 的指数为 $p^{d_i}$。式 (3) 用第一种表示给出 $p^{-d_1\gamma_1}$，用第二种表示给出 $p^{-d_2\gamma_2}$。所以这条规则要定义在张量格上，至少必须有 $d_1\gamma_1=d_2\gamma_2$。而根据 III 的实际权重，塔式公式给出

$$
 d_i\gamma_i=\frac{[L'_{w_i}:\mathbb Q_p]}{[L'_{w_i}:k_{v_i}]}
              =[k_{v_i}:\mathbb Q_p].
$$

代入第 2 节的数据，$p=5$，两个值分别是 $1$ 和 $2$。于是同一 $5M$ 的体积须同时等于 $5^{-1}$ 和 $5^{-2}$。这用的是作者为算术应用选定的权重，且完全避开了 $\Theta$ 的具体形状。带权乘积可以定义在带标签的因子格元组上。将它用于 $T$ 的子集及其 hull，需要它对同一子集的所有表示取相同的值。式 (3) 在本例排除了这种可能。[III，第 3554 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3554>) [III，第 3567 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3567>) [III，第 3576 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3576>)

同一问题也说明为什么局部几何中的“绝对值”必须指定归一化。对 $E/\mathbb Q_p$ 的通常延拓绝对值 $|p|_E=p^{-1}$，规范化 Haar 测度满足 $\mu_E(a\mathcal O_E)=|N_{E/\mathbb Q_p}(a)|_p=|a|_E^{[E:\mathbb Q_p]}$。例如在非分歧二次扩张中，$\mu_E(p\mathcal O_E)=p^{-2}$。若以 Haar 模数作绝对值，III 第 3503 行的写法成立，但它在基域标量 $p$ 上也取 $p^{-2}$。把这两种归一化互换时，次数要保留。式 (3) 的矛盾直接用格的指数得出，选择绝对值记号无法消去它。[III，第 1941 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:1941>) [III，第 3503 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3503>)

## 4. 从局部算术全纯结构到周期环估计

在有限扩张 $E/\mathbb Q_p$ 上，算术全纯结构保留 $E\hookrightarrow K$、倾斜域的识别 $K^\flat\simeq F$ 和曲线的 $K$ 值几何基点。带有同一 tilt 的不同 untilt 可以存在。倾斜给出值群的识别，因而可以比较各分量取出的正实数，而无需识别各个 $K$ 中的一般元素。对全局数域，II.5 把各处数据编成一个 arithmeticoid，并引入正指数 $\alpha_v$ 使 $|x|_{K_v}^{\alpha_v}=|x|_v$，以恢复数域的积公式。III 则声明此后的 arithmeticoid 一律归一化。计算时必须记住幂次作用在归一化之前还是之后。[AHS，第 700 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Holomorphic Structures.tex:700>) [I，第 593 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 1.tex:593>) [II，第 550 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.tex:550>) [II.5，第 1037 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.5.tex:1037>) [II.5，第 1125 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.5.tex:1125>) [III，第 837 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:837>)

### 局部赋值的平方缩放

取 $F=\mathbb C_p^\flat$，$0<|a|_F<1$。在 Fargues–Fontaine 构造中，第 $j$ 个点由 Witt 向量 $[a^{j^2}]-p$ 给出。在其剩余域 $K_j$ 上采用由 $F$ 诱导的实值赋值，则 $v_j(p)=v_F(a^{j^2})=j^2v_1(p)$。以最后一个分量 $K_m$ 为标准，便有 $v_j(p)=(j^2/m^2)v_m(p)$。若把同一个赋值域 $(E,|\cdot|_E)$ 同时等距嵌入每个 $K_j$，则每个 $|p|_{K_j}$ 又都等于 $|p|_E$。因此上述非平凡缩放使用的是各自诱导的等价赋值。I 第 593 行要求等距嵌入，随后第 595 行允许连续嵌入诱导等价赋值。II 和 III 定义所用的元组时又要求等距。这一差别在张量积上有可检验的后果，见第 5 节。[I，第 595 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 1.tex:595>) [II，第 815 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.tex:815>) [II，第 834 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.tex:834>) [III，第 1145 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:1145>) [III，第 1489 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:1489>)

### 局部 θ 函数的实际取值

II 第 663 行的级数，约去前因子后是
$$
 \theta_M(u)=\sum_{n\in\mathbb Z}q^{n(n+1)/2}u^{2n+1}.
$$
换指标 $n\mapsto -n-1$ 给出 $\theta_M(u^{-1})=\theta_M(u)$。在奇剩余特征且 $0<|q|<1$ 时，$u=1$ 的两项常数贡献为 $2$，其余项均在极大理想中，故 $\theta_M(1)\ne0$。这与紧接着使用的反对称性和 $\theta_M(1)=0$ 冲突。还可直接核对真正进入估计的 θ 值。取 $p\ne\ell$、$1\leq j\leq m$，$\zeta$ 为本原 $\ell$ 次单位根。在 $u=q^{j/(2\ell)}\zeta$ 处，第 $n$ 项的 $q$ 指数是
$$
 b_n=\frac{n(n+1)}2+(2n+1)\frac{j}{2\ell}.
$$
因 $b_{n+1}-b_n=n+1+j/\ell$，最小值唯一，在 $n=-1$，值为 $-j/(2\ell)$。分母 $\theta_M(\zeta)$ 的首项和是 $\zeta+\zeta^{-1}$，其剩余类非零，因为 $\bar\zeta$ 的阶为奇素数 $\ell$。故这份级数给出的比值绝对值是 $|q|^{-j/(2\ell)}$，II 第 689 行却写为 $|q|^{-j^2/(2\ell)}$。在 $j=2$ 已有区别。此外，即使只取 $j=1$，$\xi_1$ 的绝对值也是 $|q|^{1/(2\ell)}$。II 第 986 行和 III 第 1532 行把它与同一曲线的原 Tate 参数 $q$ 相等同，两者的赋值不同。[II，第 663 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.tex:663>) [II，第 689 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.tex:689>) [II，第 983 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.tex:983>) [III，第 1530 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:1530>)

### 周期环上的上确界下界

II 的局部原型实际在每个 $K_j$ 中提升同一个第一 θ 值。若用 Tate 根 $x=q^{1/(2\ell)}$ 或同绝对值元素，且以 $K_m$ 为标准，令 $a=|x|_{K_m}\in(0,1)$。Teichmüller 提升在相应范数下有大小 $|[x_j]|_\rho=|x|_{K_j}$。依上述诱导尺度，
$$
 \prod_{j=1}^{m}|[x_j]|_\rho=a^{s_m},\qquad
 s_m=\sum_{j=1}^m\frac{j^2}{m^2}
     =\frac{(m+1)(2m+1)}{6m}\leq m.
$$
因此 $a^{s_m}\geq a^m$，$m>1$ 时为严格不等式。III 在周期环乘积中选同一个全局标准元组，各 $w\in S$ 取这样的提升，其余有限处的坐标取 $[1]$。在所选元组按这些尺度确实属于目标集合的条件下，有限相乘并取上确界这一推理成立。它给出的是 $\widetilde\Theta_{\mathrm{Joshi}}^{\mathbb B_{L'}}$ 的大小。III 的上同调版本另行构造集合并另行定义体积。[II，第 940 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.tex:940>) [II，第 1128 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.tex:1128>) [II，第 1153 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.tex:1153>) [III，第 1552 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:1552>) [III，第 1700 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:1700>) [III，第 1754 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:1754>)

## 5. 进入上同调和张量空间时发生了什么

### Kummer 类与 Bloch–Kato 对数

III 区分了 Tate 参数的 Kummer 类与单位的 Kummer 类。$q_w$ 的赋值非零，而取 $x=q_w^{1/(2\ell)}$、$u=1+p^*x$（奇 $p$ 时 $p^*=p$，$p=2$ 时 $p^*=4$），其相容根塔给出单位类 $\kappa(u)$，有理化后属于 $H^1_e(E,\mathbb Q_p(1))=H^1_f(E,\mathbb Q_p(1))$。这里 $E=L'_w$，上同调记号省略了 $G_E$。在上述输入上，$|\log(1+p^*x)|=|p^*x|$，因为这里 $|p^*x|<|p|^{1/(p-1)}$，每个高次项的绝对值都严格小于一次项。故 $|\log(1+p^*x)/p^*|=|x|$ 是可用的局部恒等式。[III，第 2802 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:2802>) [III，第 3151 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3151>) [III，第 3188 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3188>) [III，第 3199 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3199>) [III，第 3398 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3398>)

III 把 $\log_{\rm BK}$ 明确定为通常 Bloch–Kato 指数的逆，又在同一句写 $\log_{\rm BK}\kappa(u)=\log_p(u)/p^*$。对 $\mathbb Q_p(1)$ 作文中给出的通常指数识别，在指数收敛处有 $\exp_{\rm BK}(z)=\kappa(\exp_p z)$，所以逆映射取值为 $\log_p(u)$。例如奇 $p$ 时在 $\mathbb Q_p$ 取 $u=1+p$，$\log_p(u)$ 的赋值为 1，$\log_p(u)/p$ 的赋值为 0。通常单位 Kummer 整格在通常对数下的像是 $p\mathbb Z_p$，文中定义的 log-shell 此时是 $\mathbb Z_p$。用 $p^{*-1}\log_{\rm BK}$ 作为到该壳的坐标可以解释除法，但其逆映射也必须相应改变。III 正用这个因子将好有限处的贡献算为单位，并在坏处读出 $|x|$。[III，第 2845 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:2845>) [III，第 3212 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3212>) [III，第 3224 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3224>) [III，第 3251 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3251>) [III，第 3451 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3451>)

### 标准元组用哪个分量作基准

III 定义 $\mathbf z_\Theta$ 时指定第 $m$ 个分量为标准点。其缩放定理相对于第 1 个分量给出 $j^2$，相对于第 $m$ 个分量才给出 $j^2/m^2$。在 `th:moccor-Mochizuki-form1` 的证明里，原文第 3467 行将后一个指数用在第 1 个分量上。代 $j=1$，所得等式为 $a=a^{1/m^2}$，其中 $a=|q_{w;1}^{1/(2\ell)}|_{L'_w,1}\in(0,1)$，$m\ge2$。改用第 $m$ 个分量作右端基准，可恢复第 4 节的实数计算。还须将该计算送到定义 $\Theta$ 时所取的共同空间。[III，第 1145 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:1145>) [III，第 1229 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:1229>) [III，第 3430 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3430>) [III，第 3467 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3467>)

### 张量范数的标量检验

III 先将不同 arithmeticoid 的上同调类经拓扑群同构汇集到固定空间，取凸闭包，再将元组送到张量空间。映射 $(u,v)\mapsto u\otimes v$ 在各因子上分别线性。若它如原文所写也是直积上的线性映射，就应保持加法。但 $(1,0)$ 和 $(0,1)$ 的像均为零，两者之和的像为 $1\otimes1\ne0$。以此定义**集合的像**仍有意义。要在像上计算同一范数，则必须遵守张量积的平衡关系。[II.5，第 1606 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 2.5.tex:1606>) [III，第 3056 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3056>) [III，第 3261 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3261>) [III，第 3329 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3329>) [III，第 3458 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3458>)

具体地，若范数满足 $\|u\otimes v\|=|u|_1|v|_2$，从 $p\otimes1=1\otimes p$ 立即得到 $|p|_1=|p|_2$。同一个 $\mathbb Q_p$ 上的 Banach 空间使用同一标量绝对值，标准交叉范数定理正有这个前提。III 的张量容器在不同 $j$ 上取因子，并且明确要在这些因子上记住缩放。若在两个槽中保留第 4 节的不同诱导尺度，则 $|p|_2=|p|_1^{4}\ne|p|_1$（取 $j=1,2$），这样的交叉范数无法存在。若先统一标量范数，便可使用交叉范数定理，但必须按统一后的范数重算见证点。拓扑群同构、相同值群以及全局 Frobenius 的作用都没有在原文中给出这个保数值的比较。此处排除的是让**同一个**张量范数同时实现这两种尺度。[III，第 1947 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:1947>) [III，第 1966 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:1966>) [III，第 3053 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3053>) [III，第 3088 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3088>) [III，第 3097 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3097>) [III，第 3458 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3458>)

## 6. 从一个点到一个有体积的 hull

III 定义的 holomorphic hull 是在分解 $T\simeq\prod_\alpha F_\alpha$ 后，逐分量包含原集合的最小整理想盒 $\prod_\alpha\lambda_\alpha\mathcal O_{F_\alpha}$。随后 `pr:convexes-and-hulls` 将这种 hull 与 $\mathbb Q_p$ 向量空间的普通非阿基米德凸闭包等同。两种闭包对下面这个张量格给出不同答案。[III，第 3569 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3569>) [III，第 3596 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3596>)

取奇素数 $p$，$E=\mathbb Q_p(\pi)$，$\pi^2=p$，用横线表示非平凡共轭。令 $P=\mathcal O_E\otimes_{\mathbb Z_p}\mathcal O_E\subset E\otimes_{\mathbb Q_p}E$。在同构 $f(a\otimes b)=(ab,a\bar b)$ 下，$f(P)$ 是 $E\oplus E$ 的一个紧 $\mathbb Z_p$ 格，已经凸且闭。因 $\bar b\equiv b\pmod\pi$ 对所有整元成立，其像中两个坐标模 $\pi$ 总相同。因此 $(1,0)\notin f(P)$。但 $f(a\otimes1)=(a,a)$ 表明两个坐标的投影都等于 $\mathcal O_E$，故逐分量 hull 是整个 $\mathcal O_E\oplus\mathcal O_E$，含有 $(1,0)$。线性同构保持凸性这一事实，不能证明这两种最小性相同。

这具体影响 `th:moccor-Mochizuki-form2`。其证明从“集合含有标准点给出的类”推出“集合含有由 $\tau_j\mathcal O_{E_j}$ 张成的整个张量格”，以便调用 `le:volume-lemma3`。该引理把格包含作为**假设**。对原集合或普通凸闭包，一个点不足以给出此包含。若直接估计逐分量 hull，可以验证一个较弱的包含关系。设 $t=\bigotimes_j\tau_j$ 各分量非零且整。若 $t\in U$，则 $\operatorname{hull}(U)$ 包含 $t\prod_\alpha\mathcal O_{F_\alpha}$，因为它的每个分量理想都含有 $t_\alpha$。这解释了作者希望从一个点得到正体积的想法。完成这条路线仍须在同一个 hull 上给出良定义的体积，并用其实际权重重算下界。第 3 节的反例说明，原文在这一步采用的权重无法定义所需的体积。[III，第 3576 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3576>) [III，第 3604 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3604>) [III，第 3624 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:3624>)

## 7. 两个源目录对判定的作用

`refer/Joshi2` 的 `Anabelomorphy` 给出系数为 $\mathbb Q_p(1)$ 时 $H^1_f,H^1_e$ 的有理向量空间同构，也说明 tilting 如何比较乘法逆极限。这支持 III 用共同容器汇集上同调类。`Algebraization` 的相关定理给出带幺半群作用的形式群及其普遍性质。Fargues–Fontaine 曲线一文比较基本群与曲线同构类。它们给出的同构或参数空间都没有断言式 (3) 对张量格的不同表示取值相同。FAQ 提及使用全局 Frobenius 的修订，IV 的现有文本也确实在下界中使用了移位的标准点。移动标准点不改变 $pM$ 的两种表示。目录中的正特征向量丛与 oper 文章提供几何类比。III 附录的几何版 3.12 使用单值化群中提升元素的函数值之和，其上确界定义不能推出式 (2) 中 Tate 参数的算术估计。[Anabelomorphy，第 1023 行](</home/admin-wsl/Coq/abc/refer/Joshi2/On Mochizuki's idea of Anabelomorphy and its applications.tex:1023>) [Anabelomorphy，第 2088 行](</home/admin-wsl/Coq/abc/refer/Joshi2/On Mochizuki's idea of Anabelomorphy and its applications.tex:2088>) [Algebraization，第 432 行](</home/admin-wsl/Coq/abc/refer/Joshi2/Algebraization of Mochizuki's anabelian variation of ring structures, perfectoid geometry and formal groups.tex:432>) [FF 曲线，第 355 行](</home/admin-wsl/Coq/abc/refer/Joshi2/The Absolute Grothendieck Conjecture is false for Fargues-Fontaine Curves.tex:355>) [FAQ，第 205 行](</home/admin-wsl/Coq/abc/refer/Joshi2/joshi-mochizuki-FAQ.md:205>) [IV，第 2338 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 4.tex:2338>) [III，第 4414 行](</home/admin-wsl/Coq/abc/refer/JoshiTeich/Arithmetic Teichmuller Spaces 3.tex:4414>)

就用户所问的算术结论而言，第 2 节的曲线排除了按原样证明 `cor:cor312` 的可能，第 3 节的格排除了只改末式符号就完成原证明的可能。第 4 节给出了周期环上确界估计所需的局部数值计算，并指出见证元进入指定集合所需要的赋值约定。要得到修订后的**体积**下界，仍缺少与实际 θ 集合、张量关系、局部次数和 hull 同时相容的比较定理。对 Mochizuki 原典的另一种构造或对所有未来修订的普遍不可能性，以上反例没有作出判定。
