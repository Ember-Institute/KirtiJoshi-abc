# IUT 独立审查

**本次审查定位到的主要缺口在 IUT III 推论 3.12 的证明第 (xi-e) 至 (xi-f) 步。** 初始 Θ 数据经过前面的构造，给出一个固定的 q-pilot 对数体积和一族 Θ-pilot 可能像。第 183 页把二者放到同一尺度上。第 184 页需要证明，Θ 可能像的全纯包络（holomorphic hull）的对数体积至少达到这个固定值。原文从「在固定 q 体积的条件下仍可执行该构造」推出「这个 q 体积属于输出允许的范围」。该步明列的性质不足以推出这一成员关系。本次审查没有得到一组满足 IUT 全部初始条件且使 3.12 不等式反向的算术数据。[IUT III，推论 3.12，第 173–175 页](<../refer/Mochizuki/Inter-universal Teichmuller Theory III.pdf#page=173>) · [证明第 (xi-d) 至 (xi-f) 步，第 183–184 页](<../refer/Mochizuki/Inter-universal Teichmuller Theory III.pdf#page=183>)

`refer/iut` 已形式化从**其具体 3.12 变体的全称命题**推出**经典 abc 猜想**的条件证明。该变体仍是最终定理的显式前提。III 第 129 页还另有一处可直接订正的等式，按定义计算，作者例子中所有等体积包络的并严格小于全纯包络。[Lean 条件定理](../refer/iut/Iut/Tripod/ClassicalAbcGenuineCanLift.lean#L40) · [变体与论文的对应边界](../refer/iut/Iut/Cor312/Statement.lean#L39) · [IUT III，第 129 页](<../refer/Mochizuki/Inter-universal Teichmuller Theory III.pdf#page=129>)

## 一　从初始数据到两个待比较的体积

1. **固定曲线、素数和处。** IUT I 定义 3.1 从数域 $F$、一次穿孔椭圆曲线 $X_F$、素数 $\ell\geq5$ 及相关覆盖、处和标记出发。指定的乘法坏约化处非空，剩余特征为奇数。定义还对扭点、Galois 像及处的选取加了条件。推论 3.7 构造相邻 Hodge theaters 之间的 Θ-link，给出特定 Frobenioid 数据之间非空的全体同构（full poly-isomorphism）。这个箭头传递哪些结构，在推论中有明确规定。尤其不能直接把它当成两个局部域之间保持加法 Haar 测度的环同构。[IUT I，定义 3.1，第 61–63 页](<../refer/Mochizuki/Inter-universal Teichmuller Theory I.pdf#page=61>) · [推论 3.7 和注 3.7.1，第 88–89 页](<../refer/Mochizuki/Inter-universal Teichmuller Theory I.pdf#page=88>)

2. **坏处上的平方指数可以独立算出。** 设 $q_X$ 是该处的 Tate 参数，$i^2=-1$，$\vartheta$ 取 Mochizuki 在 *The Étale Theta Function* 命题 1.4 的归一化。将级数中的求和指标平移，得到 $\vartheta(q_X^{j/2}U)=(-1)^j q_X^{-j^2/2}U^{-2j}\vartheta(U)$。在 $U=i$ 处，$(-1)^ji^{-2j}=1$，且 $\vartheta(i)=2i+O(q_X)$ 在奇剩余特征处是单位。因此 $\vartheta(iq_X^{j/2})/\vartheta(i)=q_X^{-j^2/2}$。取此比值的倒数再开 $\ell$ 次根，赋值等于 $\underline q_v^{\,j^2}$ 的赋值，其中 $\underline q_v^{\,2\ell}=q_X$。II 注 2.5.1 明确给出相应的 $\mu_{2\ell}$ 轨道，各标签的单位根选择可以独立。由这一处的求值通往全局体积，还要经过张量、按标签平均和取包络。[Étale Theta，命题 1.4，第 20 页](<../refer/Mochizuki/The Etale Theta Function and its Frobenioid-theoretic Manifestations.pdf#page=20>) · [IUT I，例 3.2(iv)，第 71 页](<../refer/Mochizuki/Inter-universal Teichmuller Theory I.pdf#page=71>) · [IUT II，注 2.5.1，第 72–73 页](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20II.pdf#page=72)

3. **确定横向箭头的源和靶。** II 推论 3.5、3.6 组织上述求值，推论 4.10 处理标签及相应的 links。III 定义 3.8 给出 LGP 版本的 Θ-pilot、q-pilot 和 log-theta-lattice。推论 3.12 选中从 $(0,0)$ 到 $(1,0)$ 的一条横向箭头。由第 (i) 和 (xi-a) 步，箭头在值群部分确实将源端 Θ-pilot 对应到目标端 q-pilot，两者在这里按全局实化 Frobenioid 中的对象理解。接受这项对应之后，还要考察算法在目标列的加性 log-shell 中究竟产生了哪些区域。[IUT II，推论 4.10，第 158 页起](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20II.pdf#page=158) · [IUT III，定义 3.8，第 112 页起](<../refer/Mochizuki/Inter-universal Teichmuller Theory III.pdf#page=112>) · [第 (xi-a) 步，第 181 页](<../refer/Mochizuki/Inter-universal Teichmuller Theory III.pdf#page=181>)

4. **确定体积的归一化。** III 命题 3.9(i) 在有限处令整结构的对数体积为零，使乘以有理素数 $p$ 引起 $-\log p$ 的位移。(ii) 处理 procession 的归一化。(iii) 在几乎处处局部贡献为零的族上求和，并把相应算术线丛的全局度识别为对数体积。(iv) 给出同一列沿竖直 log-link 的体积相容性。定理 3.11 随后给出 Θ 数据的多辐表示、Kummer 同构及其不定性。第 (x) 步说明 (Ind1)、(Ind2) 下相应对数体积不变，(Ind3) 给出从上方的界。要用这个界控制 $q$，仍须把 $q$ 的具体值接到被控制的对象上。[IUT III，命题 3.9，第 115–118 页](<../refer/Mochizuki/Inter-universal Teichmuller Theory III.pdf#page=115>) · [定理 3.11，第 153 页起](<../refer/Mochizuki/Inter-universal Teichmuller Theory III.pdf#page=153>) · [第 (x) 步，第 180–181 页](<../refer/Mochizuki/Inter-universal Teichmuller Theory III.pdf#page=181>)

保留论文的符号方向，记 $Q=|\log(\underline q)|>0$，$x=-Q$，$T=-|\log(\underline\Theta)|$。这里的 $T$ 是**可能像的并集取全纯包络之后**的带符号对数体积，按论文指定的非零标签平均，计入 (Ind1)–(Ind3)。$x$ 来自固定的 q-pilot，计算它时不施加这三种不定性。论文起初允许 $T=+\infty$，在第 175 页以各局部区域的紧性及全局对数体积的定义主张 $T$ 有限。全局求和的有限支撑条件见命题 3.9(iii) 与注 3.9.7(i)。下文即便承认这项有限性，仍须证明 $T\geq x$。当 $T\geq0$ 时它立即成立，实质是 $T<0$ 的情形。在 $T$ 有限、$Q>0$ 时，$T\geq-Q$ 等价于每个满足 $T\leq C_\Theta Q$ 的 $C_\Theta$ 都满足 $C_\Theta\geq-1$，反向只需取 $C_\Theta=T/Q$。[IUT III，推论及证明开头，第 173–175 页](<../refer/Mochizuki/Inter-universal Teichmuller Theory III.pdf#page=174>) · [注 3.9.7(i)](../refer/Mochizuki/Inter-universal_Teichmuller_Theory.md#L3508)

## 二　第 184 页的包含关系从哪里来

第 (xi-a) 步沿横向 link 识别两个 pilot 的抽象对象。另一条计算路径从多辐算法的实际输出出发，在第 1 列取可能像的并、全纯包络、适当正张量幂的行列式，再取归一化算术度。第 (xi-c) 至 (xi-d) 步解释了为什么要取行列式，输出的局部算术向量丛可以有高于一的秩，而 q-pilot 由算术线丛给出。经过这些操作，作者在同一个 $\mathbb R$ 中比较以下两项。[IUT III，第 182–183 页](<../refer/Mochizuki/Inter-universal Teichmuller Theory III.pdf#page=182>)

$$
x\in\mathbb R,\qquad D_T=\{s\in\mathbb R:s\leq T\}\subseteq\mathbb R.
$$

第 (xi-e) 步所说的 **IPL** 是输入输出经 prime-strip 同构相关联。这里的 prime-strip 包含特定的局部和全局数据。**SHE** 表示同一构造及其输出能在两端的算术全纯结构中表达。原文在此步把目标列的条件写成，固定输入的 pilot 对数体积为 $x$ 时，操作依然 “valid/executable/well-defined”。作者还说明 **APT** 是这种构造提供的平行移动，未给出把一个集合区域逐点搬到另一个区域的函数。第 (xi-f) 步随即把输出称为对输入体积的构造，允许 “perhaps only up to some sort of ‘approximation’”，并写下 $x\in D_T$。一旦有这个成员关系，$x\leq T$ 确实只需展开定义。待证之处恰在这个成员关系。[IUT III，注 3.11.1(iii)–(v)](../refer/Mochizuki/Inter-universal_Teichmuller_Theory.md#L3990) · [第 (xi-e) 至 (xi-f) 步，第 184 页](<../refer/Mochizuki/Inter-universal Teichmuller Theory III.pdf#page=184>)

### 用作者的实数模型检验这一步

III 注 3.12.2(ii) 给出一个可以完全算清的类比。一个标记 $*$ 赋值为 $-h$，另一项赋值在加入不定性后取范围 $(-\infty,-2h+\varepsilon]$，其中 $h,\varepsilon>0$。按作者的设定，把带标签的两条实数轴识别成同一条。取 $h=1,\ \varepsilon=\tfrac12$，从输入 $x=-h$ 按确定公式 $F(x)=(-\infty,2x+\varepsilon]$ 构造输出，就得到

$$
x=-1,\qquad F(x)=(-\infty,-3/2],\qquad x\notin F(x).
$$

固定 $x$ 不妨碍执行 $F$，两项赋值也使用同一个标记。若需从输出选一个实际的数，端点 $2x+\varepsilon$ 已经给出这样的选择。整个输出与 $x$ 的距离仍为 $1/2$。因此，「两项都能构造」这个读法不足以推出成员关系。若把「同时成立」读成**同一个未知的实数** $s$ 同时满足 $s=-h$ 和 $s\leq-2h+\varepsilon$，结论当然成立，但这两个条件有公共解当且仅当 $h\leq\varepsilon$，恰好就是该模型的待证不等式。作者在第 189 页说第二个逻辑蕴含 $(A\land B)\Rightarrow B$ 是形式的，真正需要算术证明的是第一个蕴含中「同一个数值见证」的存在。这个例子反驳弱读法下的逻辑推断，保留了从完整算术结构证明更强相容性的可能。[IUT III，注 3.12.2(ii)，第 188–191 页](<../refer/Mochizuki/Inter-universal Teichmuller Theory III.pdf#page=189>) · [原文实数模型的两个赋值及结论](../refer/Mochizuki/Inter-universal_Teichmuller_Theory.md#L4578)

### 全局度和闭合的同构链能否供给这个见证

III 注 3.9.5(vii) 的 (Ob5) 为全部可能区域取同一个包络。(Ob8) 用目标列的 log-Kummer 对应校正单位部分与加性 log-shell 之间的竖直错位。(viii) 的 (sQ3) 至 (sQ5) 依次处理包络的行列式、竖直错位和对数体积。(ix) 的 (cQ3)、(cQ4) 还考虑带局部化相容同构的全局对象，说明在取最后的体积以前，prime-strip 的同构链在容许的商不定性下闭合。原文在 (iQ5) 写明最后取数值时会忘掉局部 Galois 群和单位数据。第 183 页由此把两个数放在同一归一化下比较。[IUT III，注 3.9.5(vii)–(ix)，第 134–144 页](<../refer/Mochizuki/Inter-universal Teichmuller Theory III.pdf#page=134>) · [闭合发生的层次](../refer/Mochizuki/Inter-universal_Teichmuller_Theory.md#L3462)

共同容器还容许不同的数值，这一点可以在作者的值群数据上直接核对。III 注 2.4.2(iii)–(vi) 取有序加法幺半群 $M\simeq\mathbb R$ 和负的 pilot 元素 $\eta$。局部比较映射是乘固定权重，有限处取 $\eta$ 生成的子幺半群，无穷处取非正半轴。在 $M=\mathbb R$ 的坐标中，令 $s>0$，映射 $t\mapsto st$ 同时作用在全局与各局部副本上。它与每个固定权重的乘法交换，把 $\mathbb N\eta$ 送到 $\mathbb N(s\eta)$，也保持非正半轴。于是这两套有标记的数据同构，而同一预先选定的实坐标中 $\eta$ 和 $s\eta$ 可以不同。作者在 (vi) 也明说，共同的全局容器中可以比较不同的负 pilot 元素。该运算只检验这一层数据。完整的第 1 列另有固定的环、整结构和归一化，将任意 $s$ 当成全套 IUT 数据的自同构同样没有依据。[IUT III，注 2.4.2，第 89–91 页](<../refer/Mochizuki/Inter-universal Teichmuller Theory III.pdf#page=90>)

第 (xii) 步已经注意到，只凭局部 Frobenioid 的同构类，给定的格可能与它的 $p^N$ 倍无法区分，因此作者使用全局实化 Frobenioid。注 3.12.2(v) 还解释，目标列固定环结构，取包络吸收局部单位的不定性，取体积吸收竖直 log-link 选择的不定性。承认同一全局线丛能在该列精确计算度，仍需说明，沿横向箭头识别的那个 q-pilot，其度由**另一条路径实际构造的 Θ 包络**所控制。第 (xi-h) 步指出整个构造依赖一次幂的 étale theta 函数，不能任意换成高次张量幂。这限定了可用的算术对象，尚未提供一次幂情形的成员见证。[IUT III，第 (xi-h)、(xii) 步，第 185 页](<../refer/Mochizuki/Inter-universal Teichmuller Theory III.pdf#page=185>) · [注 3.12.2(v)，第 194–195 页](<../refer/Mochizuki/Inter-universal Teichmuller Theory III.pdf#page=194>)

补上该步的一个充分条件是，对每组初始数据、每个 $\delta>0$，在第 1 列实际 Θ 可能像的全纯包络内构造一族可测子区域 $B_\delta$，使其全局对数体积按论文规定的全部处与同一组权重有定义，并满足

$$
\operatorname{logVol}(B_\delta)\ \geq\ x-\delta .
$$

由对数体积的单调性，$\operatorname{logVol}(B_\delta)\leq T$，令 $\delta\downarrow0$ 即得 $x\leq T$。行列式的路线也有一个充分条件。在目标列固定的全局 Frobenioid 中，若能找到这类子区域的归一化行列式线丛 $L$，并证明 $L$ 与同一张量幂下的 q-pilot 线丛同构，就可用全局算术度相等给出 $\operatorname{logVol}(B_\delta)=x$。原文引用给出了构造的可执行性、同构层次的闭合和同列的体积相容性。我在这些引用中没有找到对实际输出给出这一侧估计的引理。[IUT III，注 3.9.5(vii) (Ob3)–(Ob4)](<../refer/Mochizuki/Inter-universal Teichmuller Theory III.pdf#page=131>) · [命题 3.9(iii)，第 117 页](<../refer/Mochizuki/Inter-universal Teichmuller Theory III.pdf#page=117>)

### 逐处比较能否补上全局下界

取 $p=421$、$\ell=7$，在 $\mathbb Q_p$ 上取 Tate 曲线 $E(q)$，其中 $q=p^{30}$。因为 $4\cdot3\cdot5\cdot7$ 整除 $p-1$，所需单位根都在基域中。$q$ 的 $30$ 次根是 $p$，所以 $E[30]$ 有理。$\ell$ 扭点域为 $k=\mathbb Q_p(p^{1/7})$，因为此时只需添加 $q^{1/7}=p^{30/7}$，且 $7$ 与 $30$ 互素。这是分歧指数 $7$ 的温和扩张。按 $\operatorname{ord}(p)=1$，其不同理想的阶为 $d_k=6/7$，而 IUT I 所用的 $\underline q=q^{1/(2\ell)}$ 有阶 $15/7$。[IUT I，例 3.2(iv)](<../refer/Mochizuki/Inter-universal Teichmuller Theory I.pdf#page=71>) · [IUT IV，命题 1.3(i)](<../refer/Mochizuki/Inter-universal Teichmuller Theory IV.pdf#page=11>)

在只有一个基域处的局部计算中，每个 capsule 的 $j+1$ 个槽都取 $k$，$j=1,2,3$。因 $7\leq p-2$，IV 定理 1.10 第 (v) 步采用的 $I^*$ 为空。向命题 1.4(iii) 代入 $d_I=(j+1)6/7$ 和 $\lambda=j^2(15/7)$，给出原文用于包络的上界

$$
\left(1+(j+1)\frac67-j^2\frac{15}7\right)\log p.
$$

三个系数依次为 $4/7$、$-35/7$、$-104/7$。取平均得到上界 $-45\log p/7$，严格小于同一归一化下 q-pilot 的 $-15\log p/7$。接受 IV 给实际 θ 包络的逐处包含后，这个例子排除了把当地 q-pilot 的体积用作 θ 包络的当地**下界**，也排除了在这个处用同一测度容纳一个具有 q-pilot 体积的格。这是局部 Tate 数据上的检验。将它作为整套初始 Θ 数据的一个指定坏处还需全局实现。III 推论 3.12 取各处之和，允许其他有限处及无穷处补偿这里的缺额。[IUT IV，命题 1.4(iii)](<../refer/Mochizuki/Inter-universal Teichmuller Theory IV.pdf#page=13>) · [定理 1.10 第 (iv)–(v) 步](<../refer/Mochizuki/Inter-universal Teichmuller Theory IV.pdf#page=27>) · [IUT III，命题 3.9(iii)](<../refer/Mochizuki/Inter-universal Teichmuller Theory III.pdf#page=117>)

## 三　第 129 页可以直接纠正的等式

III 注 3.9.5(i) 固定一个局部域直和及其整结构 $\mathcal O$。对于这里有界且含正测度子集的区域，全纯包络 $\phi(P)$ 是包含 $P$ 的最小 $\lambda\mathcal O$，其中 $\lambda$ 在该固定直和的每个域分量都非零。(iii) 定义 $\Xi(P)$ 为位于 $\phi(P)$ 内、对数体积与 $P$ 相等的这类包络，$H_{\Xi(P)}$ 为它们的并。用于 $H_{\Phi(P)}$ 的条件放宽为对数体积至少与 $P$ 相等，所以 $\phi(P)$ 自身就在 $\Phi(P)$ 里。[IUT III，注 3.9.5(i)–(iv)，第 127–129 页](<../refer/Mochizuki/Inter-universal Teichmuller Theory III.pdf#page=127>) · [两个族的定义](../refer/Mochizuki/Inter-universal_Teichmuller_Theory.md#L3147)

作者在 $I=\mathbb Q_p\times\mathbb Q_p$ 中取

$$
\begin{aligned}
H_0&=\mathbb Z_p\times\mathbb Z_p,&
H_1&=p^{-1}\mathbb Z_p\times p\mathbb Z_p,\\
P&=H_0\cup(\{p^{-1}\}\times\mathbb Z_p),&
H_P&=p^{-1}\mathbb Z_p\times\mathbb Z_p=\phi(P).
\end{aligned}
$$

$P=(\mathbb Z_p\cup\{p^{-1}\})\times\mathbb Z_p$ 是定义容许的直积区域。按原文归一化 Haar 测度 $\mu(H_0)=1$，新增的切片测度为零，所以 $\mu(P)=1$。固定两个域分量后，每个候选包络都是 $H(a,b)=p^a\mathbb Z_p\times p^b\mathbb Z_p$，$a,b\in\mathbb Z$，测度为 $p^{-a-b}$。在这个等权算例中，候选包络与 $P$ 有相同对数体积等价于有相同 Haar 测度。于是

$$
H(a,b)\in\Xi(P)
\quad\Longleftrightarrow\quad a\geq-1,\quad b\geq0,\quad a+b=0.
$$

整数解恰为 $(0,0)$、$(-1,1)$。因此 $H_{\Xi(P)}=H_0\cup H_1$。取 $z=(p^{-1},1)$，它甚至属于 $P$，却落在这两个包络之外。又因 $H_0\cap H_1=\mathbb Z_p\times p\mathbb Z_p$，正确的测度关系是

$$
1=\mu(P)<2-p^{-1}=\mu(H_{\Xi(P)})<p=\mu(H_P).
$$

原文也算对了 $2-p^{-1}$，但紧接着用 $H_P$ 的 $\mathbb Z_p$-模自同构声称 $H_{\Xi(P)}=H_P$。例如剪切 $(u,v)\mapsto(u,pu+v)$ 保持 $H_P$，并把 $H_1$ 送到含 $z$ 的斜格。这个斜格包含 $z$，却不包含其第一坐标投影 $(p^{-1},0)$，因而没有 $\lambda(\mathbb Z_p\times\mathbb Z_p)$ 的形式。加入斜格相当于扩大了 $\Xi(P)$ 的定义域。这给出了该实例末句的反例，同时保留作者在 (Ξ3) 要展示的严格不等式 $\mu(P)<\mu(H_{\Xi(P)})$ 及一般恒等式 $H_{\Phi(P)}=\phi(P)$。[IUT III，第 129 页原例](<../refer/Mochizuki/Inter-universal Teichmuller Theory III.pdf#page=129>) · [原文声称相等的句子](../refer/Mochizuki/Inter-universal_Teichmuller_Theory.md#L3214)

紧开区域也给出同一反例。取 $P'=\big((\mathbb Z_p\setminus(1+p\mathbb Z_p))\cup(p^{-1}+p\mathbb Z_p)\big)\times\mathbb Z_p$。它从第一分量去掉一个测度 $p^{-1}$ 的陪集，再加入一个同测度的陪集，所以 $\mu(P')=1$。新陪集仍含 $p^{-1}$，故 $\phi(P')=H_P$。$\Xi(P')$ 依旧只有 $H_0,H_1$。[IUT III，直积区域的定义，第 95 页](<../refer/Mochizuki/Inter-universal Teichmuller Theory III.pdf#page=95>)

同一组格也说明注 3.9.5(v)–(vi) 的集合商保留了什么。把 $\phi(P)=H_P$ 压成一点后，$H_0$ 和 $H_P$ 的像相同，Haar 测度分别是 $1$ 和 $p$。因此同一个商类可以有不同的实数对数体积。(Ob5) 另在体积值端取集合商。若要用它证明 (xi-f)，还须证明固定的 q 体积在实数端映到代表 $D_T$ 的商点，等价于证明该体积属于 $D_T$。[IUT III，注 3.9.5(v)–(vi)，第 129–130 页](<../refer/Mochizuki/Inter-universal Teichmuller Theory III.pdf#page=129>) · [体积值端的商](../refer/Mochizuki/Inter-universal_Teichmuller_Theory.md#L3316)

推论 3.12 取的是**全部可能像的并集的全纯包络**，对应例子里的 $H_P$。第 (xi-d) 步援引注 3.9.5(vii)–(ix) 的行列式和同构相容性。(Ob6) 提到用等体积包络做近似，也说明 $\Xi(P)$ 未必容易控制，因而采用容许体积增大的 $\Phi(P)$。(Ob5) 直接取全部可能区域的包络。改正第 129 页末句后，算例的完整包络仍为 $H_P$。这项反例排除了以 $H_{\Xi(P)}=\phi(P)$ 为依据的补证，主推论所需的固定 q-pilot 的归一化度与实际 Θ 包络的比较仍须单独证明。[推论 3.12 对包络的定义](<../refer/Mochizuki/Inter-universal Teichmuller Theory III.pdf#page=174>) · [注 3.9.5(vii) 的 (Ob5)、(Ob6)](../refer/Mochizuki/Inter-universal_Teichmuller_Theory.md#L3316)

与 Joshi 审查相交的是一个具体的数学问题。逐域分解里的全纯包络必须是各因子分式理想的直积。Joshi 用底层向量空间的凸闭包，第 129 页用底层模的自同构，这两种操作都可能产生斜格。Joshi 的另一项检验则在 Mochizuki 的归一化下有唯一结果。固定一个有限处的张量块 $A$，设 $d=\dim_{\mathbb Q_p}A$。标量 $p$ 在 $A$ 上的行列式是 $p^d$，故不论写成哪一个张量因子乘 $p$，同一格 $pM$ 相对 $M$ 的块内归一化对数体积位移都是 $-\log p$。III 的权重作用在整个处元组上，IV 改用块内归一化后相应调整外层权重。[Joshi 审查中的包络算例](<../对Arithmetic Teichmuller Spaces到Joshi 3.12的独立审计.md#L136>) · [IUT III，注 3.1.1(ii)，第 94–95 页](<../refer/Mochizuki/Inter-universal Teichmuller Theory III.pdf#page=94>) · [IUT IV，命题 1.4(i)](../refer/Mochizuki/Inter-universal_Teichmuller_Theory_4.md#L255) · [注 1.7.1 的权重换算](../refer/Mochizuki/Inter-universal_Teichmuller_Theory_4.md#L415)

## 四　`refer/iut` 已经形式化的下游

IUT IV 定理 1.10 将一个显式上界与 III 的 $C_\Theta\geq-1$ 合用。Lean 中，`theorem110` 把 `h312` 作为下界，再用传递性接上局部估计汇总得到的上界。它还接收局部估计、算术证书与素数估计。`c2` 对所构造的数据调用 `theorem110`。`statementII_of_cor312` 用 `c2` 得到三足曲线上紧有界子集的不等式，随后 `statementI_of_statementII` 将结论推广到固定次数上界的全部点。仓库记录了这条条件链中定理 1.10、推论 2.2 和陈述 II 的既有内核验收。[IUT IV，定理 1.10，第 23 页](<../refer/Mochizuki/Inter-universal Teichmuller Theory IV.pdf#page=23>) · [定理的输入](../refer/iut/Iut/Implication/Theorem110.lean#L227) · [下界与上界合用](../refer/iut/Iut/Implication/Theorem110.lean#L271) · [推论 2.2](../refer/iut/Iut/Implication/Corollary22.lean#L527) · [陈述 II](../refer/iut/Iut/Implication/Corollary23.lean#L53) · [推广及经典形式](../refer/iut/Iut/Tripod/ClassicalAbcOfVariant.lean#L26) · [既有验收记录](Scene1进度总览5.md#L222)

`Iut.Tripod.classicalABC_of_variant_genuine'` 是通往经典 abc 的具体入口。它实例化了 étale 基本群和以模型定义的 tempered 基本群，并证明所用的 `canLift27`。其唯一显式命题前提为 `h312`。略去已经固定的类型参数，定理为

```lean
(∀ D LT TL QI, Corollary312Variant (concreteVariantData D LT TL QI)) → ClassicalABC
```

这里 $D$ 是该模型的初始 Θ 数据，`LT` 是局部理论，`TL` 是相应 Θ 局部数据，`QI` 是 q-pilot 输入。结论 `ClassicalABC` 的量词是对每个 $\varepsilon>0$ 存在与三元组无关的常数 $C$，使所有正互素解 $a+b=c$ 满足 $c\leq C\,\operatorname{rad}(abc)^{1+\varepsilon}$。这覆盖完整的经典指数 $1+\varepsilon$。仓库 README 另注明，以模型定义的 tempered 群与 André tempered 群的比较目前有半稳定约化前提。[条件定理及全部量词](../refer/iut/Iut/Tripod/ClassicalAbcGenuineCanLift.lean#L40) · [经典 abc 的 Lean 定义](../refer/iut/Iut/Abc/Classical.lean#L38) · [tempered 群的比较条件](../refer/iut/README.md#L527)

论文从定理 3.11 的算法、Kummer 同构和不定性产生 Θ 区域，并在推论中论证体积有限。Lean 的抽象 `RHSData` 将区域及其包络的可接受性作为字段，`rhs` 是实数值 `processionVol`。具体版本把右侧区域定为 IV 的局部估计所用的容纳区域。要将原文证明送进 Lean，足够核对同一组数据上 $X.\mathrm{qPilot.lhs}=-|\log(q)|_{\mathrm{III}}$ 及 $-|\log(\Theta)|_{\mathrm{III}}\leq X.\mathrm{rhsData.rhs}$。后一比较可以由相同归一化下的包络包含给出。随后原文 3.12 就能通过传递性给出 `Corollary312Variant X`。现有代码计算了具体容器的体积界，论文构造的 Θ 区域到该容器的比较仍需对应证明。[变体定义和边界](../refer/iut/Iut/Cor312/Statement.lean#L39) · [右侧体积](../refer/iut/Iut/Cor312/RightHandSide.lean#L79) · [具体区域及其纸面对照](../refer/iut/Iut/Concrete/ThetaRegion.lean#L19)

形式化部分依据源码与已有的验收记录核对。本次没有重跑 Lean 编译或公理审查。

本文页码采用 PDF 自印页码。卷 I、III、IV 及 Étale Theta 论文取自 `refer/Mochizuki`。本地 `Inter-universal_Teichmuller_Theory.md` 对应卷 III。卷 III 本地 PDF 与作者网站的 2020 年 5 月版 SHA-256 一致，均为 `9a7ee3c77b1c7717210c0613eb39b6844649d0040dc3d9e1be7d544f8f91a0b9`。本地目录缺卷 II，相关交叉引用据作者网站 2020 年 12 月版核对。[作者的卷 III](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20III.pdf) · [作者的卷 II](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20II.pdf)
