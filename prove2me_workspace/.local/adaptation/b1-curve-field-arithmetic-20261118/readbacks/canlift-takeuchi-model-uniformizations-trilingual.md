# CanLift · Takeuchi model uniformizations

## 中文

### Belyi 拉回

设 `RatCert f N D H K R c` 是曲线 $W$ 的证书。`exists_takeuchi` 接收 `JOrbStatement` 和这份证书。它要求 $W/\mathbb C$ 为椭圆曲线，$a_1=a_3=0$，且对每个 $x\in\mathbb C$ 有 $f(x)=x^3+a_2x^2+a_4x+a_6$。把 $W$ 写成周期格模型 $E_\tau$ 的变量变换 $C\cdot E_\tau$，记其周期格为 $\Lambda$。令 $a=u_C^{-2}$、$r=-ar_C$，其中 $u_C$ 和 $r_C$ 是变量变换 $C$ 的缩放和平移系数。`mem_twoTorsionX_iff` 通过直线 $y=0$ 把非零二阶挠点的 $x$ 坐标集合识别为 $f$ 的根集。

令 $G=N/D$、$\ell_X(z)=a\wp_\Lambda(z/2)+r$、$F=G\circ\ell_X$。$\ell_X$ 在 $\mathbb C\setminus\Lambda$ 上局部可逆，并取遍二阶挠点 $x$ 坐标以外的值。`ellOrbStatement` 用 $G$ 的有限纤维以及在极点和无穷远处的发散控制小圆盘的原像，再沿符号和 $2\Lambda$ 平移搬运局部图。`RatCert.ellipticOrbifoldCover` 给出 $F$ 在 $\mathbb C\setminus\Lambda$ 上的轨形覆盖、阶数 $\operatorname{sig}(F(z))$ 的局部正规形，以及对所有 $z\in\mathbb C$ 和 $\lambda\in\Lambda$ 的等式 $F(z+2\lambda)=F(z)$。

### 模 $j$ 与轨形提升

`jOrbStatement` 给出模 $j$ 在上半平面 $\mathbb H$ 上的轨形覆盖。稳定子在以不动点为中心的 Cayley 坐标中作用为旋转，确定 $j=0$、$j=1728$ 和其余纤维的局部阶数分别为 $3$、$2$、$1$。旋转不变性表明局部阶数是稳定子旋转阶数的倍数，局部纤维的大小再给出反向整除。用模群元素移动局部图可覆盖整个小圆盘的原像。移动后的两个图若相交，则其定义域重合。

设 $p$ 是定义在 $Y\subseteq\mathbb C$ 上、阶数函数 $e$ 处处为正的轨形覆盖。若全纯函数 $f$ 在上半平面的每一点 $z$ 都具有阶数 $e(f(z))$ 的局部正规形，`orbLiftStatement` 给出全纯提升 $h\colon\mathbb H\to Y$，使得 $p(h(z))=f(z)$。若源函数的局部正规形为 $w+g^n$，覆盖图的逆坐标为 $v_i$，局部提升为 $v_i(\zeta g)$，其中 $\zeta^n=1$。用 $(z,h(z),h'(z))$ 表示提升的芽。同一图中不同根的导数分开各支，不同图由值所在的不交开集区分。这些芽构成 $\mathbb H$ 上的普通覆盖。利用 $\mathbb H$ 的凸性提升恒等映射，取其值坐标，得到全纯提升。

### 整数平方迹

`int_sq_traces` 接收 `OrbLiftStatement`、`JOrbStatement`，以及 $F$ 的轨形覆盖、局部正规形和 $2\Lambda$ 周期性。

设 $\psi:\mathbb H\to\mathbb C\setminus\Lambda$ 为格补集的覆盖。`exists_mobius_lift_of_orbifold` 将 $\Psi=F\circ\psi$ 提升过 $j$，得到 $h$。反向先将 $j$ 提升过 $F$，再提升过 $\psi$，得到 $k$。于是 $j\circ h\circ k=j$。由模 $j$ 的纤维、Baire 定理和解析恒等定理，$h\circ k$ 由单个 $\delta\in\mathrm{SL}_2(\mathbb Z)$ 作用给出。以 $\delta^{-1}$ 修正 $h$ 得到 $k$ 的全纯左逆，因此 $k$ 和 $h=m\cdot(-)$ 都是 Möbius 变换，其中 $m\in\mathrm{SL}_2(\mathbb R)$。

对边配对矩阵 $A,B$ 生成的子群中的每个 $\gamma$，存在 $\lambda\in\Lambda$，使得对所有 $z\in\mathbb H$ 都有 $\psi(\gamma z)=\psi(z)+\lambda$。$2\Lambda$ 周期性给出 $\Psi(\gamma^2z)=\Psi(z)$。因此 $m\gamma^2m^{-1}$ 保持 $j$，它与某个整数模矩阵至多相差一个符号，故其迹是整数。迹的共轭不变性与 $\operatorname{tr}(\gamma)^2=\operatorname{tr}(\gamma^2)+2$ 给出 `int_sq_traces` 的结论。

### 四个模型的一致化

`exists_takeuchi` 使用同一个格补集覆盖构造 $W\setminus\{O\}$ 的一致化。把格补集覆盖与变换后的 Weierstrass 参数映射复合。`Uniformizes W (A, B)` 包含一条全纯浸入，其像是全部仿射点，且纤维恰是 $\langle A,B\rangle$ 的轨道。由 $\operatorname{tr}[A,B]=-2$、$\operatorname{tr} A\ne0$ 和整数平方迹得到 Nielsen 约化，继而得到 `IsTakeuchiConj A B`。该命题保存生成同一子群的生成元、各生成元的符号选择，以及到某个显式 `takeuchiPair i` 的共同 $\mathrm{GL}_2(\mathbb R)$ 共轭。

`exists_uniformizes_ccurve` 对每个 $k:\mathrm{Fin}\,4$ 使用 `exists_modelRatCert k` 和已证明的 `jOrbStatement`。`exists_takeuchiPair_ccurve` 得出存在某个 $i$，使 `ccurve k` 或它的复共轭由 `takeuchiPair i` 一致化。共轭矩阵的行列式为正时取原曲线，为负时取复共轭曲线。四个模型定义在 $\mathbb Q$ 上，复共轭固定这些模型。同一生成元对的一致化刚性与四个不同的 $j$ 值使模型与生成元对的指标形成双射。

### 复数域 CanLift 的输入

`canLift27Complex_of_fricke_integrality` 把四个模型的一致化直接传给 `canLift27Complex_of_fricke_normal_form`。它的显式参数 `NormalFormTraceIntegrality` 要求 $x,y,z>0$、$x^2+y^2+z^2=xyz$ 和三个严格三角不等式。设 $\Gamma_0=\langle\mathrm{nA},\mathrm{nB}\rangle$ 是相应的 Fricke 正规形群。若 $\Gamma_0$ 的可公度子在 $\mathrm{SL}_2(\mathbb R)$ 中稠密，该参数要求 $\Gamma_0$ 中每个元素的平方迹都是整数。装配证明将这一整数性传回待研究曲线的格群。结合模型的一致化与刚性，它排除非例外 $j$ 情形下的无限指数。`CanLift27Complex` 的量化对象是任意复椭圆曲线 $E$，其 $j(E)$ 避开 $0$、$1728$、$488095744/125$ 和 $1556068/81$。令 $X$ 和 $Q$ 分别为 $E\setminus\{O\}$ 及其符号商的正规化呈示，两者都取级别 $1$ 和零子群。结论是 `IsCoreOf X Q`。$X$ 与 $Q$ 有共同覆盖，且每个与 $X$ 有共同覆盖的仿射轨形曲线呈示都有唯一的到 $Q$ 的覆盖。

## English

### Belyi pullback

The theorem `exists_takeuchi` takes `JOrbStatement` and a certificate `RatCert f N D H K R c` for an elliptic curve $W/\mathbb C$. It requires $a_1=a_3=0$ and $f(x)=x^3+a_2x^2+a_4x+a_6$ for every $x\in\mathbb C$. Write $W=C\cdot E_\tau$ for a change of variables of a lattice curve with period lattice $\Lambda$. Set $a=u_C^{-2}$ and $r=-ar_C$, where $u_C$ and $r_C$ are the scale and translation of $C$. The theorem `mem_twoTorsionX_iff` identifies the nonzero two-torsion $x$-coordinates as the solutions of the curve equation at $y=0$. These solutions are the roots of $f$.

Set $G=N/D$, $\ell_X(z)=a\wp_\Lambda(z/2)+r$, and $F=G\circ\ell_X$. Off $\Lambda$, $\ell_X$ is locally invertible and attains every value outside the two-torsion $x$-coordinates. The theorem `ellOrbStatement` uses finite fibers of $G$ and its pole limits at the roots and at infinity. These control the preimage of a small disk. The proof transports local charts by signs and translations in $2\Lambda$. The theorem `RatCert.ellipticOrbifoldCover` gives the orbifold cover for $F$ off $\Lambda$ and the local forms of order $\operatorname{sig}(F(z))$. It also gives $F(z+2\lambda)=F(z)$ for all $z\in\mathbb C$ and $\lambda\in\Lambda$.

### Modular $j$ and orbifold lifting

The theorem `jOrbStatement` gives an orbifold cover for modular $j$ on the upper half-plane $\mathbb H$. In Cayley coordinates centered at the fixed point, the stabilizer acts by rotations. Rotation invariance and the size of the local fibers determine the exact order. It is $3$ over $0$, $2$ over $1728$, and $1$ elsewhere. Modular translates of a local chart cover the preimage of the target disk. Two translates with intersecting domains have the same domain.

Let $p$ be an orbifold cover on $Y\subseteq\mathbb C$ with positive order function $e$. Let $f$ be holomorphic on $\mathbb H$ with local form of order $e(f(z))$ at each $z\in\mathbb H$. Then `orbLiftStatement` gives a holomorphic $h\colon\mathbb H\to Y$ with $p(h(z))=f(z)$. Suppose the local form is $w+g^n$ and $v_i$ is an inverse chart coordinate. The local lifts are $v_i(\zeta g)$ with $\zeta^n=1$. A jet $(z,h(z),h'(z))$ records the germ of a local lift $h$. Distinct roots give distinct derivatives at the center of a chart, and disjoint chart domains distinguish the values. The germs form an ordinary cover of $\mathbb H$. Convexity gives a lift of the identity through this cover. The value coordinate of this lift gives the holomorphic lift.

### Integral squared traces

`int_sq_traces` takes `OrbLiftStatement`, `JOrbStatement`, and the orbifold cover, local forms, and $2\Lambda$-periodicity of $F$.

Let $\psi:\mathbb H\to\mathbb C\setminus\Lambda$ be the lattice complement cover. The theorem `exists_mobius_lift_of_orbifold` lifts $\Psi=F\circ\psi$ through $j$ to $h$. It lifts $j$ through $F$ and then through $\psi$ to obtain $k$. Thus $j\circ h\circ k=j$. The modular fibers, Baire's theorem, and the identity theorem give a single $\delta\in\mathrm{SL}_2(\mathbb Z)$ that acts as $h\circ k$. Composing $h$ with $\delta^{-1}$ gives a holomorphic left inverse for $k$. It follows that $k$ and $h=m\cdot(-)$ are Möbius maps, with $m\in\mathrm{SL}_2(\mathbb R)$.

Let $\gamma$ belong to the subgroup generated by the edge pairings $A,B$. There is a $\lambda\in\Lambda$ with $\psi(\gamma z)=\psi(z)+\lambda$ for every $z\in\mathbb H$. The $2\Lambda$-periodicity gives $\Psi(\gamma^2z)=\Psi(z)$. Thus $m\gamma^2m^{-1}$ preserves $j$. It equals an integral modular matrix up to sign and has integral trace. Trace is invariant under conjugation, and $\operatorname{tr}(\gamma)^2=\operatorname{tr}(\gamma^2)+2$. This gives the integral squared trace in `int_sq_traces`.

### Uniformizations of the four models

The theorem `exists_takeuchi` uses the same lattice complement cover to uniformize $W\setminus\{O\}$. It composes the cover with the Weierstrass parameterization in the new coordinates. In `Uniformizes W (A, B)`, the map is a holomorphic immersion onto the affine points of $W$. Its fibers are the $\langle A,B\rangle$-orbits. Nielsen descent uses $\operatorname{tr}[A,B]=-2$, $\operatorname{tr} A\ne0$, and integral squared traces. `IsTakeuchiConj A B` retains new generators of the same subgroup. It includes independent signs and simultaneous $\mathrm{GL}_2(\mathbb R)$-conjugacy to a `takeuchiPair i`.

For each $k:\mathrm{Fin}\,4$, `exists_uniformizes_ccurve` uses `exists_modelRatCert k` and the proved `jOrbStatement`. The theorem `exists_takeuchiPair_ccurve` gives some $i$ for which `takeuchiPair i` uniformizes `ccurve k` or its complex conjugate. A positive conjugating determinant gives the original curve. A negative determinant gives the complex-conjugate curve. Complex conjugation fixes the four models because they are defined over $\mathbb Q$. Same-pair rigidity and the four distinct $j$-values give a bijection between the model indices and the pair indices.

### Input to complex CanLift

The theorem `canLift27Complex_of_fricke_integrality` supplies the four model uniformizations to `canLift27Complex_of_fricke_normal_form`. Its explicit input, `NormalFormTraceIntegrality`, uses $x,y,z>0$, $x^2+y^2+z^2=xyz$, and the three strict triangle inequalities. Let $\Gamma_0=\langle\mathrm{nA},\mathrm{nB}\rangle$ be the corresponding Fricke normal-form subgroup. If the commensurator of $\Gamma_0$ is dense in $\mathrm{SL}_2(\mathbb R)$, the input requires integral squared traces for every element of $\Gamma_0$. The assembly transports this integrality to the lattice group of the given curve. The model uniformizations and rigidity then exclude infinite index for non-exceptional $j$. The conclusion `CanLift27Complex` applies to each complex elliptic curve $E$ with $j(E)$ outside $\{0,1728,488095744/125,1556068/81\}$. Let $X$ and $Q$ be the normalized presentations of $E\setminus\{O\}$ and its sign quotient. Both use level $1$ and the trivial subgroup. The conclusion `IsCoreOf X Q` gives a common cover of $X$ and $Q$. Any affine orbicurve presentation with a common cover with $X$ has exactly one cover to $Q$.

## 日本語

### Belyi 写像の引き戻し

`RatCert f N D H K R c` を曲線 $W$ の証明書とする。`exists_takeuchi` は `JOrbStatement` とこの証明書を受け取る。$W/\mathbb C$ は楕円曲線であり、$a_1=a_3=0$ かつすべての $x\in\mathbb C$ に対して $f(x)=x^3+a_2x^2+a_4x+a_6$ と仮定する。$W=C\cdot E_\tau$ と書き、格子曲線 $E_\tau$ の周期格子を $\Lambda$ とする。$C$ の拡大率 $u_C$ と平行移動係数 $r_C$ を用いて $a=u_C^{-2}$、$r=-ar_C$ とおく。`mem_twoTorsionX_iff` は直線 $y=0$ を用い、非零の 2 等分点の $x$ 座標を $f$ の根と同定する。

$G=N/D$、$\ell_X(z)=a\wp_\Lambda(z/2)+r$、$F=G\circ\ell_X$ とおく。$\ell_X$ は $\mathbb C\setminus\Lambda$ 上で局所的に可逆であり、2 等分点の $x$ 座標を除くすべての値をとる。`ellOrbStatement` は $G$ のファイバーの有限性と極および無限遠での発散を用いて、小円板の逆像を制御する。局所座標を符号変換と $2\Lambda$ の平行移動で移す。`RatCert.ellipticOrbifoldCover` は $\mathbb C\setminus\Lambda$ 上の $F$ のオービフォールド被覆、位数 $\operatorname{sig}(F(z))$ の局所標準形、およびすべての $z\in\mathbb C$ と $\lambda\in\Lambda$ に対する $F(z+2\lambda)=F(z)$ を与える。

### モジュラー $j$ とオービフォールドの持ち上げ

`jOrbStatement` は、上半平面 $\mathbb H$ 上のモジュラー $j$ がオービフォールド被覆を与えることを示す。固定点を中心とする Cayley 座標で固定部分群は回転として作用する。回転不変性と局所ファイバーの大きさから正確な位数が決まる。位数は $0$ の上で $3$、$1728$ の上で $2$、それ以外で $1$ である。局所座標をモジュラー群で移すと、値の小円板の逆像全体を覆う。二つの移動後の座標近傍が交わる場合、その近傍は一致する。

$p$ を $Y\subseteq\mathbb C$ 上のオービフォールド被覆とし、その位数関数 $e$ はいたるところ正とする。$\mathbb H$ 上の正則関数 $f$ が各点 $z$ で位数 $e(f(z))$ の局所標準形をもつとき、`orbLiftStatement` は $p(h(z))=f(z)$ を満たす正則な持ち上げ $h\colon\mathbb H\to Y$ を与える。局所標準形を $w+g^n$、被覆の座標の逆写像を $v_i$ とすると、局所持ち上げは $\zeta^n=1$ を満たす $v_i(\zeta g)$ である。局所持ち上げ $h$ の芽を $(z,h(z),h'(z))$ で表す。同じ座標近傍では異なる根が中心で異なる導関数を与え、互いに素な座標近傍では値が異なる。これらの芽は $\mathbb H$ の通常の被覆をなす。$\mathbb H$ の凸性を使って恒等写像を持ち上げ、その値の座標を取ると正則な持ち上げが得られる。

### 跡の二乗の整数性

`int_sq_traces` は `OrbLiftStatement`、`JOrbStatement`、および $F$ のオービフォールド被覆、局所標準形、$2\Lambda$ 周期性を入力とする。

$\psi:\mathbb H\to\mathbb C\setminus\Lambda$ を格子補集合の被覆とする。`exists_mobius_lift_of_orbifold` は $\Psi=F\circ\psi$ を $j$ に沿って持ち上げ、$h$ を得る。$j$ を $F$、次に $\psi$ に沿って持ち上げると $k$ が得られる。したがって $j\circ h\circ k=j$ である。モジュラー $j$ のファイバー、Baire の定理、正則関数の一致の定理から、$h\circ k$ は一つの $\delta\in\mathrm{SL}_2(\mathbb Z)$ の作用である。$\delta^{-1}$ を $h$ の後に合成すると $k$ の正則な左逆写像が得られる。よって $k$ と $h=m\cdot(-)$ は Möbius 変換であり、$m\in\mathrm{SL}_2(\mathbb R)$ である。

辺の貼り合わせ行列 $A,B$ が生成する部分群の各元 $\gamma$ について、ある $\lambda\in\Lambda$ が存在し、すべての $z\in\mathbb H$ に対して $\psi(\gamma z)=\psi(z)+\lambda$ が成り立つ。$2\Lambda$ 周期性から $\Psi(\gamma^2z)=\Psi(z)$ が従う。したがって $m\gamma^2m^{-1}$ は $j$ を保ち、符号を除いて整数係数のモジュラー行列に等しい。その跡は整数である。跡の共役不変性と $\operatorname{tr}(\gamma)^2=\operatorname{tr}(\gamma^2)+2$ により、`int_sq_traces` の結論を得る。

### 四つのモデルの一意化

`exists_takeuchi` は同じ格子補集合の被覆を使って $W\setminus\{O\}$ を一意化する。被覆に座標変換後の Weierstrass パラメータ表示を合成する。`Uniformizes W (A, B)` は、すべてのアフィン点への正則はめ込みで、ファイバーが $\langle A,B\rangle$ の軌道と一致するものの存在を表す。$\operatorname{tr}[A,B]=-2$、$\operatorname{tr} A\ne0$、跡の二乗の整数性を用いて Nielsen 降下を適用する。`IsTakeuchiConj A B` は、同じ部分群を生成する新しい生成元、それぞれの符号、ある `takeuchiPair i` への $\mathrm{GL}_2(\mathbb R)$ による同時共役を与える。

各 $k:\mathrm{Fin}\,4$ に対し、`exists_uniformizes_ccurve` は `exists_modelRatCert k` と証明済みの `jOrbStatement` を用いる。`exists_takeuchiPair_ccurve` は、`ccurve k` またはその複素共役を一意化する `takeuchiPair i` の存在を与える。共役を与える行列の行列式が正なら元の曲線、負なら複素共役曲線を得る。四つのモデルは $\mathbb Q$ 上で定義され、複素共役で変わらない。同じ生成元対に関する一意化の剛性と相異なる四つの $j$ 値により、モデルの添字と生成元対の添字の間に全単射が得られる。

### 複素数体上の CanLift の入力

`canLift27Complex_of_fricke_integrality` は四つのモデルの一意化を `canLift27Complex_of_fricke_normal_form` に渡す。明示的な入力 `NormalFormTraceIntegrality` では $x,y,z>0$、$x^2+y^2+z^2=xyz$、および三つの狭義三角不等式を用いる。対応する Fricke 標準形の群を $\Gamma_0=\langle\mathrm{nA},\mathrm{nB}\rangle$ とする。$\Gamma_0$ の commensurator が $\mathrm{SL}_2(\mathbb R)$ で稠密なら、$\Gamma_0$ の各元の跡の二乗が整数であることを要求する。組立ての証明はこの整数性を対象の曲線の格子群に移す。モデルの一意化と剛性を合わせると、$j$ が例外値でない場合の無限指数を排除できる。結論 `CanLift27Complex` は、$j(E)$ が $0$、$1728$、$488095744/125$、$1556068/81$ のいずれとも異なる各複素楕円曲線 $E$ に適用される。$X$ と $Q$ をそれぞれ $E\setminus\{O\}$ とその符号作用による商の正規化表示とする。どちらもレベル $1$ と自明な部分群を用いる。`IsCoreOf X Q` により $X$ と $Q$ は共通被覆をもち、$X$ と共通被覆をもつ任意のアフィン軌道曲線の表示から $Q$ への被覆がただ一つ存在する。

## Sources

| Step | Pinned source | Local declaration |
| --- | --- | --- |
| Lattice coordinate and pole set | [ellX and twoTorsionX](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Defs.lean#L82) · [mem_twoTorsionX_iff](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Belyi.lean#L25) | [ellX](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiEllipticX.lean#L26) · [mem_twoTorsionX_iff](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiBelyiPullback.lean#L26) |
| Orbifold cover and periodicity | [ellOrbStatement](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/EllOrb.lean#L245) · [pullback and periodicity](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Belyi.lean#L88) | [ellOrbStatement](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiEllipticOrbifoldCover.lean#L95) · [RatCert.ellipticOrbifoldCover](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiBelyiPullback.lean#L78) |
| Modular orbifold charts | [local rotation order](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/JOrb.lean#L87) · [chart translates](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/JOrb.lean#L845) · [jOrbStatement](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/JOrb.lean#L940) | [exists_localForm_of_rot](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRotationLocalForm.lean#L61) · [JChartData.cover](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiJOrb.lean#L89) · [jOrbStatement](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiJOrb.lean#L184) |
| Local lift branches and the covering of germs | [local_data](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/OrbLift.lean#L104) · [germs_isCoveringMapOn](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/OrbLift.lean#L268) · [orbLiftStatement](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/OrbLift.lean#L284) | [orbifoldLocalLiftData](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiOrbifoldLocalLift.lean#L96) · [germs_isCoveringMapOn](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiOrbifoldLift.lean#L114) · [orbLiftStatement](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiOrbifoldLift.lean#L130) |
| Two lifts give a Möbius map | [two orbifold lifts](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Arith.lean#L87) · [exists_SL2R_eq_of_leftInverse](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Mobius.lean#L25) · [exists_SL2Z_eq_of_modularJ](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Mobius.lean#L148) | [exists_mobius_lift_of_orbifold](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiModularLift.lean#L27) · [exists_SL2R_eq_of_leftInverse](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiModularMobius.lean#L62) · [exists_SL2Z_eq_of_modularJ](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiModularMobius.lean#L103) |
| Integral squared traces on the edge-pairing subgroup | [exists_int_tr_of_modularJ](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Arith.lean#L45) · [int_sq_traces](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Arith.lean#L70) | [exists_int_tr_of_modularJ](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiIntegralTraces.lean#L32) · [int_sq_traces](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiIntegralTraces.lean#L51) |
| Uniformization and Takeuchi conjugacy for a certified curve | [uniformizes_unif](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/LatticeUnif.lean#L183) · [IsTakeuchiConj](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/Classification.lean#L31) · [exists_takeuchi](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Belyi.lean#L72) | [LatticeComplementCover.uniformizes](../../../../Solutions/Source_ReferenceIutCanLiftLatticeUniformization.lean#L26) · [IsTakeuchiConj](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiBelyi.lean#L30) · [exists_takeuchi](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiBelyi.lean#L38) |
| Uniformizations of all four complex models | [exists_uniformizes_ccurve](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Main.lean#L83) · [Uniformizes.exists_takeuchiPair](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Transport.lean#L251) | [exists_modelRatCert](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiCertificates.lean#L362) · [exists_uniformizes_ccurve](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiModelUniformizations.lean#L21) · [exists_takeuchiPair_ccurve](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiModelUniformizations.lean#L27) |
| Matching model indices by rigidity | [exceptional_of_takeuchi](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Main.lean#L101) · [rigidityStatement](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Rigidity.lean#L73) | [exceptionalJ_of_model_uniformizations](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiModelRigidity.lean#L28) · [j_eq_of_uniformizes](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRigidity.lean#L147) |
| Arithmetic input and complex conclusion | [trace_sq_int_of_dense](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L548) · [fixes_xP](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/U2/TheoremG.lean#L189) | [NormalFormTraceIntegrality](../../../../Solutions/Source_ReferenceIutCanLiftFrickeTraceTransport.lean#L28) · [canLift27Complex_of_fricke_normal_form](../../../../Solutions/Source_ReferenceIutCanLiftFrickeTraceTransport.lean#L167) · [canLift27Complex_of_fricke_integrality](../../../../Solutions/Source_ReferenceIutCanLiftComplexFromFricke.lean#L15) · [CanLift27Complex](../../../../Solutions/Source_ReferenceIutCanLiftPresentation.lean#L113) · [IsCoreOf](../../../../Solutions/Source_ReferenceIutCanLiftPresentation.lean#L26) |
