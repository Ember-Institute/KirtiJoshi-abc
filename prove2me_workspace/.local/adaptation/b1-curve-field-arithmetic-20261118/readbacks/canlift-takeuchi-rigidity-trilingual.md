# CanLift · 周期格子与 $j$ 不变量刚性

$$
\mathbb H=\{z\in\mathbb C\mid\operatorname{Im}z>0\},\qquad
\Lambda_\tau=\mathbb Z\tau+\mathbb Z,\qquad
q_\tau\colon\mathbb C\longrightarrow\mathbb C/\Lambda_\tau,\quad x\longmapsto[x]_\tau .
$$

## 中文

### 从一致化取得格提升

设 $W$ 是判别式非零的复 Weierstrass 曲线，$A,B\in\mathrm{SL}_2(\mathbb R)$，$\Gamma=\langle A,B\rangle$ 是由这两个矩阵生成的子群。`IsUniformization W A B π` 要求 $\pi\colon\mathbb C\to\mathbb C^2$ 在上半平面每一点处复可微且导数非零，$\pi(\mathbb H)$ 恰为 $W$ 的仿射点集，并且 $\pi(z)=\pi(w)$ 当且仅当存在 $\gamma\in\Gamma$ 使得 $\gamma\cdot z=w$，其中 $z,w\in\mathbb H$。

`exists_isLatticeLift` 由此给出 $\tau\in\mathbb H$ 和 $\sigma\colon\mathbb C\to\mathbb C$，使得 $j(W)=\operatorname{modularJ}(\tau)$。对每个 $z\in\mathbb H$，$\sigma(z)\notin\Lambda_\tau$，且 $\sigma$ 在 $z$ 处复可微、导数非零。对每个 $x\notin\Lambda_\tau$，存在 $z\in\mathbb H$ 使 $\sigma(z)-x\in\Lambda_\tau$。对所有 $z,w\in\mathbb H$，

$$
\sigma(z)-\sigma(w)\in\Lambda_\tau
\quad\Longleftrightarrow\quad
\exists\,\gamma\in\Gamma,\ \gamma\cdot z=w .
$$

证明先取把格子曲线化为 $W$ 的 Weierstrass 变量变换 $C$。用 $\Psi\colon\mathbb H\to\mathbb C\setminus\Lambda_\tau$ 表示格子补集覆盖，用 $P_{\tau,C}$ 表示变换后的 Weierstrass 参数化。两份一致化的唯一性给出 $g\in\mathrm{SL}_2(\mathbb R)$，使得 $\pi(z)=P_{\tau,C}(\Psi(g\cdot z))$。取 $\sigma(z)=\Psi(g\cdot z)$。Möbius 变换的导数非零，而 $P_{\tau,C}$ 在格子补集上的纤维恰好由周期同余刻画。 [一致化](../../../../Solutions/Source_ReferenceIutCanLiftUniformizationCover.lean#L69) · [格提升](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRigidityLift.lean#L55)

### 从共同纤维到整函数

设 $\sigma,\sigma'$ 分别满足周期格子 $\Lambda_\tau,\Lambda_{\tau'}$ 的 `IsLatticeLift` 条件。`SameFibres` 要求对所有 $z,w\in\mathbb H$，$\sigma(z)-\sigma(w)\in\Lambda_\tau$ 等价于 $\sigma'(z)-\sigma'(w)\in\Lambda_{\tau'}$。每个非零类都可写成 $q_\tau(\sigma(z))$，而 `SameFibres` 保证其像 $q_{\tau'}(\sigma'(z))$ 与 $z$ 的选择无关。令零类映到零类，`transfer` 就给出格商之间的双射 $T$。交换两份提升得到逆映射。

给定非零类的代表点 $x_0$，取 $\sigma(z_0)=x_0+\ell$，其中 $\ell\in\Lambda_\tau$。先把 $x_0$ 附近的点平移 $\ell$，再应用 $\sigma$ 的局部全纯逆支，得到截面 $s$。局部公式 $T(q_\tau(y))=q_{\tau'}(\sigma'(s(y)))$ 给出非零类处的连续性。两个格商是紧致 Hausdorff 空间，逆映射在非零类处连续，这给出 $T$ 在零类处的连续性。

由于 $\mathbb C$ 是凸集，$T\circ q_\tau$ 可沿覆盖映射 $q_{\tau'}$ 提升为满足 $\beta(0)=0$ 的连续函数 $\beta$。在 $\Lambda_\tau$ 外，$\beta$ 局部等于 $\sigma'\circ s$ 加一个常周期。格点孤立，连续性使这些点成为可去奇点。`exists_entire_lift` 得到整函数 $\beta\colon\mathbb C\to\mathbb C$，满足 $\beta(0)=0$，且对每个 $x\in\mathbb C$，

$$
q_{\tau'}(\beta(x))=T(q_\tau(x)).
$$

[同纤维与传递映射](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRigidityTransfer.lean#L109) · [整函数提升](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRigidityTransfer.lean#L200)

### 从格子缩放到 $j$ 相等

对每个 $\ell\in\Lambda_\tau$，连续函数 $x\mapsto\beta(x+\ell)-\beta(x)$ 从连通的复平面取值于离散格子 $\Lambda_{\tau'}$，所以它是常函数。于是 $\beta'$ 以 $\Lambda_\tau$ 为周期，由闭基本平行四边形的紧性可知它有界。Liouville 定理给出常导数，再用 $\beta(0)=0$ 得到 $\beta(x)=ax$。逆映射也有形如 $x\mapsto bx$ 的提升。两者复合在格商上是恒等映射，故 $(ba-1)x\in\Lambda_\tau$ 对所有 $x\in\mathbb C$ 成立。该连续函数在 $0$ 处为零，由格子的离散性可知 $ba=1$。

`exists_homothety` 得到 $a\in\mathbb C\setminus\{0\}$，使得对所有 $x\in\mathbb C$，$x\in\Lambda_\tau$ 当且仅当 $ax\in\Lambda_{\tau'}$。即 $\Lambda_{\tau'}=a\Lambda_\tau$。在此缩放下，Weierstrass 不变量 $g_2,g_3$ 分别乘以 $a^{-4},a^{-6}$。`modularJ_eq_of_homothety` 用这两条公式得到 $\operatorname{modularJ}(\tau)=\operatorname{modularJ}(\tau')$，因为 $j=(12g_2)^3/(g_2^3-27g_3^2)$ 的分子与分母都乘以 $a^{-12}$。

若同一矩阵对 $(A,B)$ 分别一致化两条判别式非零的复 Weierstrass 曲线 $W,W'$，两份格提升便由相同的 $\Gamma$ 轨道给出 `SameFibres`。`j_eq_of_uniformizes` 因此得到 $j(W)=j(W')$。 [格子缩放](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRigidity.lean#L80) · [模 $j$ 不变性](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRigidity.lean#L125) · [同矩阵对的刚性](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRigidity.lean#L147)

## English

### From uniformization to a lattice lift

Let $W$ be a complex Weierstrass curve with nonzero discriminant. Let $A,B\in\mathrm{SL}_2(\mathbb R)$, and let $\Gamma=\langle A,B\rangle$ be the subgroup they generate. In `IsUniformization W A B π`, the map $\pi\colon\mathbb C\to\mathbb C^2$ is complex differentiable with nonzero derivative at every point of $\mathbb H$. It maps $\mathbb H$ onto the affine points of $W$. For all $z,w\in\mathbb H$, $\pi(z)=\pi(w)$ if and only if some $\gamma\in\Gamma$ sends $z$ to $w$.

`exists_isLatticeLift` gives $\tau\in\mathbb H$ and $\sigma\colon\mathbb C\to\mathbb C$ with $j(W)=\operatorname{modularJ}(\tau)$. On $\mathbb H$, the map $\sigma$ avoids $\Lambda_\tau$ and is complex differentiable with nonzero derivative. For every $x\notin\Lambda_\tau$, there is a $z\in\mathbb H$ with $\sigma(z)-x\in\Lambda_\tau$. For all $z,w\in\mathbb H$,

$$
\sigma(z)-\sigma(w)\in\Lambda_\tau
\quad\Longleftrightarrow\quad
\exists\,\gamma\in\Gamma,\ \gamma\cdot z=w .
$$

Choose a Weierstrass change of variables $C$ from the lattice curve to $W$. Write $\Psi\colon\mathbb H\to\mathbb C\setminus\Lambda_\tau$ for the lattice complement covering and $P_{\tau,C}$ for the Weierstrass parameterization after the change of variables. Uniqueness of uniformization gives $g\in\mathrm{SL}_2(\mathbb R)$ with $\pi(z)=P_{\tau,C}(\Psi(g\cdot z))$. Put $\sigma(z)=\Psi(g\cdot z)$. The Möbius transformation has nonzero derivative. On the lattice complement, two values of $P_{\tau,C}$ agree exactly when their arguments differ by a period. [Uniformization](../../../../Solutions/Source_ReferenceIutCanLiftUniformizationCover.lean#L69) · [Lattice lift](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRigidityLift.lean#L55)

### From common fibers to an entire function

Suppose $\sigma,\sigma'$ satisfy `IsLatticeLift` for $\Lambda_\tau,\Lambda_{\tau'}$, respectively. For every $z,w\in\mathbb H$, `SameFibres` requires $\sigma(z)-\sigma(w)\in\Lambda_\tau$ if and only if $\sigma'(z)-\sigma'(w)\in\Lambda_{\tau'}$. Write each nonzero class as $q_\tau(\sigma(z))$. By `SameFibres`, its image $q_{\tau'}(\sigma'(z))$ is independent of the choice of $z$. With the zero class sent to zero, `transfer` gives a bijection $T$ between the quotients. Swapping the two lifts gives its inverse.

For a representative $x_0$ of a nonzero class, choose $\sigma(z_0)=x_0+\ell$ with $\ell\in\Lambda_\tau$. Translate points near $x_0$ by $\ell$, then apply a local holomorphic inverse branch of $\sigma$ to obtain a section $s$. The local formula $T(q_\tau(y))=q_{\tau'}(\sigma'(s(y)))$ gives continuity at the nonzero classes. The quotients are compact Hausdorff spaces. Continuity of the inverse away from zero gives continuity of $T$ at zero.

Convexity of $\mathbb C$ permits a continuous lift $\beta$ of $T\circ q_\tau$ through the covering $q_{\tau'}$, with $\beta(0)=0$. Away from $\Lambda_\tau$, the lift locally equals $\sigma'\circ s$ plus a constant period. The lattice points are isolated, and continuity makes the singularities removable. Thus `exists_entire_lift` gives an entire function $\beta\colon\mathbb C\to\mathbb C$ with $\beta(0)=0$ and, for every $x\in\mathbb C$,

$$
q_{\tau'}(\beta(x))=T(q_\tau(x)).
$$

[Common fibers and transfer](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRigidityTransfer.lean#L109) · [Entire lift](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRigidityTransfer.lean#L200)

### From lattice scaling to equality of $j$

For each $\ell\in\Lambda_\tau$, the continuous function $x\mapsto\beta(x+\ell)-\beta(x)$ maps the connected plane into the discrete lattice $\Lambda_{\tau'}$. It is therefore constant. This makes $\beta'$ periodic with lattice $\Lambda_\tau$. Compactness of a closed fundamental parallelogram bounds $\beta'$ on $\mathbb C$. Liouville's theorem makes the derivative constant, and $\beta(0)=0$ gives $\beta(x)=ax$. The inverse transfer has a lift $x\mapsto bx$. Their composition induces the identity on the quotient, so $(ba-1)x\in\Lambda_\tau$ for every $x\in\mathbb C$. This continuous function takes values in a discrete lattice and vanishes at zero, so $ba=1$.

`exists_homothety` gives $a\in\mathbb C\setminus\{0\}$ such that $x\in\Lambda_\tau$ if and only if $ax\in\Lambda_{\tau'}$ for every $x\in\mathbb C$. Equivalently, $\Lambda_{\tau'}=a\Lambda_\tau$. Scaling the lattice multiplies the Weierstrass invariants $g_2,g_3$ by $a^{-4},a^{-6}$, respectively. Both numerator and denominator of $j=(12g_2)^3/(g_2^3-27g_3^2)$ acquire the factor $a^{-12}$. This proves $\operatorname{modularJ}(\tau)=\operatorname{modularJ}(\tau')$ in `modularJ_eq_of_homothety`.

Suppose the same pair $(A,B)$ uniformizes two complex Weierstrass curves $W,W'$ with nonzero discriminant. The two lattice lifts satisfy `SameFibres` because they both have the $\Gamma$-orbits as fibers modulo their lattices. Therefore `j_eq_of_uniformizes` gives $j(W)=j(W')$. [Lattice scaling](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRigidity.lean#L80) · [Modular $j$ invariance](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRigidity.lean#L125) · [Same-pair rigidity](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRigidity.lean#L147)

## 日本語

### 一意化から格子への持ち上げ

$W$ を判別式が零でない複素 Weierstrass 曲線とする。$A,B\in\mathrm{SL}_2(\mathbb R)$ とし、それらが生成する部分群を $\Gamma=\langle A,B\rangle$ とする。`IsUniformization W A B π` では、写像 $\pi\colon\mathbb C\to\mathbb C^2$ は $\mathbb H$ の各点で複素微分可能で、導関数は非零である。$\pi(\mathbb H)$ は $W$ のアフィン点全体に等しい。任意の $z,w\in\mathbb H$ について、$\pi(z)=\pi(w)$ であることと、$\gamma\cdot z=w$ を満たす $\gamma\in\Gamma$ が存在することは同値である。

`exists_isLatticeLift` は $j(W)=\operatorname{modularJ}(\tau)$ を満たす $\tau\in\mathbb H$ と、写像 $\sigma\colon\mathbb C\to\mathbb C$ を与える。$\sigma$ は $\mathbb H$ 上で $\Lambda_\tau$ に値を取らず、各点で複素微分可能で導関数が非零である。任意の $x\notin\Lambda_\tau$ に対し、$\sigma(z)-x\in\Lambda_\tau$ を満たす $z\in\mathbb H$ が存在する。任意の $z,w\in\mathbb H$ に対し、次が成り立つ。

$$
\sigma(z)-\sigma(w)\in\Lambda_\tau
\quad\Longleftrightarrow\quad
\exists\,\gamma\in\Gamma,\ \gamma\cdot z=w .
$$

格子曲線を $W$ に移す Weierstrass 変数変換 $C$ を取る。格子の補集合への被覆を $\Psi\colon\mathbb H\to\mathbb C\setminus\Lambda_\tau$、変数変換後の Weierstrass パラメータ表示を $P_{\tau,C}$ とする。一意化の一意性により、$\pi(z)=P_{\tau,C}(\Psi(g\cdot z))$ を満たす $g\in\mathrm{SL}_2(\mathbb R)$ が得られる。そこで $\sigma(z)=\Psi(g\cdot z)$ とおく。Möbius 変換の導関数は非零である。格子の補集合で $P_{\tau,C}$ の値が等しいことと、引数の差が周期であることは同値である。 [一意化](../../../../Solutions/Source_ReferenceIutCanLiftUniformizationCover.lean#L69) · [格子への持ち上げ](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRigidityLift.lean#L55)

### 共通のファイバーから整関数へ

$\sigma,\sigma'$ がそれぞれ $\Lambda_\tau,\Lambda_{\tau'}$ に対する `IsLatticeLift` の条件を満たすとする。`SameFibres` は任意の $z,w\in\mathbb H$ について、$\sigma(z)-\sigma(w)\in\Lambda_\tau$ と $\sigma'(z)-\sigma'(w)\in\Lambda_{\tau'}$ が同値であることをいう。各非零類は $q_\tau(\sigma(z))$ と表せる。`SameFibres` により、その像 $q_{\tau'}(\sigma'(z))$ は $z$ の選び方によらない。零類の像を零類とすると、`transfer` は商空間の間の全単射 $T$ を与える。二つの持ち上げを入れ替えると逆写像が得られる。

非零類の代表元 $x_0$ に対し、$\sigma(z_0)=x_0+\ell$ となる $z_0$ と $\ell\in\Lambda_\tau$ を取る。$x_0$ の近くの点を $\ell$ だけ平行移動してから $\sigma$ の正則な局所逆写像を適用し、切断 $s$ を得る。局所表示 $T(q_\tau(y))=q_{\tau'}(\sigma'(s(y)))$ により、$T$ は非零類で連続である。二つの商空間はコンパクト Hausdorff 空間である。逆写像が零類以外で連続であることから、$T$ は零類でも連続となる。

$\mathbb C$ は凸なので、$T\circ q_\tau$ は被覆写像 $q_{\tau'}$ を通して $\beta(0)=0$ を満たす連続写像 $\beta$ に持ち上がる。$\Lambda_\tau$ の外では、$\beta$ は $\sigma'\circ s$ に一定の周期を加えた形で局所的に表される。格子点は孤立しており、連続性によりそこでの特異点は除去可能である。`exists_entire_lift` は $\beta(0)=0$ を満たす整関数 $\beta\colon\mathbb C\to\mathbb C$ を与え、任意の $x\in\mathbb C$ に対して次が成り立つ。

$$
q_{\tau'}(\beta(x))=T(q_\tau(x)).
$$

[共通のファイバーと商写像](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRigidityTransfer.lean#L109) · [整関数への持ち上げ](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRigidityTransfer.lean#L200)

### 格子の複素数倍と $j$ の一致

各 $\ell\in\Lambda_\tau$ に対し、連続関数 $x\mapsto\beta(x+\ell)-\beta(x)$ は連結な複素平面から離散格子 $\Lambda_{\tau'}$ に値を取るため定数である。したがって $\beta'$ は $\Lambda_\tau$ に関して周期的であり、閉基本平行四辺形のコンパクト性から $\mathbb C$ 上で有界である。Liouville の定理により導関数は定数であり、$\beta(0)=0$ から $\beta(x)=ax$ が得られる。逆写像も $x\mapsto bx$ の形に持ち上がる。二つの持ち上げの合成は商空間上で恒等写像を誘導するので、任意の $x\in\mathbb C$ に対して $(ba-1)x\in\Lambda_\tau$ である。この連続関数は離散格子に値を取り、原点で零であるから、$ba=1$ となる。

`exists_homothety` は、任意の $x\in\mathbb C$ に対して $x\in\Lambda_\tau$ と $ax\in\Lambda_{\tau'}$ が同値となる $a\in\mathbb C\setminus\{0\}$ を与える。これは $\Lambda_{\tau'}=a\Lambda_\tau$ と同値である。格子を $a$ 倍すると、Weierstrass 不変量 $g_2,g_3$ はそれぞれ $a^{-4},a^{-6}$ 倍される。$j=(12g_2)^3/(g_2^3-27g_3^2)$ の分子と分母はともに $a^{-12}$ 倍されるので、`modularJ_eq_of_homothety` は $\operatorname{modularJ}(\tau)=\operatorname{modularJ}(\tau')$ を与える。

同じ行列対 $(A,B)$ が判別式の零でない二つの複素 Weierstrass 曲線 $W,W'$ を一意化するとする。二つの持ち上げは格子を法として同じ $\Gamma$ の軌道をファイバーにもつので、`SameFibres` を満たす。したがって `j_eq_of_uniformizes` により $j(W)=j(W')$ が成り立つ。 [格子の複素数倍](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRigidity.lean#L80) · [モジュラー $j$ の不変性](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRigidity.lean#L125) · [同じ行列対に対する剛性](../../../../Solutions/Source_ReferenceIutCanLiftTakeuchiRigidity.lean#L147)

## Lean 声明与回执 · Lean declarations and receipts · Lean の宣言と検査記録

MCP-CI 的三份叶检查回执均为 `succeeded`，退出码为 $0$。回执中的源文件 SHA-256 与本稿核对的文件一致。

| Lean 声明 | MCP-CI 叶检查 | 固定版本的代码来源 |
| --- | --- | --- |
| `exists_isLatticeLift` | `ci-024236-baa61aed` | [Lattice.lean](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Rigidity/Lattice.lean) · [Lift.lean](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Rigidity/Lift.lean) |
| `SameFibres`, `transfer`, `exists_entire_lift` | `ci-024252-359893ed` | [Transfer.lean](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Rigidity/Transfer.lean#L26) |
| `exists_homothety`, `modularJ_eq_of_homothety`, `j_eq_of_uniformizes` | `ci-024263-d85d8bf9` | [Transfer.lean](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Rigidity/Transfer.lean#L220) · [Rigidity.lean](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/S1/Rigidity.lean) |
