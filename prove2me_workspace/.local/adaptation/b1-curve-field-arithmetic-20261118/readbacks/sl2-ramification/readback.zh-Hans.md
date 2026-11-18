# 形式声明读回

## `EllipticCurveData.prime_dvd_ramificationIdx`

设 $F$ 为数域，$\overline F$ 为 $F$ 的选定代数闭包，$E$ 为 $F$ 上的 Weierstrass 椭圆曲线。这些对象由 $C$ 给出，$F$ 与 $\overline F$ 属于同一宇宙层级。令 $M=\mathbb Q(j(E))\subseteq F$ 为模域。有限位 $z$ 对应整数环的非零极大理想 $\mathfrak p_z$，其剩余特征是该整数环模 $\mathfrak p_z$ 所得剩余域的特征。一个有限位位于另一个有限位上方，是指前者的理想收缩为后者的理想。

令 $W$ 为 $F$ 上 $E$ 具有乘法约化的有限位集合。这里的乘法约化指存在 $F$ 上的 Weierstrass 变量变换，使所得模型扩张到该位的完备化后，在完备化的赋值环上具有乘法约化。

算术记录 $CA:C.\mathrm{CurveArithmetic}$ 给出以下条件。

- $-1$ 在 $F$ 中为平方。
- 在 $F$ 的每个有限位，$E$ 经 $F$ 上的变量变换后具有好约化或乘法约化。
- $E(\overline F)$ 中每个被 $6$ 倍映射送到单位元的点都来自 $E(F)$。
- 对每个素数 $r\geq 7$，$F/M$ 是 Galois 扩张，且 $[F:M]$ 与 $r$ 互素。
- $F$ 的每个有限位都位于 $M$ 的某个有限位上方。凡是具有这种上下关系的两个有限位，其剩余特征均相等。
- 对 $M$ 的任意剩余特征不等于 $2$ 的有限位，若 $E$ 在其上方的一个 $F$ 的有限位具有乘法约化，则在其上方的每个 $F$ 的有限位都具有乘法约化。
- $W$ 是有限集合。$F$ 的每个有限位相对于其下方有理素数的剩余次数为正。
- 对每个自然数 $r$，$W$ 中剩余特征为 $r$ 的各位的剩余次数之和至多为 $[F:\mathbb Q]$。

对每个 $w\in W$，记录 $TI:C.\mathrm{TateInputs}$ 给出 $q_w\in F_w^\times$，满足 $\lVert q_w\rVert<1$，其中 $F_w$ 是 $F$ 在 $w$ 处的完备化。由 $q_w$ 确定的 Tate 曲线的 $j$ 不变量等于 $j(E)$ 在 $F_w$ 中的像。记录还给出一个【译名待定：TERM-015】$\pi_w$。它满足 $\pi_w\ne0$ 和 $\lVert\pi_w\rVert<1$，并且 $F_w^\times$ 中每个元素的范数都是 $\lVert\pi_w\rVert$ 的某个整数次幂。令 $n_w$ 为满足 $\lVert q_w\rVert=\lVert\pi_w\rVert^{n_w}$ 的唯一正整数。这个自然数即 `TI.qOrder w hw`。

设 $\ell$ 是不等于 $2$ 的素数。记录 $R:C.\mathrm{ModEllRepData}\,\ell$ 给出加法群同构 $b:E(\overline F)[\ell]\simeq\mathbb F_\ell^2$，以及群同态 $\rho:\operatorname{Aut}_F(\overline F)\to\mathrm{GL}_2(\mathbb F_\ell)$。$\rho$ 的核在 Krull 拓扑下是开子群。对每个 $\sigma\in\operatorname{Aut}_F(\overline F)$ 和 $P\in E(\overline F)[\ell]$，记录要求 $b(\sigma P)=\rho(\sigma)b(P)$，其中 $\sigma$ 作用于点的坐标并固定单位元。令 $K=\overline F^{\ker\rho}$ 为 $R$ 所定义的挠点域。$K$ 是数域。

取任意 $w\in W$，其剩余特征既不等于 $2$，也不等于 $\ell$，且 $\ell\nmid n_w$。对 $K$ 中任意位于 $w$ 上方的有限位 $w'$，定理断言
$$\ell\mid e(w'/w).$$
这里 $e(w'/w)$ 是 $\mathfrak p_{w'}$ 在 $\mathfrak p_w$ 上的分歧指数，取值于自然数。

## 子义务一　`tateStructureOfTorsion`

设 $E/F$ 为数域 $F$ 上的 Weierstrass 椭圆曲线，$\overline F$ 为选定的代数闭包，$K$ 为 $\overline F/F$ 中的一个中间数域。$F$、$\overline F$ 和 $K$ 属于同一宇宙层级。令 $M=\mathbb Q(j(E))$，并令 $V$ 为 $M$ 的有限位的一个集合。假设 $V$ 中各位的剩余特征不等于 $2$，且对每个 $v\in V$ 及其上方的每个 $F$ 的有限位，$E$ 在该 $F$ 的有限位具有乘法约化。此处乘法约化沿用前一条陈述中的变量变换定义。

设 $\ell$ 是不等于 $2$ 的素数。令 $T_K$ 为 $E(K)$ 的加法子群，满足 $T_K\subseteq E(K)[\ell]=\{P:\ell P=0\}$ 及 $\operatorname{Nat.card}(T_K)\geq\ell^2$。设 $w'$ 为 $K$ 的一个有限位，位于某个 $v\in V$ 上方，其中位于上方的关系由对应的理想确定。则该构造给出扩张到 $K_{w'}$ 的曲线 $E_{K_{w'}}$ 上的一个 Tate 结构 $S$。

对 $k=K_{w'}$ 上的 Weierstrass 曲线 $B$，一个 Tate 结构包含以下数据。

- 参数 $q\in k^\times$，满足 $\lVert q\rVert<1$。
- $k$ 上的 Weierstrass 变量变换 $D$，满足 $D\cdot B=E_q$，其中 $E_q$ 为 $q$ 的 Tate Weierstrass 模型。
- 从改用加法记号的乘法商群 $k^\times/q^{\mathbb Z}$ 到 $B(k)$ 的加法群同构。
- 对每个不属于 $q^{\mathbb Z}$ 的 $u\in k^\times$，其类对应的点在变换后的模型 $E_q$ 中具有 Tate 坐标 $X_q(u),Y_q(u)$。

## 子义务二　`TateStructure.finite_torsion` 与 `TateStructure.exists_root_class`

设 $k$ 为域，带有一个指定的秩一赋值，其值域由采用乘法记号的 $\mathbb Z$ 添上零得到。假设 $k$ 对此赋值完备。取 $k$ 上的 Weierstrass 曲线 $B$ 和给定的 Tate 结构 $S$，其定义同上。以 $q$ 表示 $S$ 的 Tate 参数。群 $B(k)$ 由非奇异仿射 $k$ 点和无穷远点组成。对任意非零自然数 $\ell$，令 $B(k)[\ell]=\{P\in B(k):\ell P=0\}$。第一条断言 $B(k)[\ell]$ 是有限群。

若 $\ell^2\leq\operatorname{Nat.card}(B(k)[\ell])$，第二条给出 $u\in k^\times$ 和 $m\in\mathbb Z$，使得
$$u^\ell=q^{\,1+\ell m}\quad\text{在 }k^\times\text{ 中成立。}$$
右边的指数是整数。群 $k^\times$ 包含域 $k$ 的所有非零元素。

### 参考证明在给定有限位上的计算

在父定理的条件下，取 $E_{K_{w'}}$ 上的 Tate 结构 $S$，并令 $q$ 为其参数。全局挠点给出基数下界 $\ell^2\leq\operatorname{Nat.card}(E(K_{w'})[\ell])$。因此，由上述根类计算得到 $K_{w'}^\times$ 中的等式 $u^\ell=q^{1+\ell m}$。

记 $\operatorname{ord}_{w'}$ 为 $K_{w'}^\times$ 的归一化加法赋值。$q$ 的 Tate 曲线的 $j$ 不变量等于 $j(E)$ 在 $K_{w'}$ 中的像。扩域后的阶满足 $\operatorname{ord}_{w'}(q)=e(w'/w)n_w$。对根等式取加法赋值，得到
$$\ell\,\operatorname{ord}_{w'}(u)=(1+\ell m)e(w'/w)n_w.$$
右侧模 $\ell$ 同余于 $e(w'/w)n_w$，故 $\ell$ 整除 $e(w'/w)n_w$。因为 $\ell$ 是素数且 $\ell\nmid n_w$，所以 $\ell$ 整除 $e(w'/w)$。
