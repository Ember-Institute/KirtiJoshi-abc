# 局部 Tate 结构与分歧指数的整除性 · Local Tate structure and divisibility of ramification indices · 局所テイト構造と分岐指数の整除

本稿依据下文所列 Lean 声明及其前置定义。分歧定理的原始读回另见同目录的三个语言版本。 [简体中文](sl2-ramification/readback.zh-Hans.md) · [English](sl2-ramification/readback.en.md) · [日本語](sl2-ramification/readback.ja.md)

## 简体中文 · 形式声明对照

### 1. 超度量域中的平方根

设 $k$ 为完备超度量赋范域，且 $\lVert2\rVert=1$。对任意 $a,x_0\in k$，若 $\lVert x_0\rVert=1$ 且 $\lVert x_0^2-a\rVert<1$，则存在 $x\in k$ 满足 $x^2=a$ 和 $\lVert x-x_0\rVert<1$。因此，任意满足 $\lVert a-1\rVert<1$ 的 $a\in k$ 都有平方根。证明以 $x_0$ 为初值，对 $x\mapsto(x+a/x)/2$ 迭代并取极限。 [1](#1-ultrametricsqrt)

### 2. Weierstrass 换元对点群的作用

设 $k$ 为域，$W/k$ 为 Weierstrass 曲线，$C=(d,r,s,t)$ 为换元，其中 $d\in k^\times$，$r,s,t\in k$。这里 $k^\times$ 是 $k$ 的非零元素组成的乘法群。点群由非奇异仿射 $k$ 点与无穷远点组成。换元给出从 $W(k)$ 到 $(C\cdot W)(k)$ 的加法群同构 $\phi_C$。它固定无穷远点，并将每个仿射点 $(x,y)$ 送到

$$
\left(\frac{x-r}{d^2},\frac{y-t-s(x-r)}{d^3}\right).
$$

对 $k$ 上任意另一条 Weierstrass 曲线 $W'$，若 $W=W'$，则该等式给出保持两个坐标的加法群同构 $W(k)\simeq W'(k)$。在无穷远点，两种坐标函数均取零。 [2](#2-variablechangepoint)

### 3. 切线二次式与完备化

对赋范域 $k$ 上的 Weierstrass 曲线 $W$，令

$$
T_W(z)=c_4z^2+a_1c_4z-(54b_6-3b_2b_4+a_2c_4).
$$

这里的系数与不变量都取自 $W$。对任意 $z\in k$，有 $(2c_4z+a_1c_4)^2=-c_4c_6+4c_4T_W(z)$。若 $2\ne0$、$c_4\ne0$，且 $s_0\in k$ 满足 $s_0^2=-c_4c_6$，则存在 $z\in k$ 满足 $\lVert T_W(z)\rVert<1$。证明所取的 $z=(s_0-a_1c_4)/(2c_4)$ 满足 $T_W(z)=0$。

对任意满足 $s_0^2=-c_4c_6$ 的 $s_0$ 和缩放系数为 $d$ 的换元 $C$，都有 $(d^{-5}s_0)^2=-c_4(C\cdot W)c_6(C\cdot W)$。若 $W$ 为椭圆曲线、$\lVert c_4\rVert=1$ 且 $\lVert\Delta\rVert<1$，则 $\lVert j(W)\rVert>1$。 [3](#3-tatelocalmodels)

设 $F$ 为数域，$L$ 为带给定 $F$-代数结构的域，$K$ 为 $L/F$ 的一个中间数域。$F$ 与 $L$ 属于同一 Lean 宇宙层级。设 $E/F$ 为 Weierstrass 曲线，$w$ 为 $K$ 的有限位。记 $K_w$ 为完备化，$E_w$ 为 $E$ 扩张到 $K_w$ 后的模型。

在 $F$ 上换元再扩域到 $K_w$，与先扩域再用所诱导的换元，得到同一模型。$-c_4(E_w)c_6(E_w)$ 是 $-c_4(E)c_6(E)$ 在复合映射 $F\to K\to K_w$ 下的像。一个有限位位于另一个有限位上方，是指它对应的极大理想收缩为后者对应的极大理想。有限位的剩余特征是整数环对该位对应的极大理想取商所得域的特征。若 $w$ 位于 $F$ 的有限位 $v_0$ 上方，则 $v_0(c_4(E))=1$ 推出 $\lVert c_4(E_w)\rVert=1$，$v_0(\Delta(E))<1$ 推出 $\lVert\Delta(E_w)\rVert<1$。式中的 $v_0$ 表示乘法赋值。

若 $E$ 为椭圆曲线，令 $M=\mathbb Q(j(E))$，取 $M$ 的有限位集合 $V$。设 $w$ 位于某个 $v\in V$ 上方。若 $E$ 在所有位于 $V$ 上方的 $F$ 的有限位都有乘法约化，则 $E$ 在 $w$ 下方的 $F$ 的有限位也具有乘法约化。若 $V$ 中各位的剩余特征均异于 $2$，则在 $K_w$ 中有 $\lVert2\rVert=1$。在一个有限位具有乘法约化，指存在 $F$ 上的换元，使所得模型在该位完备化的赋值环上具有乘法约化。 [3](#3-tatelocalmodels)

### 4. Tate 模型

设 $k$ 为完备超度量赋范域，满足 $\lVert2\rVert=1$ 和 $12\ne0$。令 $W/k$ 为 Weierstrass 椭圆曲线。若 $\lVert c_4(W)\rVert=1$、$\lVert\Delta(W)\rVert<1$，且某个 $z\in k$ 满足 $\lVert T_W(z)\rVert<1$，则存在 $q\in k^\times$ 与 $k$ 上的换元 $D$，满足 $\lVert q\rVert<1$、$D\cdot W=E_q$ 和 $\mathrm{tateJ}(q)=j(W)$。 [4](#4-tateisomorphism)

对每个自然数 $m$，令 $s_m(q)=\sum_{i\ge1}i^m q^i/(1-q^i)$ 为 Eisenstein 级数。Tate 模型 $E_q$ 的仿射方程与系数如下。

$$
y^2+xy=x^3+a_4(q)x+a_6(q),\qquad
a_4(q)=-5s_3(q),\qquad a_6(q)=-\frac{5s_3(q)+7s_5(q)}{12}.
$$

源码将 $\mathrm{tateJ}(q)$ 定义为 $c_4(E_q)^3/\Delta(E_q)$。在定理的假设下，该值等于 $E_q$ 的 $j$ 不变量。

### 5. 固定 Tate 坐标的均匀化

给定赋范域 $k$ 及 Tate 参数 $q\in k^\times$，其中 $\lVert q\rVert<1$。均匀化数据由加法群同构 $U:(k^\times/q^{\mathbb Z})_{\mathrm{add}}\simeq E_q(k)$ 和两条坐标等式组成。$[u]$ 表示 $u$ 在商群中的类，商群的群运算改用加法记号。对每个 $u\in k^\times$，若对每个 $n\in\mathbb Z$ 都有 $q^nu\ne1$，则两个坐标函数在 $U([u])$ 处的值分别为 $X_q(u),Y_q(u)$。这两个 Tate 坐标级数为

$$
X_q(u)=\sum_{n\in\mathbb Z}\frac{q^nu}{(1-q^nu)^2}-2s_1(q),\qquad
Y_q(u)=\sum_{n\in\mathbb Z}\frac{(q^nu)^2}{(1-q^nu)^3}+s_1(q).
$$

这些级数使用 Lean 的求和约定，不可求和时取值为零。域中的除法采用 $0^{-1}=0$ 的约定。

在完备超度量赋范域中，若 $12\ne0$，且对上述每个 $u$，$(X_q(u),Y_q(u))$ 满足 $E_q$ 的仿射方程，就可定义点映射 $P_q$。它把 $q^{\mathbb Z}$ 中每个元素送到无穷远点，并把其余单位送到坐标为 $(X_q(u),Y_q(u))$ 的非奇异仿射点。

再假设对所有 $u,v\in k^\times$ 都有 $P_q(uv)=P_q(u)+P_q(v)$，并且 $E_q(k)$ 的每个点都有原像。此时同态的核恰为 $q^{\mathbb Z}$，故商群给出 $U$ 和两条坐标等式。

适配后的方程定理在 $12\ne0$ 时给出上述仿射方程。加法和满射定理以方程证明为输入，并要求 $\lVert2\rVert=1$。加法定理还要求 $k$ 上的相等关系可判定。构造器 `TateParameterUniformization.ofTateParameter` 在 $12\ne0$ 且 $\lVert2\rVert=1$ 时对每个 $q$ 给出均匀化数据。 [5](#5-tateuniformization) · [7](#7-source-dependencies)

### 6. 坏处上的 Tate 结构

设 $k$ 为带指定秩一赋值且对此赋值完备的域，赋值的值域为乘法记号下的 $\mathbb Z$ 添零。给定 Weierstrass 曲线 $W/k$、Tate 参数 $q$、Weierstrass 换元 $D$、等式 $D\cdot W=E_q$ 和第 5 节的均匀化数据，`TateStructure.ofVariableChangeWithUniformization` 用曲线等式与 $\phi_D^{-1}$ 把 $U$ 搬到 $W(k)$。所得结构记录 $q,D$、模型等式和加法群同构。对每个 $u\in k^\times\setminus q^{\mathbb Z}$，$[u]$ 对应点在换元模型中的两个坐标为 $X_q(u),Y_q(u)$。

采用第 3 节中 $E$ 为椭圆曲线时的 $F,L,K,E,V,w$。假设 $V$ 中各有限位的剩余特征异于 $2$，且对每个 $v\in V$，$E$ 在 $v$ 上方的每个 $F$ 的有限位都具有乘法约化。令 $w$ 位于某个 $v\in V$ 上方。适配后的构造器 `tateStructureOfBadPlace` 另取以下输入。

- $K_w$ 中存在元素，其平方等于 $-c_4(E)c_6(E)$ 在 $K_w$ 中的像。
- 对 $K_w$ 中每个 Tate 参数，给定 $12\ne0$ 与 $\lVert2\rVert=1$ 的证明就能构造第 5 节的均匀化数据。

在这些条件下，构造器给出 $E_w$ 上的 Tate 结构。它选取乘法约化模型，把平方根搬过去以满足切线二次式的条件，再选取使该模型成为 Tate 曲线的第二个换元。最后用两次换元的复合把均匀化搬回 $E_w$。 [6](#6-tatestructureoftorsion)

来源声明 `exists_sq_eq_neg_c₄_mul_c₆` 与 `tateStructureOfTorsion` 沿用以上关于约化和有限位的条件，并取 $L$ 为 $F$ 的选定代数闭包。设 $\ell$ 为自然数中的素数且 $\ell\ne2$，$T_K$ 为 $E(K)[\ell]=\{P\in E(K):\ell P=0\}$ 的加法子群，满足 $\operatorname{Nat.card}(T_K)\ge\ell^2$。$\operatorname{Nat.card}$ 对有限类型给出其基数，对无限类型取值为零。对每个这样的 $w$，平方根定理给出 $s\in K_w$，使 $s^2$ 等于 $-c_4(E)c_6(E)$ 在 $K_w$ 中的像。来源构造器在同样的假设下给出 $E_w$ 上的 Tate 结构。 [6](#6-tatestructureoftorsion) · [7](#7-source-dependencies)

另设 $k,W$ 满足本节开头的条件，给定 $W$ 上的 Tate 结构 $S$，记其参数为 $q$。对每个非零自然数 $\ell$，`finite_torsion` 断言 $W(k)[\ell]=\{P:\ell P=0\}$ 有限，`card_torsion_le` 给出其基数上界 $\ell^2$。若 $\ell^2\le\operatorname{Nat.card}(W(k)[\ell])$，则 `exists_root_class` 给出 $u\in k^\times$ 和 $m\in\mathbb Z$，使得 $u^\ell=q^{1+\ell m}$ 在 $k^\times$ 中成立。右边的指数取整数值。 [7](#7-source-dependencies)

### 7. 指定有限位上的分歧指数

来源和适配后的分歧定理都接收曲线数据 $C$，其中包含数域 $F$、选定的代数闭包 $\overline F$ 和 Weierstrass 椭圆曲线 $E/F$。$F$ 与 $\overline F$ 属于同一 Lean 宇宙层级。令 $M=\mathbb Q(j(E))$，$W$ 为 $E$ 具有乘法约化的 $F$ 的有限位集合。曲线算术记录 $CA$ 给出以下事实。

- $-1$ 在 $F$ 中是平方。
- 对 $F$ 的每个有限位，$E$ 有半稳定约化。也就是说，存在 $F$ 上的换元，使所得模型在完备化的赋值环上有良好约化或乘法约化。
- $E(\overline F)$ 中每个被 $6$ 倍映射送到单位元的点都来自 $E(F)$。
- 对每个素数 $r\ge7$，$F/M$ 是 Galois 扩张且 $[F:M]$ 与 $r$ 互素。
- $F$ 的每个有限位位于 $M$ 的某个有限位上方。
- 具有上述关系的任意两处的剩余特征相同。
- 对 $M$ 中剩余特征异于 $2$ 的任意有限位 $v$，若 $E$ 在 $v$ 上方一处具有乘法约化，则在 $v$ 上方每处都具有乘法约化。
- $W$ 有限。
- $F$ 的每个有限位相对于其下方有理素数的剩余次数为正。
- 对每个自然数 $r$，$W$ 中剩余特征为 $r$ 的各位的剩余次数之和至多为 $[F:\mathbb Q]$。

对每个 $w\in W$，$TI$ 给定 $q_w\in F_w^\times$，满足 $\lVert q_w\rVert<1$，其中 $F_w$ 为 $F$ 在 $w$ 处的完备化。$\mathrm{tateJ}(q_w)$ 等于 $j(E)$ 在 $F_w$ 中的像。记录还给定素元$\pi_w\in F_w$，满足 $0<\lVert\pi_w\rVert<1$。对每个 $x\in F_w^\times$，存在整数 $m$ 使得 $\lVert x\rVert=\lVert\pi_w\rVert^m$。令 $n_w=\mathrm{TI.qOrder}(w,hw)$，即满足 $\lVert q_w\rVert=\lVert\pi_w\rVert^{n_w}$ 的唯一正整数。

设 $\ell$ 为自然数中的素数且 $\ell\ne2$。记录 $R$ 给出加法群同构 $b:E(\overline F)[\ell]\simeq(\mathbb Z/\ell\mathbb Z)^2$ 和群同态 $\rho:\operatorname{Aut}_F(\overline F)\to\mathrm{GL}_2(\mathbb Z/\ell\mathbb Z)$。对每个 $\sigma\in\operatorname{Aut}_F(\overline F)$ 和 $P\in E(\overline F)[\ell]$，有 $b(\sigma P)=\rho(\sigma)b(P)$。$\sigma$ 作用于点的坐标并固定无穷远点。$\ker\rho$ 在 Krull 拓扑中是开子群。令 $K=\overline F^{\ker\rho}$，这是一个数域。

取任意 $w\in W$，其剩余特征异于 $2$ 和 $\ell$，且 $\ell\nmid n_w$。对 $K$ 的任意位于 $w$ 上方的有限位 $w'$，定理断言 $\ell\mid e(w'/w)$，其中 $e(w'/w)$ 为整数环中对应极大理想的相对分歧指数，取值于自然数。

对任意自然数 $\ell$，$V_{\mathrm{BadOf}}(\ell)$ 恰由满足以下条件的 $M$ 的有限位组成。

- 该位的剩余特征异于 $2$ 和 $\ell$。
- 该位上方至少有一个 $F$ 的有限位。
- $E$ 在该位上方的每个 $F$ 的有限位都有乘法约化。

引理 `badPlacesOver_VBadOf` 假设 $C$ 和 $CA$。对任意自然数 $\ell$，它断言 $V_{\mathrm{BadOf}}(\ell)$ 上方的 $F$ 的有限位恰为 $W$ 中剩余特征异于 $2$ 和 $\ell$ 的各位。

证明用此等式和位于上方关系的传递性，将 $w'$ 置于 $V_{\mathrm{BadOf}}(\ell)$ 上方。这里取 $T_K=E(K)[\ell]$，其基数为 $\ell^2$。平方根定理和均匀化构造器给出 $w'$ 处的 Tate 结构。从 $K$ 上点群到完备化上点群的单射给出局部 $\ell$ 挠点的基数下界 $\ell^2$。对该结构的 Tate 参数 $q$，根类定理给出 $u\in K_{w'}^\times$ 和 $m\in\mathbb Z$，满足 $u^\ell=q^{1+\ell m}$。

两处的 Tate $j$ 不变量及赋值扩张公式给出 $\operatorname{ord}_{w'}(q)=e(w'/w)n_w$。对根等式取归一化加法赋值，得到

$$
\ell\operatorname{ord}_{w'}(u)=(1+\ell m)e(w'/w)n_w.
$$

模 $\ell$ 化简得 $\ell\mid e(w'/w)n_w$。因为 $\ell$ 为素数且 $\ell\nmid n_w$，所以 $\ell\mid e(w'/w)$。 [7](#7-source-dependencies) · [8](#8-ramification)

## English · Formal statements

### 1. Square roots in an ultrametric field

Let $k$ be a complete ultrametric normed field with $\lVert2\rVert=1$. Let $a,x_0\in k$ satisfy $\lVert x_0\rVert=1$ and $\lVert x_0^2-a\rVert<1$. Then there is an $x\in k$ with $x^2=a$ and $\lVert x-x_0\rVert<1$. Thus every $a\in k$ with $\lVert a-1\rVert<1$ has a square root in $k$. The proof starts at $x_0$ and takes the limit of the iteration $x\mapsto(x+a/x)/2$. [1](#1-ultrametricsqrt)

### 2. Changes of Weierstrass variables on point groups

Let $k$ be a field and $W$ a Weierstrass curve over $k$. Let $C=(d,r,s,t)$ be a change of variables with $d\in k^\times$ and $r,s,t\in k$. Here $k^\times$ is the multiplicative group of nonzero elements of $k$. The point group consists of nonsingular affine $k$-points and the point at infinity. The change gives an additive isomorphism $\phi_C:W(k)\simeq(C\cdot W)(k)$. It fixes the point at infinity and sends each affine point $(x,y)$ to

$$
\left(\frac{x-r}{d^2},\frac{y-t-s(x-r)}{d^3}\right).
$$

For any second Weierstrass curve $W'$ over $k$, an equality $W=W'$ gives an additive isomorphism $W(k)\simeq W'(k)$. This isomorphism preserves both coordinates. Each coordinate function has value zero at the point at infinity. [2](#2-variablechangepoint)

### 3. The tangent quadratic and completion

Let $W$ be a Weierstrass curve over a normed field $k$. Define

$$
T_W(z)=c_4z^2+a_1c_4z-(54b_6-3b_2b_4+a_2c_4).
$$

The coefficients and invariants belong to $W$. For each $z\in k$, $(2c_4z+a_1c_4)^2=-c_4c_6+4c_4T_W(z)$. Suppose $s_0\in k$ satisfies $s_0^2=-c_4c_6$. If $2\ne0$ and $c_4\ne0$, then some $z\in k$ satisfies $\lVert T_W(z)\rVert<1$. The proof uses $z=(s_0-a_1c_4)/(2c_4)$, which satisfies $T_W(z)=0$.

For any $s_0$ with $s_0^2=-c_4c_6$ and any change $C$ with scale $d$, we have $(d^{-5}s_0)^2=-c_4(C\cdot W)c_6(C\cdot W)$. If $W$ is elliptic, $\lVert c_4\rVert=1$ and $\lVert\Delta\rVert<1$ imply $\lVert j(W)\rVert>1$. [3](#3-tatelocalmodels)

Let $F$ be a number field and $L$ a field with a specified $F$-algebra structure. Let $K$ be an intermediate field of $L/F$ that is a number field. The fields $F$ and $L$ have the same Lean universe level. Let $E$ be a Weierstrass curve over $F$, and let $w$ be a finite place of $K$. Write $K_w$ for the completion and $E_w$ for the base change of $E$ to $K_w$.

A change of variables over $F$ commutes with base change to $K_w$. The element $-c_4(E_w)c_6(E_w)$ is the image of $-c_4(E)c_6(E)$ under the composition $F\to K\to K_w$. A finite place lies over another if its maximal ideal contracts to the other's maximal ideal. The residue characteristic is the characteristic of the ring of integers modulo the maximal ideal of the place. If $w$ lies over a finite place $v_0$ of $F$, then $v_0(c_4(E))=1$ implies $\lVert c_4(E_w)\rVert=1$. Under the same relation, $v_0(\Delta(E))<1$ implies $\lVert\Delta(E_w)\rVert<1$. In these formulas $v_0$ denotes the multiplicative valuation.

For elliptic $E$, put $M=\mathbb Q(j(E))$ and let $V$ be a set of finite places of $M$. Suppose $w$ lies over some $v\in V$. If $E$ has multiplicative reduction at every finite place of $F$ above $V$, then $E$ has multiplicative reduction at the place below $w$. If every place in $V$ has residue characteristic different from $2$, then $\lVert2\rVert=1$ in $K_w$. Multiplicative reduction at a finite place means that some change over $F$ gives a model with multiplicative reduction over the completed valuation ring. [3](#3-tatelocalmodels)

### 4. The Tate model

Let $k$ be a complete ultrametric normed field with $\lVert2\rVert=1$ and $12\ne0$. Let $W$ be a Weierstrass elliptic curve over $k$. Assume $\lVert c_4(W)\rVert=1$ and $\lVert\Delta(W)\rVert<1$. Also assume that some $z\in k$ satisfies $\lVert T_W(z)\rVert<1$. Then there are $q\in k^\times$ and a change of variables $D$ over $k$. They satisfy $\lVert q\rVert<1$, $D\cdot W=E_q$, and $\mathrm{tateJ}(q)=j(W)$. [4](#4-tateisomorphism)

For each natural number $m$, let $s_m(q)=\sum_{i\ge1}i^m q^i/(1-q^i)$ be the Eisenstein series. The Tate model $E_q$ has the following affine equation and coefficients.

$$
y^2+xy=x^3+a_4(q)x+a_6(q),\qquad
a_4(q)=-5s_3(q),\qquad a_6(q)=-\frac{5s_3(q)+7s_5(q)}{12}.
$$

The code defines $\mathrm{tateJ}(q)$ as $c_4(E_q)^3/\Delta(E_q)$. This value is the $j$-invariant of $E_q$ under the hypotheses of the theorem.

### 5. Uniformization with prescribed Tate coordinates

Let $k$ be a normed field and let $q\in k^\times$ satisfy $\lVert q\rVert<1$. Uniformization data give an additive isomorphism $U:(k^\times/q^{\mathbb Z})_{\mathrm{add}}\simeq E_q(k)$ and two coordinate laws. Here $[u]$ is the class of $u$ in the quotient, with the group law written additively. Let $u\in k^\times$ satisfy $q^nu\ne1$ for every $n\in\mathbb Z$. The coordinate functions at $U([u])$ have values $X_q(u),Y_q(u)$. These are the Tate coordinate series.

$$
X_q(u)=\sum_{n\in\mathbb Z}\frac{q^nu}{(1-q^nu)^2}-2s_1(q),\qquad
Y_q(u)=\sum_{n\in\mathbb Z}\frac{(q^nu)^2}{(1-q^nu)^3}+s_1(q).
$$

Lean assigns zero to an infinite sum if its series is nonsummable. Field division uses the convention $0^{-1}=0$.

Suppose $k$ is complete and ultrametric, and $12\ne0$ in $k$. Assume that for each such $u$, the pair $(X_q(u),Y_q(u))$ satisfies the affine equation of $E_q$. This defines the point map $P_q$. It sends each $u\in q^{\mathbb Z}$ to the point at infinity. It sends each other unit to the nonsingular affine point with coordinates $(X_q(u),Y_q(u))$.

Suppose $P_q(uv)=P_q(u)+P_q(v)$ for all $u,v\in k^\times$. Also suppose every point of $E_q(k)$ has a preimage. The kernel is $q^{\mathbb Z}$, so the quotient gives $U$ with both coordinate laws.

The adapted equation theorem gives the affine equation when $12\ne0$, for every $u\in k^\times$ with $q^nu\ne1$ for all $n\in\mathbb Z$. The additivity and surjectivity theorems take the equation as input. They also require $\lVert2\rVert=1$. The additivity theorem takes decidable equality on $k$. The constructor `TateParameterUniformization.ofTateParameter` gives the uniformization data for each $q$ under $12\ne0$ and $\lVert2\rVert=1$. [5](#5-tateuniformization) · [7](#7-source-dependencies)

### 6. A Tate structure at a bad place

Let $k$ be a field with a rank-one valuation in the multiplicative copy of $\mathbb Z$ with zero adjoined. Assume $k$ is complete for this valuation. Let $W/k$ be a Weierstrass curve and $q$ a Tate parameter. Let $D$ be a change of Weierstrass variables with $D\cdot W=E_q$. Supply uniformization data for $q$ as in section 5. The constructor `TateStructure.ofVariableChangeWithUniformization` uses the curve equality and $\phi_D^{-1}$ to transport $U$ to $W(k)$. The structure records $q,D$, the model equality, and the additive isomorphism. For each $u\in k^\times\setminus q^{\mathbb Z}$, the image of $[u]$ has coordinates $X_q(u),Y_q(u)$ in the changed model.

Use $F,L,K,E,V,w$ from the elliptic case in section 3. Assume that each place in $V$ has residue characteristic different from $2$. Assume that $E$ has multiplicative reduction at every finite place of $F$ above each $v\in V$. Let $w$ lie above some $v\in V$. The adapted constructor `tateStructureOfBadPlace` takes two further inputs.

- There is an element of $K_w$ whose square is the image of $-c_4(E)c_6(E)$.
- For every Tate parameter in $K_w$, proofs of $12\ne0$ and $\lVert2\rVert=1$ give the uniformization data from section 5.

From these inputs the constructor gives a Tate structure on $E_w$. It chooses a multiplicative model and uses the square root to obtain the tangent bound. It then chooses a second change of variables that gives the Tate curve. The composition of both changes transports the uniformization to $E_w$. [6](#6-tatestructureoftorsion)

The source declarations `exists_sq_eq_neg_c₄_mul_c₆` and `tateStructureOfTorsion` use the same reduction and place hypotheses. For these declarations $L$ is a chosen algebraic closure of $F$. Let $\ell$ be a prime natural number with $\ell\ne2$. Let $T_K$ be an additive subgroup of $E(K)[\ell]=\{P\in E(K):\ell P=0\}$ with $\operatorname{Nat.card}(T_K)\ge\ell^2$. The function $\operatorname{Nat.card}$ gives the cardinality of a finite type and returns zero for an infinite type. For each such $w$, the square-root theorem gives $s\in K_w$ with $s^2$ equal to the image of $-c_4(E)c_6(E)$. The source constructor gives a Tate structure on $E_w$ under the same hypotheses. [6](#6-tatestructureoftorsion) · [7](#7-source-dependencies)

Let $k,W$ satisfy the conditions at the start of this section. Let $S$ be a Tate structure on $W$ with parameter $q$. For every nonzero natural number $\ell$, `finite_torsion` shows that $W(k)[\ell]=\{P:\ell P=0\}$ is finite. The lemma `card_torsion_le` gives the upper bound $\ell^2$ on its cardinality. If $\ell^2\le\operatorname{Nat.card}(W(k)[\ell])$, then `exists_root_class` gives $u\in k^\times$ and $m\in\mathbb Z$ with $u^\ell=q^{1+\ell m}$ in $k^\times$. The exponent on the right is an integer. [7](#7-source-dependencies)

### 7. The ramification index at the specified place

The source and adapted ramification theorems take curve data $C$. It gives a number field $F$, a chosen algebraic closure $\overline F$, and a Weierstrass elliptic curve $E/F$. The fields $F$ and $\overline F$ have the same Lean universe level. Put $M=\mathbb Q(j(E))$. Let $W$ be the set of finite places of $F$ where $E$ has multiplicative reduction. The arithmetic record $CA$ gives the following facts.

- The element $-1$ is a square in $F$.
- At each finite place of $F$, the curve $E$ has semistable reduction. Some change over $F$ gives good or multiplicative reduction over the completed valuation ring.
- Each point of $E(\overline F)$ killed by multiplication by $6$ comes from $E(F)$.
- For every prime $r\ge7$, $F/M$ is Galois and $[F:M]$ is coprime to $r$.
- Every finite place of $F$ lies over a finite place of $M$.
- For every pair of places with this relation, their residue characteristics are equal.
- Fix a finite place $v$ of $M$ with residue characteristic different from $2$. If $E$ has multiplicative reduction at one place above $v$, it has multiplicative reduction at every place above $v$.
- The set $W$ is finite.
- Each finite place of $F$ has positive residue degree over its rational prime.
- For each natural number $r$, the sum of residue degrees in $W$ at residue characteristic $r$ is at most $[F:\mathbb Q]$.

For each $w\in W$, $TI$ gives $q_w\in F_w^\times$ with $\lVert q_w\rVert<1$. Here $F_w$ is the completion of $F$ at $w$. The value $\mathrm{tateJ}(q_w)$ equals the image of $j(E)$ in $F_w$. The record also gives a uniformizer $\pi_w\in F_w$ with $0<\lVert\pi_w\rVert<1$. For every $x\in F_w^\times$, there is an integer $m$ with $\lVert x\rVert=\lVert\pi_w\rVert^m$. Write $n_w=\mathrm{TI.qOrder}(w,hw)$ for the unique positive integer with $\lVert q_w\rVert=\lVert\pi_w\rVert^{n_w}$.

Let $\ell$ be a prime natural number with $\ell\ne2$. The record $R$ gives an additive isomorphism $b:E(\overline F)[\ell]\simeq(\mathbb Z/\ell\mathbb Z)^2$. It gives a group homomorphism $\rho:\operatorname{Aut}_F(\overline F)\to\mathrm{GL}_2(\mathbb Z/\ell\mathbb Z)$. For every $\sigma\in\operatorname{Aut}_F(\overline F)$ and $P\in E(\overline F)[\ell]$, we have $b(\sigma P)=\rho(\sigma)b(P)$. The automorphism $\sigma$ acts on point coordinates and fixes the point at infinity. The kernel of $\rho$ is open in the Krull topology. Put $K=\overline F^{\ker\rho}$, a number field.

Let $w\in W$ have residue characteristic different from $2$ and $\ell$, and assume $\ell\nmid n_w$. For every finite place $w'$ of $K$ above $w$, the theorem asserts $\ell\mid e(w'/w)$ in $\mathbb N$. Here $e(w'/w)$ is the relative ramification index of the corresponding maximal ideals in the rings of integers.

For any natural number $\ell$, the set $V_{\mathrm{BadOf}}(\ell)$ consists of the finite places of $M$ with the following properties.

- The residue characteristic differs from $2$ and $\ell$.
- At least one finite place of $F$ lies above the place.
- The curve $E$ has multiplicative reduction at every finite place of $F$ above the place.

The lemma `badPlacesOver_VBadOf` assumes $C$ and $CA$. For every natural number $\ell$, it identifies the places of $F$ above $V_{\mathrm{BadOf}}(\ell)$. They are exactly the places in $W$ with residue characteristic different from $2$ and $\ell$.

The proof uses this equality and transitivity of lying over to put $w'$ above $V_{\mathrm{BadOf}}(\ell)$. It uses $T_K=E(K)[\ell]$, which has cardinality $\ell^2$. The square-root theorem and the uniformization constructor give a Tate structure at $w'$. The injection from $K$-points gives at least $\ell^2$ points of local $\ell$-torsion. For the parameter $q$ of this structure, the root-class theorem gives $u\in K_{w'}^\times$ and $m\in\mathbb Z$ with $u^\ell=q^{1+\ell m}$.

Comparison of Tate $j$-invariants and the valuation formula for an extension give $\operatorname{ord}_{w'}(q)=e(w'/w)n_w$. The normalized additive valuation of the root equation gives the equality

$$
\ell\operatorname{ord}_{w'}(u)=(1+\ell m)e(w'/w)n_w.
$$

Reduction modulo $\ell$ gives $\ell\mid e(w'/w)n_w$. Since $\ell$ is prime and $\ell\nmid n_w$, it divides $e(w'/w)$. [7](#7-source-dependencies) · [8](#8-ramification)

## 日本語 · 形式宣言の対照

### 1. 超距離体における平方根

$k$ を $\lVert2\rVert=1$ を満たす完備な超距離ノルム体とする。任意の $a,x_0\in k$ に対し、$\lVert x_0\rVert=1$ かつ $\lVert x_0^2-a\rVert<1$ ならば、$x^2=a$ かつ $\lVert x-x_0\rVert<1$ となる $x\in k$ が存在する。したがって、$\lVert a-1\rVert<1$ を満たす任意の $a\in k$ は $k$ 内に平方根を持つ。証明では $x_0$ を初期値とする反復 $x\mapsto(x+a/x)/2$ の極限を取る。 [1](#1-ultrametricsqrt)

### 2. ワイエルシュトラス変数変換と点の群

$k$ を体、$W/k$ をワイエルシュトラス曲線とする。$d\in k^\times$ と $r,s,t\in k$ を成分とする変数変換 $C=(d,r,s,t)$ を取る。ここで $k^\times$ は $k$ の非零元の乗法群である。点の群は非特異なアフィン $k$ 点と無限遠点からなる。この変数変換は加法群同型 $\phi_C:W(k)\simeq(C\cdot W)(k)$ を与える。この同型は無限遠点を固定し、各アフィン点 $(x,y)$ を

$$
\left(\frac{x-r}{d^2},\frac{y-t-s(x-r)}{d^3}\right)
$$

へ写す。$k$ 上の任意のワイエルシュトラス曲線 $W'$ に対し、等式 $W=W'$ は両座標を保つ加法群同型 $W(k)\simeq W'(k)$ を与える。無限遠点では二つの座標関数の値を零とする。 [2](#2-variablechangepoint)

### 3. 接線の二次式と完備化

$W$ をノルム体 $k$ 上のワイエルシュトラス曲線とし、

$$
T_W(z)=c_4z^2+a_1c_4z-(54b_6-3b_2b_4+a_2c_4)
$$

と定める。係数と不変量は $W$ のものである。任意の $z\in k$ に対し、$(2c_4z+a_1c_4)^2=-c_4c_6+4c_4T_W(z)$ が成り立つ。$2\ne0$、$c_4\ne0$ であり、$s_0\in k$ が $s_0^2=-c_4c_6$ を満たすならば、$\lVert T_W(z)\rVert<1$ となる $z\in k$ が存在する。証明で用いる $z=(s_0-a_1c_4)/(2c_4)$ は $T_W(z)=0$ を満たす。

$s_0^2=-c_4c_6$ を満たす任意の $s_0$ と、拡大係数が $d$ である任意の変数変換 $C$ に対し、$(d^{-5}s_0)^2=-c_4(C\cdot W)c_6(C\cdot W)$ が成り立つ。$W$ が楕円曲線で $\lVert c_4\rVert=1$ と $\lVert\Delta\rVert<1$ を満たすならば、$\lVert j(W)\rVert>1$ である。 [3](#3-tatelocalmodels)

$F$ を数体、$L$ を指定された $F$ 代数構造を持つ体、$K$ を $L/F$ の中間体である数体とする。$F$ と $L$ は Lean で同じ宇宙レベルに属する。$E/F$ をワイエルシュトラス曲線、$w$ を $K$ の有限素点とする。$K_w$ は完備化、$E_w$ は $E$ の $K_w$ への基底変換である。

$F$ 上の変数変換と $K_w$ への基底変換は可換である。$-c_4(E_w)c_6(E_w)$ は $-c_4(E)c_6(E)$ の合成 $F\to K\to K_w$ による像である。有限素点が別の有限素点の上にあるとは、対応する極大イデアルの収縮が下の素点の極大イデアルに等しいことをいう。有限素点の剰余標数は、その素点の極大イデアルによる整数環の商体の標数である。$w$ が $F$ の有限素点 $v_0$ の上にあれば、$v_0(c_4(E))=1$ から $\lVert c_4(E_w)\rVert=1$ が従う。同じ条件で $v_0(\Delta(E))<1$ から $\lVert\Delta(E_w)\rVert<1$ が従う。ここで $v_0$ は乗法付値を表す。

$E$ が楕円曲線の場合、$M=\mathbb Q(j(E))$ とし、$V$ を $M$ の有限素点の集合とする。$w$ はある $v\in V$ の上にあるとする。$V$ の上にある $F$ のすべての有限素点で $E$ が乗法的還元を持つならば、$w$ の下にある $F$ の素点でも乗法的還元を持つ。さらに、$V$ のすべての素点の剰余標数が $2$ と異なれば、$K_w$ では $\lVert2\rVert=1$ となる。ある有限素点で乗法的還元を持つとは、$F$ 上の変数変換で得たモデルが、その素点の完備化の付値環上で乗法的還元を持つことをいう。 [3](#3-tatelocalmodels)

### 4. テイト曲線のモデル

$k$ を $\lVert2\rVert=1$ と $12\ne0$ を満たす完備な超距離ノルム体とし、$W/k$ をワイエルシュトラス楕円曲線とする。$\lVert c_4(W)\rVert=1$、$\lVert\Delta(W)\rVert<1$ であり、ある $z\in k$ について $\lVert T_W(z)\rVert<1$ であるとする。このとき、$q\in k^\times$ と $k$ 上の変数変換 $D$ が存在し、$\lVert q\rVert<1$、$D\cdot W=E_q$、$\mathrm{tateJ}(q)=j(W)$ を満たす。 [4](#4-tateisomorphism)

各自然数 $m$ に対して Eisenstein 級数 $s_m(q)=\sum_{i\ge1}i^m q^i/(1-q^i)$ を定める。テイトモデル $E_q$ のアフィン方程式と係数は次のとおりである。

$$
y^2+xy=x^3+a_4(q)x+a_6(q),\qquad
a_4(q)=-5s_3(q),\qquad a_6(q)=-\frac{5s_3(q)+7s_5(q)}{12}.
$$

コードでは $\mathrm{tateJ}(q)$ を $c_4(E_q)^3/\Delta(E_q)$ と定める。定理の仮定の下で、この値は $E_q$ の $j$ 不変量に等しい。

### 5. テイト座標を定めた一意化

ノルム体 $k$ と、$\lVert q\rVert<1$ を満たすテイトパラメータ $q\in k^\times$ を取る。一意化のデータは加法群同型 $U:(k^\times/q^{\mathbb Z})_{\mathrm{add}}\simeq E_q(k)$ と二つの座標の等式からなる。$[u]$ は商群における $u$ の類を表し、商群の演算は加法で表記する。すべての $n\in\mathbb Z$ に対して $q^nu\ne1$ を満たす各 $u\in k^\times$ について、$U([u])$ での座標関数の値はそれぞれ $X_q(u),Y_q(u)$ である。これらは次のテイト座標級数である。

$$
X_q(u)=\sum_{n\in\mathbb Z}\frac{q^nu}{(1-q^nu)^2}-2s_1(q),\qquad
Y_q(u)=\sum_{n\in\mathbb Z}\frac{(q^nu)^2}{(1-q^nu)^3}+s_1(q).
$$

Lean では、総和可能でない級数の和を零とする。体の除法では $0^{-1}=0$ と定める。

$k$ は完備な超距離ノルム体であり、$12\ne0$ とする。上の条件を満たす各 $u$ について $(X_q(u),Y_q(u))$ が $E_q$ のアフィン方程式を満たせば、点の写像 $P_q$ が定まる。$q^{\mathbb Z}$ の各元は無限遠点へ、残りの単元は座標 $(X_q(u),Y_q(u))$ を持つ非特異なアフィン点へ写る。

さらに、すべての $u,v\in k^\times$ について $P_q(uv)=P_q(u)+P_q(v)$ が成り立ち、$E_q(k)$ の各点が原像を持つとする。このとき核は $q^{\mathbb Z}$ に等しく、商群を取ると同型 $U$ と二つの座標の等式が得られる。

移植した方程式の定理では、$12\ne0$ の下で上のアフィン方程式が成り立つ。加法性と全射性の定理は方程式の証明を引数に取り、$\lVert2\rVert=1$ も仮定する。加法性の定理では $k$ の等号が決定可能であることも仮定する。構成子 `TateParameterUniformization.ofTateParameter` は $12\ne0$ と $\lVert2\rVert=1$ の下で、各 $q$ に対して一意化のデータを与える。 [5](#5-tateuniformization) · [7](#7-source-dependencies)

### 6. 悪い還元を持つ素点でのテイト構造

$k$ を、零を付加した乗法表記の $\mathbb Z$ に値を取る指定された階数一の付値を持ち、その付値について完備な体とする。ワイエルシュトラス曲線 $W/k$、テイトパラメータ $q$、変数変換 $D$、等式 $D\cdot W=E_q$、および第 5 節の一意化データを与える。構成子 `TateStructure.ofVariableChangeWithUniformization` は曲線の等式と $\phi_D^{-1}$ により $U$ を $W(k)$ に移す。得られる構造は $q,D$、モデルの等式、加法群同型を記録する。各 $u\in k^\times\setminus q^{\mathbb Z}$ について、$[u]$ の像は変数変換後のモデルで座標 $X_q(u),Y_q(u)$ を持つ。

第 3 節の楕円曲線の場合の $F,L,K,E,V,w$ を用いる。$V$ の各有限素点の剰余標数が $2$ と異なり、各 $v\in V$ の上にある $F$ のすべての有限素点で $E$ が乗法的還元を持つとする。$w$ はある $v\in V$ の上にあるとする。移植した構成子 `tateStructureOfBadPlace` はさらに次の二つを引数に取る。

- $-c_4(E)c_6(E)$ の $K_w$ における像を平方とする元が $K_w$ に存在する。
- $K_w$ の任意のテイトパラメータに対し、$12\ne0$ と $\lVert2\rVert=1$ の証明から第 5 節の一意化データが得られる。

これらの条件の下で、構成子は $E_w$ 上のテイト構造を与える。まず乗法的還元を持つモデルを選び、そこに平方根を移して接線の二次式の条件を満たす。次に、そのモデルをテイト曲線へ移す変数変換を選ぶ。二つの変数変換の合成を用いて一意化を $E_w$ に移す。 [6](#6-tatestructureoftorsion)

参照元の宣言 `exists_sq_eq_neg_c₄_mul_c₆` と `tateStructureOfTorsion` では、還元と素点について上と同じ条件を課し、$L$ を $F$ の選んだ代数閉包とする。$\ell$ を $\ell\ne2$ を満たす自然数の素数とする。$T_K$ は $E(K)[\ell]=\{P\in E(K):\ell P=0\}$ の加法部分群であり、$\operatorname{Nat.card}(T_K)\ge\ell^2$ を満たすとする。$\operatorname{Nat.card}$ は有限型の要素数を与え、無限型では零を返す。この条件を満たす各 $w$ に対し、平方根の定理は $s\in K_w$ で $s^2$ が $-c_4(E)c_6(E)$ の $K_w$ における像に等しいものを与える。参照元の構成子は同じ仮定の下で $E_w$ 上のテイト構造を与える。 [6](#6-tatestructureoftorsion) · [7](#7-source-dependencies)

$k,W$ は本節冒頭の条件を満たすとする。$W$ 上のテイト構造 $S$ を取り、そのパラメータを $q$ とする。任意の非零自然数 $\ell$ に対し、`finite_torsion` は $W(k)[\ell]=\{P:\ell P=0\}$ が有限であることを示し、`card_torsion_le` はその位数の上界 $\ell^2$ を与える。$\ell^2\le\operatorname{Nat.card}(W(k)[\ell])$ ならば、`exists_root_class` は $u^\ell=q^{1+\ell m}$ を $k^\times$ で満たす $u\in k^\times$ と $m\in\mathbb Z$ を与える。右辺の指数は整数である。 [7](#7-source-dependencies)

### 7. 指定された有限素点での分岐指数

参照元と移植後の分岐指数の定理はともに曲線のデータ $C$ を取る。$C$ は数体 $F$、選んだ代数閉包 $\overline F$、ワイエルシュトラス楕円曲線 $E/F$ を与える。$F$ と $\overline F$ は Lean で同じ宇宙レベルに属する。$M=\mathbb Q(j(E))$ とし、$W$ を $E/F$ が乗法的還元を持つ $F$ の有限素点の集合とする。算術データ $CA$ は以下を与える。

- $-1$ は $F$ 内で平方である。
- $F$ の各有限素点で $E$ は半安定還元を持つ。すなわち、完備化の付値環上で良い還元または乗法的還元を持つモデルを与える $F$ 上の変数変換が存在する。
- $E(\overline F)$ で $6$ 倍が単位元となる各点は $E(F)$ の点から来る。
- 各素数 $r\ge7$ に対し $F/M$ はガロア拡大であり、$[F:M]$ と $r$ は互いに素である。
- $F$ の各有限素点は $M$ のある有限素点の上にある。
- この上下関係にある任意の二つの素点の剰余標数は等しい。
- $M$ の剰余標数が $2$ と異なる任意の有限素点 $v$ について、$v$ の上の一つの素点で $E$ が乗法的還元を持てば、その上のすべての素点で乗法的還元を持つ。
- $W$ は有限である。
- $F$ の各有限素点の、下にある有理素数に対する剰余次数は正である。
- 任意の自然数 $r$ に対し、$W$ のうち剰余標数が $r$ である素点の剰余次数の和は $[F:\mathbb Q]$ 以下である。

各 $w\in W$ について、$TI$ は $\lVert q_w\rVert<1$ を満たす $q_w\in F_w^\times$ を与える。ここで $F_w$ は $F$ の $w$ における完備化である。$\mathrm{tateJ}(q_w)$ は $j(E)$ の $F_w$ における像に等しい。$TI$ は $0<\lVert\pi_w\rVert<1$ を満たす素元 $\pi_w\in F_w$ も与える。任意の $x\in F_w^\times$ に対し、$\lVert x\rVert=\lVert\pi_w\rVert^m$ を満たす整数 $m$ が存在する。$\lVert q_w\rVert=\lVert\pi_w\rVert^{n_w}$ を満たす唯一の正整数 $n_w$ が $\mathrm{TI.qOrder}(w,hw)$ である。

$\ell$ を $\ell\ne2$ を満たす自然数の素数とする。データ $R$ は加法群同型 $b:E(\overline F)[\ell]\simeq(\mathbb Z/\ell\mathbb Z)^2$ と群準同型 $\rho:\operatorname{Aut}_F(\overline F)\to\mathrm{GL}_2(\mathbb Z/\ell\mathbb Z)$ を与える。任意の $\sigma\in\operatorname{Aut}_F(\overline F)$ と $P\in E(\overline F)[\ell]$ について、$b(\sigma P)=\rho(\sigma)b(P)$ が成り立つ。$\sigma$ は点の座標に作用し、無限遠点を固定する。$\rho$ の核はクルル位相で開である。固定体 $K=\overline F^{\ker\rho}$ は数体である。

剰余標数が $2$ と $\ell$ のいずれとも異なり、$\ell\nmid n_w$ を満たす任意の $w\in W$ を取る。その上にある $K$ の任意の有限素点 $w'$ に対し、自然数の整除関係 $\ell\mid e(w'/w)$ が成り立つ。ここで $e(w'/w)$ は整数環の対応する極大イデアルの相対分岐指数である。

任意の自然数 $\ell$ に対し、$V_{\mathrm{BadOf}}(\ell)$ は以下の条件を満たす $M$ の有限素点からなる。

- 剰余標数が $2$ と $\ell$ のいずれとも異なる。
- その上に少なくとも一つの $F$ の有限素点がある。
- その上にあるすべての $F$ の有限素点で $E$ が乗法的還元を持つ。

補題 `badPlacesOver_VBadOf` は $C$ と $CA$ を仮定する。任意の自然数 $\ell$ について、$V_{\mathrm{BadOf}}(\ell)$ の上にある $F$ の有限素点は、$W$ のうち剰余標数が $2$ と $\ell$ のいずれとも異なる素点に一致する。

証明ではこの等式と上下関係の推移性により、$w'$ が $V_{\mathrm{BadOf}}(\ell)$ の上にあることを得る。$T_K=E(K)[\ell]$ は位数 $\ell^2$ を持つ。平方根の定理と一意化の構成子により、$w'$ でのテイト構造を得る。$K$ 上の点の完備化への単射により、局所 $\ell$ 捩れ点の位数は $\ell^2$ 以上となる。この構造のテイトパラメータ $q$ について、根の類に関する定理から $u^\ell=q^{1+\ell m}$ を満たす $u\in K_{w'}^\times$ と $m\in\mathbb Z$ が得られる。

テイト曲線の $j$ 不変量の比較と拡大に伴う付値の公式から、$\operatorname{ord}_{w'}(q)=e(w'/w)n_w$ が成り立つ。根の等式に正規化した加法付値を適用すると、

$$
\ell\operatorname{ord}_{w'}(u)=(1+\ell m)e(w'/w)n_w
$$

を得る。$\ell$ を法として考えると $\ell\mid e(w'/w)n_w$ となる。$\ell$ は素数であり $\ell\nmid n_w$ であるため、$\ell\mid e(w'/w)$ が従う。 [7](#7-source-dependencies) · [8](#8-ramification)

## Lean 来源 · Lean sources · Lean の参照元

IUT source paths below refer to `lana-agents/iut` snapshot `07cb1da58f6d428a670dbb5dd6093d428bcbcdd8`. The mathematical proof files retain the contributor notices under Apache 2.0. The port notices credit Christian Merten as the Git author. [IUT license](/home/admin-wsl/Coq/abc/refer/iut/LICENSE) · [Earlier provenance record](sl2-ramification/source-and-reuse.md)

### 1. UltrametricSqrt

`exists_sq_eq_of_norm_sq_sub_lt` and `exists_sq_eq_of_norm_sub_one_lt` follow `Iut/Cor312/ThetaData/UltrametricSqrt.lean` at commit `09d74a40f46688fa5e4eba46ead73cb37d6abbe2`. [Target](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutUltrametricSqrt.lean:193) · [Source](/home/admin-wsl/Coq/abc/refer/iut/Iut/Cor312/ThetaData/UltrametricSqrt.lean:172)

### 2. VariableChangePoint

`vcEquiv`, `ptX`, `ptY`, and `pointCongr` follow `Iut/Cor312/ThetaData/VariableChangePoint.lean` at commit `a0879d37aa370169cbdd563d2919b02318166541`. [Target](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutVariableChangePoint.lean:347) · [Source](/home/admin-wsl/Coq/abc/refer/iut/Iut/Cor312/ThetaData/VariableChangePoint.lean:337)

### 3. TateLocalModels

`tangent_sq_eq` follows `TateIsomorphism.lean` at `09d74a40f46688fa5e4eba46ead73cb37d6abbe2`. `exists_tangent_root_of_sq`, `mult_placeUnder`, and the completed norms of $c_4$ and $\Delta$ follow `SqrtAtBadPlace.lean` at `e4777b2238f45be2e58c00b4d0213c0cb83405b9`. The square-root change and curve base change follow `TateFamilyOfTorsion.lean` at the same commit. `norm_two_curveKw` adapts the bad-place calculation from `BadPlaceNorm.lean` at `cfc9e36c8984a83c9199ccbb8d1b30d9c130edf6`. [Target](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTateLocalModels.lean:35) · [Tangent identity](/home/admin-wsl/Coq/abc/refer/iut/Iut/Cor312/ThetaData/TateIsomorphism.lean:162) · [Square root and norms](/home/admin-wsl/Coq/abc/refer/iut/Iut/Cor312/ThetaData/SqrtAtBadPlace.lean:53) · [Change of model](/home/admin-wsl/Coq/abc/refer/iut/Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean:52) · [Norm of two](/home/admin-wsl/Coq/abc/refer/iut/Iut/Cor312/ThetaData/BadPlaceNorm.lean:38)

### 4. TateIsomorphism

`exists_variableChange_tateCurve` follows `Iut/Cor312/ThetaData/TateIsomorphism.lean` at `09d74a40f46688fa5e4eba46ead73cb37d6abbe2`. The adaptation calls the existing proof of Tate parameter existence for the prescribed $j$. [Target](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTateIsomorphism.lean:283) · [Source](/home/admin-wsl/Coq/abc/refer/iut/Iut/Cor312/ThetaData/TateIsomorphism.lean:291) · [Parameter existence](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_TateCurvesTheta_QParameter_JExistence.lean:386)

### 5. TateUniformization

`TatePointEquation` and `tatePoint` use the adapted Tate coordinate series and the source point-map formula. `TateParameterUniformization.ofTatePoint` uses `QuotientGroup.liftEquiv` and records both coordinate laws. The Tate library revision is `ca6c2279d3cea0690cdb01328e727118d5485d68`. [Target point map](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTateUniformization.lean:47) · [Target quotient construction](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTateUniformization.lean:103) · [Source point map](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/.lake/packages/tate-curves-theta/TateCurvesTheta/TateCurve/PointMap.lean:103) · [Source uniformization](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/.lake/packages/tate-curves-theta/TateCurvesTheta/TateCurve/TateUniformization.lean:105) · [Coordinate definitions](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_TateCurvesTheta_TateCurve_Parametrization.lean:107) · [Dependency closure](tate-uniformization-sources.md)

### 6. TateStructureOfTorsion

`tateStructureOfBadPlace` and `TateStructure.ofVariableChangeWithUniformization` follow the model selection and transport of `TateFamilyOfTorsion.lean` at `e4777b2238f45be2e58c00b4d0213c0cb83405b9` and `TateStructureOfIso.lean` at `09d74a40f46688fa5e4eba46ead73cb37d6abbe2`. The Tate structure type follows `TateStructure.lean` at `76c7866b5bbc4adbd245a30af1a4fd05d32f8c3f`. The adapted constructor takes the square-root identity and the uniformization function explicitly. [Target transport](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTateStructureOfTorsion.lean:42) · [Target constructor](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTateStructureOfTorsion.lean:110) · [Source constructor](/home/admin-wsl/Coq/abc/refer/iut/Iut/Cor312/ThetaData/TateFamilyOfTorsion.lean:121) · [Source transport](/home/admin-wsl/Coq/abc/refer/iut/Iut/Cor312/ThetaData/TateStructureOfIso.lean:68) · [Source fields](/home/admin-wsl/Coq/abc/refer/iut/Iut/Cor312/ThetaData/TateStructure.lean:59)

### 7. Source dependencies

`Source_ReferenceIutSplitSquare` uses the main library's `JoshiTeich.ReferenceIut.exists_sq_eq_neg_c₄_mul_c₆`. Its input curves, finite places, and completion embeddings unfold to the same definitions in both namespaces. The original is `Iut/Cor312/ThetaData/SqrtAtBadPlace.lean` at `e4777b2238f45be2e58c00b4d0213c0cb83405b9`. [Target](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutSplitSquare.lean:27) · [Main library proof](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutCompat/Cor312/ThetaData/SqrtAtBadPlace.lean:351) · [Original](/home/admin-wsl/Coq/abc/refer/iut/Iut/Cor312/ThetaData/SqrtAtBadPlace.lean:343)

`Source_ReferenceIutTateUniformizationLaws` uses `tatePoint_mem'`, `tatePoint_mul`, and `tatePoint_surjective` from the pinned Tate library. It uses the same parameter unit, Weierstrass equation, and series in both namespaces. The two point maps agree by unfolding the definitions and by proof irrelevance. The migration lock records the proof-only compatibility patch for the Tate library at this revision. [Target](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTateUniformizationLaws.lean:23) · [Equation](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/.lake/packages/tate-curves-theta/TateCurvesTheta/TateCurve/TatePointOnCurve.lean:334) · [Additivity](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/.lake/packages/tate-curves-theta/TateCurvesTheta/TateCurve/GroupLaw.lean:242) · [Surjectivity](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/.lake/packages/tate-curves-theta/TateCurvesTheta/TateCurve/TateUniformization.lean:55) · [Environment lock](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/migration/environment.lock.json:18)

The source and adapted Tate torsion declarations have the same finiteness result, cardinality bound, and unit equation. [Source torsion declarations](/home/admin-wsl/Coq/abc/refer/iut/Iut/Anabelian/TateTorsion.lean:186) · [Adapted torsion declarations](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTateTorsion.lean:172)

### 8. Ramification

`badPlacesOver_VBadOf` follows `Iut/Concrete/Existence.lean`. The type of `prime_dvd_ramificationIdx_from_source` follows `Iut/Concrete/SL2Image.lean` at `47ef99c97945984ea799ee2333fcf920abecdae4`. The adapted proof supplies the Tate structure before it calls `prime_dvd_ramificationIdx_of_tateStructure`. [Target](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_SL2ImageLocalTate.lean:81) · [Source bad-place pullback](/home/admin-wsl/Coq/abc/refer/iut/Iut/Concrete/Existence.lean:228) · [Source ramification theorem](/home/admin-wsl/Coq/abc/refer/iut/Iut/Concrete/SL2Image.lean:162) · [Existing local proof](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_SL2ImageLocalTorsion.lean:58) · [Canonical Prove2Me target](/home/admin-wsl/Coq/abc/prove2me_workspace/Theorems/Thm_AbcAdaptation_Reference_Iut_EllipticCurveData_prime_dvd_ramificationIdx.lean:22)

## 论文出处 · Paper provenance · 論文の出典

Shinichi Mochizuki, *Arithmetic Elliptic Curves in General Position*, February 2009, §3, printed and PDF p. 15, before Lemma 3.2. Here $K$ is the local field in the paper, corresponding to the completion in the root argument. Definition 3.3 on p. 15 calls the positive additive order of the Tate parameter the local height. Remark 3.3.1 on p. 16 gives the normalization by the ramification index. The last part of Theorem 3.8 on p. 20 uses this local calculation in the image argument. [Official PDF](https://www.kurims.kyoto-u.ac.jp/~motizuki/Arithmetic%20Elliptic%20Curves%20in%20General%20Position.pdf) · [Local PDF](</home/admin-wsl/Coq/abc/refer/Mochizuki/Arithmetic Elliptic Curves in General Position.pdf>) · [Verified excerpt and file digest](sl2-ramification/source-and-reuse.md:27)

> Thus, the above exact sequence splits if and only if $q_E$ has an $l$-th root in $K$. Note that in order for this to happen, it is necessary that $v_K(q_E)$ be divisible by $l$. In particular, we have the following well-known result.

Shinichi Mochizuki, *Inter-universal Teichmüller Theory IV: Log-volume Computations and Set-theoretic Foundations*, April 2020. See §2, proof of Corollary 2.2(ii), on printed page 46 and PDF page 46. The local ramification theorem gives divisibility at the place used to bound the order of the Galois image. [Official PDF](https://www.kurims.kyoto-u.ac.jp/~motizuki/Inter-universal%20Teichmuller%20Theory%20IV.pdf) · [Local PDF](</home/admin-wsl/Coq/abc/refer/Mochizuki/Inter-universal Teichmuller Theory IV.pdf>) · [Verified excerpt and file digest](sl2-ramification/source-and-reuse.md:43)

> Indeed, since, by (P5), $E_F$ has bad multiplicative reduction at some valuation $\in\mathbb V_{\mathrm{mod}}^{\mathrm{bad}}\neq\emptyset$, (P6) follows formally from (P2), (P4), and [GenEll], Lemma 3.1, (iii) [cf. the proof of the final portion of [GenEll], Theorem 3.8].

## 验收范围 · Verification scope · 検証の範囲

主库和 Tate 库的编译产物用于本地 MCP-CI 验证。Prove2Me 平台发布与验收另行记录。 [项目依赖](/home/admin-wsl/Coq/abc/prove2me_workspace/lakefile.lean:7) · [Tate 库版本](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/migration/environment.lock.json:18)

The compiled main-library and Tate-library artifacts support local MCP-CI verification. Prove2Me publication and acceptance have separate records.

主ライブラリとテイト曲線ライブラリのコンパイル済み成果物はローカルの MCP-CI 検証に用いる。Prove2Me への公開と受理は別途記録する。
