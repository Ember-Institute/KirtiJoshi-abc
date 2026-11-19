# Descent of the product of the designated Vélu ratios

## English

For the provider curve `P.curve x`, write $E_\lambda/F$ for its Legendre model and $\bar F$ for the algebraic closure used in the representation. Let $\ell$ be an odd prime. Let $L$ be the $\ell$-torsion field of `P.modRep x ℓ hℓ`. Write $j\colon F\hookrightarrow L$ and $\iota\colon L\hookrightarrow\bar F$ for the field embeddings. The point map $\beta\colon E_\lambda(L)\hookrightarrow E_\lambda(\bar F)$ is `bcK`. [Torsion field](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:201) · [Point map and lift](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ModEllRepGalois.lean:58)

Let $H\le E_\lambda(\bar F)$ have order $\ell$. Assume that $\sigma Q\in H$ for every $Q\in H$ and $\sigma\in\operatorname{Gal}(\bar F/F)$, with $\sigma$ acting on the coordinates. Define $H_L=\beta^{-1}(H)$. Each element of $H$ is killed by $\ell$ and lifts to an $L$-rational point. Thus $\beta$ induces an additive isomorphism $H_L\simeq H$, so `card_HL` gives $|H_L|=\ell$. The lemma `finite_HL` allows a `Fintype` instance for $H_L$ to index the product. [Points killed by $\ell$](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutModEllRepCyclicSubgroup.lean:66) · [Subgroup isomorphism](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluDescent.lean:34) · [Cardinality](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluDescent.lean:55) · [Finiteness](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluDescent.lean:58)

### The ratio and its behavior under base change

Write $O$ for the identity and $X$ for the first coordinate with $X(O)=0$. For a finite subgroup $J$ and a pair of points on the same curve, `veluRatio` is

$$
V_J(T,R)=\prod_{Q\in J\setminus\{O\}}
\frac{X(T)-X(R+Q)}{X(T)-X(Q)}.
$$

The lemma `algebraMap_veluRatio` transports the ratio along $\iota$. The subgroup isomorphism reindexes the nonzero points, and $\beta$ preserves addition and applies $\iota$ to first coordinates. [Definition of the ratio](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicVeluRatio.lean:93) · [Coordinate transport](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluDescent.lean:61) · [Base change of the ratio](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluDescent.lean:71)

$$
\iota\bigl(V_{H_L}(T,R)\bigr)=V_H(\beta T,\beta R)
\qquad\bigl(T,R\in E_\lambda(L)\bigr).
$$

The designated pairs $(T_k,R_k)$ for $k=1,2$ are the base changes of $(T_{k,\mathrm{base}},R_{k,\mathrm{base}})$ from $F$ to $L$. Let $a,b,i\in F$ be the chosen roots with $a^2=\lambda$, $b^2=1-\lambda$, and $i^2=-1$. Over $F$ the points are

$$
\begin{aligned}
T_{1,\mathrm{base}}&=(0,0), & R_{1,\mathrm{base}}&=(a,ia(a-1)),\\
T_{2,\mathrm{base}}&=(1,0), & R_{2,\mathrm{base}}&=(1+b,b(1+b)).
\end{aligned}
$$

For each pair, $T_k$ has order two and $[2]R_k=T_k$. The odd order of $H_L$ implies $T_k\notin H_L$, and then $R_k\notin H_L$ because $[2]R_k=T_k$. For $Q\in H_L\setminus\{O\}$, equality $X(Q)=X(T_k)$ would give $Q=\pm T_k=T_k$. The point $R_k+Q$ is nonzero. Equality $X(R_k+Q)=X(T_k)$ would give $R_k+Q=T_k$, hence $Q=R_k$. Both equalities contradict subgroup membership. Thus all the numerator and denominator factors in the two ratios are nonzero. [Base points](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:168) · [Composition of point maps](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:226) · [Doubling](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:252) · [Nonzero factors](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicVeluRatio.lean:99) · [Nonzero designated ratios](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluDescent.lean:101)

### Descent to $F$ and the logarithmic product formula

Galois fixes the four base points and permutes $H\setminus\{O\}$, since the stability assumption also applies to $\sigma^{-1}$. The lemma `veluRatio_galois` reindexes each geometric ratio by that permutation. Therefore their product is fixed by every $F$-automorphism of $\bar F$ and comes from an element $\rho\in F$. The embedding $\iota$ is injective. The transport formula gives this equality in $L$, and the nonzero ratios imply $\rho\ne0$. [Galois reindexing](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicVeluRatio.lean:150) · [Fixed-field descent](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicVeluRatio.lean:196) · [Descent in the reference](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/CyclicIsogeny.lean:275) · [Lean theorem](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluDescent.lean:112)

$$
\rho\in F^\times,\qquad
j(\rho)=V_{H_L}(T_1,R_1)\,V_{H_L}(T_2,R_2).
$$

For every finite set $S$ of finite places of $F$ that contains all $v$ with $|\rho|_v\ne1$, the same theorem `exists_ratio_logProductFormula` gives the logarithmic product formula. The proof takes the logarithm of the multiplicative product formula, using positivity of each absolute value. Here $m_v$ is 1 at a real place and 2 at a complex place. [Logarithmic product formula](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicVeluRatio.lean:241) · [Multiplicities](/home/admin-wsl/Coq/mathlib4-0df444a/Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean:274)

$$
\sum_{v\mid\infty} m_v\log|\rho|_v+\sum_{v\in S}\log|\rho|_v=0.
$$

MCP-CI leaf check `ci-022337-967b971f` passed on `Source_TripodCyclicVeluDescent.lean` with exit code 0 and two `letI` style warnings. [MCP-CI receipt](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-022337-967b971f-result.json)

Project and axiom review passed. [MCP-CI](../receipts/round-ci-022356-38c5d13c-result.json)

## 中文

对 `P.curve x`，记其 Legendre 模型为 $E_\lambda/F$，表示中使用的代数闭包为 $\bar F$。取奇素数 $\ell$，令 $L$ 为 `P.modRep x ℓ hℓ` 的 $\ell$ 挠点域。记域嵌入为 $j\colon F\hookrightarrow L$、$\iota\colon L\hookrightarrow\bar F$，点的基变换 $\beta\colon E_\lambda(L)\hookrightarrow E_\lambda(\bar F)$ 对应 `bcK`。 [挠点域](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:201) · [点映射与提升](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ModEllRepGalois.lean:58)

设 $H\le E_\lambda(\bar F)$ 的阶为 $\ell$。假设每个 $Q\in H$ 和 $\sigma\in\operatorname{Gal}(\bar F/F)$ 都满足 $\sigma Q\in H$，其中 $\sigma$ 按坐标作用。令 $H_L=\beta^{-1}(H)$。$H$ 中每个点都被 $\ell$ 消去且可提升为 $L$ 上的有理点。因此 $\beta$ 诱导加法群同构 $H_L\simeq H$，`card_HL` 给出 $|H_L|=\ell$。由 `finite_HL` 可为 $H_L$ 选取 `Fintype` 实例，用于给乘积加上指标。 [被 $\ell$ 消去的点](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutModEllRepCyclicSubgroup.lean:66) · [子群同构](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluDescent.lean:34) · [基数](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluDescent.lean:55) · [有限性](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluDescent.lean:58)

### 比值及其基变换

记点群的零元为 $O$，横坐标为 $X$，约定 $X(O)=0$。对有限子群 $J$ 和同一曲线上的一对点，`veluRatio` 定义为

$$
V_J(T,R)=\prod_{Q\in J\setminus\{O\}}
\frac{X(T)-X(R+Q)}{X(T)-X(Q)}.
$$

`algebraMap_veluRatio` 沿 $\iota$ 传递比值。子群同构给出非零点之间的双射，$\beta$ 保持点的加法，并在横坐标上作用为 $\iota$。 [比值的定义](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicVeluRatio.lean:93) · [坐标的基变换](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluDescent.lean:61) · [比值的基变换](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluDescent.lean:71)

$$
\iota\bigl(V_{H_L}(T,R)\bigr)=V_H(\beta T,\beta R)
\qquad\bigl(T,R\in E_\lambda(L)\bigr).
$$

两对指定点 $(T_k,R_k)$（$k=1,2$）由 $(T_{k,\mathrm{base}},R_{k,\mathrm{base}})$ 从 $F$ 基变换到 $L$ 得到。记选定的平方根为 $a,b,i\in F$，满足 $a^2=\lambda$、$b^2=1-\lambda$、$i^2=-1$。在 $F$ 上，这些点为

$$
\begin{aligned}
T_{1,\mathrm{base}}&=(0,0), & R_{1,\mathrm{base}}&=(a,ia(a-1)),\\
T_{2,\mathrm{base}}&=(1,0), & R_{2,\mathrm{base}}&=(1+b,b(1+b)).
\end{aligned}
$$

每个 $T_k$ 的阶为二，且 $[2]R_k=T_k$。由 $H_L$ 的奇数阶得 $T_k\notin H_L$，继而由倍点等式得 $R_k\notin H_L$。取 $Q\in H_L\setminus\{O\}$。如果 $X(Q)=X(T_k)$，则 $Q=\pm T_k=T_k$。点 $R_k+Q$ 非零。如果 $X(R_k+Q)=X(T_k)$，则 $R_k+Q=T_k$，故 $Q=R_k$。两种等式都与 $Q\in H_L$ 矛盾。因此两个比值的分子与分母中的因子均非零。 [基域上的点](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:168) · [点映射的复合](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:226) · [倍点等式](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:252) · [因子非零](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicVeluRatio.lean:99) · [指定比值非零](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluDescent.lean:101)

### 下降到 $F$ 与对数乘积公式

Galois 作用固定四个基域点。稳定性也适用于 $\sigma^{-1}$，故 $\sigma$ 置换 $H\setminus\{O\}$。`veluRatio_galois` 通过该置换对每个几何比值的乘积换指标。因此两个比值的乘积被 $\bar F$ 的所有 $F$-自同构固定，来自某个 $\rho\in F$。由 $\iota$ 的单射性及比值的基变换公式，得到下列在 $L$ 中的等式。两个比值均非零，故 $\rho\ne0$。 [Galois 作用下换指标](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicVeluRatio.lean:150) · [不动域下降](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicVeluRatio.lean:196) · [参考下降证明](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/CyclicIsogeny.lean:275) · [Lean 定理](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluDescent.lean:112)

$$
\rho\in F^\times,\qquad
j(\rho)=V_{H_L}(T_1,R_1)\,V_{H_L}(T_2,R_2).
$$

取 $F$ 的任意有限位有限集 $S$，其中包含所有满足 $|\rho|_v\ne1$ 的有限位。`exists_ratio_logProductFormula` 同时给出对数乘积公式。各处的绝对值均为正，证明对乘积公式取对数。$m_v$ 在实位为 1，在复位为 2。 [对数乘积公式](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicVeluRatio.lean:241) · [无穷位重数](/home/admin-wsl/Coq/mathlib4-0df444a/Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean:274)

$$
\sum_{v\mid\infty} m_v\log|\rho|_v+\sum_{v\in S}\log|\rho|_v=0.
$$

`Source_TripodCyclicVeluDescent.lean` 的 MCP-CI 叶检查 `ci-022337-967b971f` 通过，退出码为 0，有两条 `letI` 风格警告。 [MCP-CI 回执](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-022337-967b971f-result.json)

项目与公理审查通过。 [MCP-CI](../receipts/round-ci-022356-38c5d13c-result.json)

## 日本語

`P.curve x` の Legendre モデルを $E_\lambda/F$、表現に用いる代数閉包を $\bar F$ とする。$\ell$ を奇素数とし、$L$ を `P.modRep x ℓ hℓ` の $\ell$-ねじれ点体とする。体の埋め込みを $j\colon F\hookrightarrow L$ および $\iota\colon L\hookrightarrow\bar F$ と書く。点の写像 $\beta\colon E_\lambda(L)\hookrightarrow E_\lambda(\bar F)$ は `bcK` である。 [ねじれ点体](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:201) · [点の写像と持ち上げ](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ModEllRepGalois.lean:58)

$H\le E_\lambda(\bar F)$ の位数を $\ell$ とする。すべての $Q\in H$ と $\sigma\in\operatorname{Gal}(\bar F/F)$ について $\sigma Q\in H$ と仮定する。ここで $\sigma$ は座標に作用する。$H_L=\beta^{-1}(H)$ とおく。$H$ の各点は $\ell$ 倍で零元になり、$L$ 上の有理点に持ち上がる。従って $\beta$ は加法群の同型 $H_L\simeq H$ を誘導し、`card_HL` により $|H_L|=\ell$ となる。`finite_HL` から $H_L$ の `Fintype` インスタンスを取り、積の添字に使える。 [$\ell$ 倍で零元になる点](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutModEllRepCyclicSubgroup.lean:66) · [部分群の同型](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluDescent.lean:34) · [位数](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluDescent.lean:55) · [有限性](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluDescent.lean:58)

### 比と基底変換

零元を $O$、第一座標を $X$ とし、$X(O)=0$ とおく。有限部分群 $J$ と同じ曲線上の一組の点に対し、`veluRatio` は次の積である。

$$
V_J(T,R)=\prod_{Q\in J\setminus\{O\}}
\frac{X(T)-X(R+Q)}{X(T)-X(Q)}.
$$

`algebraMap_veluRatio` は比を $\iota$ で移す。部分群の同型で非零点の積の添字を付け替える。$\beta$ は加法を保ち、第一座標に $\iota$ を適用する。 [比の定義](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicVeluRatio.lean:93) · [座標の基底変換](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluDescent.lean:61) · [比の基底変換](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluDescent.lean:71)

$$
\iota\bigl(V_{H_L}(T,R)\bigr)=V_H(\beta T,\beta R)
\qquad\bigl(T,R\in E_\lambda(L)\bigr).
$$

指定した二組の点 $(T_k,R_k)$（$k=1,2$）は $(T_{k,\mathrm{base}},R_{k,\mathrm{base}})$ を $F$ から $L$ に基底変換したものである。選んだ平方根を $a,b,i\in F$ とし、$a^2=\lambda$、$b^2=1-\lambda$、$i^2=-1$ とする。$F$ 上では次の点である。

$$
\begin{aligned}
T_{1,\mathrm{base}}&=(0,0), & R_{1,\mathrm{base}}&=(a,ia(a-1)),\\
T_{2,\mathrm{base}}&=(1,0), & R_{2,\mathrm{base}}&=(1+b,b(1+b)).
\end{aligned}
$$

各 $T_k$ の位数は 2 であり、$[2]R_k=T_k$ である。$H_L$ の位数は奇数なので $T_k\notin H_L$ となり、倍点の等式により $R_k\notin H_L$ となる。$Q\in H_L\setminus\{O\}$ とする。$X(Q)=X(T_k)$ ならば $Q=\pm T_k=T_k$ となる。$R_k+Q$ は非零点である。$X(R_k+Q)=X(T_k)$ ならば $R_k+Q=T_k$ であり、$Q=R_k$ となる。どちらの等式も $Q\in H_L$ に矛盾する。従って、二つの比の分子と分母の因子はいずれも非零である。 [基礎体上の点](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:168) · [点の写像の合成](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:226) · [倍点の等式](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluPoints.lean:252) · [因子の非零性](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicVeluRatio.lean:99) · [指定した比の非零性](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluDescent.lean:101)

### $F$ への降下と対数積公式

Galois 作用は基礎体上の四点を固定する。安定性の仮定は $\sigma^{-1}$ にも適用できるため、$\sigma$ は $H\setminus\{O\}$ を置換する。`veluRatio_galois` は各幾何的な比の積の添字をこの置換で付け替える。二つの比の積は $\bar F$ のすべての $F$-自己同型で固定されるため、ある $\rho\in F$ の像である。$\iota$ の単射性と比の基底変換の等式により、$L$ で次の等式を得る。二つの比が非零なので $\rho\ne0$ である。 [Galois 作用による添字の付け替え](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicVeluRatio.lean:150) · [固定体への降下](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicVeluRatio.lean:196) · [参照元の降下の証明](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/CyclicIsogeny.lean:275) · [Lean の定理](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodCyclicVeluDescent.lean:112)

$$
\rho\in F^\times,\qquad
j(\rho)=V_{H_L}(T_1,R_1)\,V_{H_L}(T_2,R_2).
$$

$|\rho|_v\ne1$ を満たすすべての有限素点 $v$ を含む $F$ の有限素点の有限集合 $S$ を取る。`exists_ratio_logProductFormula` は対数積公式も与える。各絶対値は正なので、証明では積公式の対数を取る。$m_v$ は実素点で 1、複素素点で 2 である。 [対数積公式](/home/admin-wsl/Coq/abc/ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/IutCyclicVeluRatio.lean:241) · [無限素点の重複度](/home/admin-wsl/Coq/mathlib4-0df444a/Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean:274)

$$
\sum_{v\mid\infty} m_v\log|\rho|_v+\sum_{v\in S}\log|\rho|_v=0.
$$

`Source_TripodCyclicVeluDescent.lean` の MCP-CI の葉モジュール検査 `ci-022337-967b971f` は終了コード 0 で通過した。`letI` のスタイル警告は 2 件である。 [MCP-CI の結果](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-022337-967b971f-result.json)

プロジェクトの検査と公理の監査に合格した。 [MCP-CI](../receipts/round-ci-022356-38c5d13c-result.json)
