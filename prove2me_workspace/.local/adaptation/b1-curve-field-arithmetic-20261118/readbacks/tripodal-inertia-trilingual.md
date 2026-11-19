# Inertia over the tripodal field

## English

Fix `P : CurveProviders` and `x : Pt`. Let $E_\lambda/F$ be `P.curve x` and let $F_{\mathrm{tpd}}=\mathbb Q(\lambda)$. Write $a,b,i\in F$ for the chosen roots with $a^2=\lambda$, $b^2=1-\lambda$, and $i^2=-1$. Let $w$ be a finite place of $F$, $\nu_w$ its multiplicative valuation, and $I$ its inertia group for $F/F_{\mathrm{tpd}}$. The subgroup `inertiaPlus` is $I^+=\{\sigma\in I\mid\sigma(a)=a,\ \sigma(b)=b\}$. [Chosen roots](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodUnramifiedBase.lean:66) · [Inertia subgroup](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:100)

### The representations on 3- and 5-torsion

The field $F$ contains the coordinates of all geometric $n$-torsion points for $n=3,5$. Base change identifies $E_\lambda(F)[n]$ with $E_\lambda(\overline{\mathbb Q})[n]$. The basis `basisF` identifies this group with $\mathbb F_n^2$. In that basis, `repF` gives

$$
\rho_n\colon\operatorname{Gal}(F/F_{\mathrm{tpd}})\longrightarrow\mathrm{GL}_2(\mathbb F_n),\qquad n\in\{3,5\}.
$$

The lemma `mem_repF_ker_iff` identifies the kernel with the automorphisms that fix every $n$-torsion point. Such an automorphism fixes each affine coordinate of those points. [3-torsion coordinates](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodUnramifiedBase.lean:75) · [5-torsion coordinates](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodUnramifiedBase.lean:78) · [Torsion equivalence](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdTorsionRep.lean:97) · [Basis](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdTorsionRep.lean:118) · [Representation](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdTorsionRep.lean:182) · [Kernel](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdTorsionRep.lean:189) · [Fixed coordinates](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdTorsionRep.lean:210)

### Bounding the order of $I^+$

Assume the residue characteristic at $w$ is outside $\{2,3,5\}$. Assume $\nu_w(\lambda)\ne1$ or $\nu_w(\lambda-1)\ne1$. If $s^2$ belongs to $F_{\mathrm{tpd}}$ and is a unit at $w$, then $I$ fixes $s$. Inertia gives $\nu_w(\sigma s-s)<1$. The sign $\sigma s=-s$ would give $\nu_w(\sigma s-s)=\nu_w(2s)=1$, a contradiction. This proves that $I$ fixes $i$. Since $I^+$ also fixes $a$, `galF_pow_eq_self_of_mem_inertiaPlus` applies the Legendre inertia theorem with $n=3,5$. The valuation of each $n$ is one. Thus $\rho_n(\sigma)^n=1$ for every $\sigma\in I^+$ and each $n\in\{3,5\}$. [Square root rigidity](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerTorsionRigid.lean:38) · [Inertia fixes $i$](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:145) · [Action of $\sigma^n$](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:162) · [Powers in the representations](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:185)

On $I^+$ the two representations are jointly faithful. An element in both kernels fixes all 3- and 5-torsion coordinates. Together with $i,a,b$, these coordinates generate $F$ over $F_{\mathrm{tpd}}$. The orders of $\mathrm{GL}_2(\mathbb F_3)$ and $\mathrm{GL}_2(\mathbb F_5)$ are $3\cdot16$ and $5\cdot96$, respectively. The exponent condition at $3$ and the finite subgroup bound give $|\rho_3(I^+)|\le3$. Joint faithfulness makes $\rho_5$ injective on $I^+\cap\ker\rho_3$. The exponent condition at $5$ bounds the image of this subgroup under $\rho_5$ by $5$. The index formula now gives `card_inertiaPlus_le`.

$$
|I^+|=|I^+\cap\ker\rho_3|\cdot|\rho_3(I^+)|\le5\cdot3=15.
$$

[Field generators](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodUnramifiedBase.lean:128) · [Joint faithfulness](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:197) · [Finite subgroup bound](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodBadRamIdx.lean:41) · [Group order calculation](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:215) · [Lean bound](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:251) · [Reference proof](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/TpdInertia.lean:192)

### Bounding the ramification indices

Let $u$ be the place of $F_{\mathrm{tpd}}$ below $w$ and assume $u\in\texttt{badT P x}$. The condition on $\nu_w(\lambda)$ and $\nu_w(\lambda-1)$ follows by transport from $u$. The sign homomorphism on a chosen root $s$ has value $+1$ precisely when $\sigma s=s$. In each case below, its kernel on $I$ is $I^+$. [Valuation transport](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodBadRamIdx.lean:79) · [Sign homomorphism](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:33) · [Index bound](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:116)

| Valuation at $w$ | Fixed by all of $I$ | Root used for the sign |
| --- | --- | --- |
| $\nu_w(\lambda)<1$ | $b$ | $a$ |
| $\nu_w(\lambda)=1$ | $a$ | $b$ |
| $1<\nu_w(\lambda)$ | $b/a$ | $a$ |

In the three cases, the square of the fixed element is a unit at $w$. In the last case, fixing $a$ and $b/a$ also fixes $b$. Hence $[I:I^+]\le2$. Since $F/F_{\mathrm{tpd}}$ is Galois, $e(w/u)=|I|\le30$ by `relRamIdx_tpd_le_thirty`. [Galois extension](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodUnramifiedBase.lean:274) · [Ramification and inertia](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerInertia.lean:71) · [Lean bound](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:281) · [Reference proof](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/TpdInertia.lean:276)

Take an odd prime $\ell$ and any `R : (P.curve x).ModEllRepData ℓ` with torsion field $K$. Let $v$ be a finite place of $K$ above $w$ and $u$. Suppose its residue characteristic is outside $\{2,3,5,\ell\}$. The residue characteristic agrees at $v$ and $w$. Above $u\in\texttt{badT P x}$ the bound for $F/F_{\mathrm{tpd}}$ applies. Above every other $u$, the unramified case gives $e(w/u)=1$. The bound $e(v/w)\le\ell$ for $K/F$ then gives `relRamIdx_le_thirty_mul`.

$$
e(v/u)=e(v/w)e(w/u)\le30\ell.
$$

[Unramified case](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodUnramifiedBase.lean:301) · [Torsion-field bound](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodBadRamIdx.lean:131) · [Tower bound](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:339) · [Reference proof](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/TowerFacts.lean:46)

MCP-CI leaf check `ci-022222-f3a919cf` passed on the cited `Source_TripodTpdInertia.lean` input with exit code 0 and two `haveI` style warnings. Project and axiom review passed. [MCP-CI](../receipts/round-ci-022255-2c5b55c1-result.json) [MCP-CI receipt](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-022222-f3a919cf-result.json)

## 中文

固定 `P : CurveProviders` 和 `x : Pt`。记 `P.curve x` 为 $E_\lambda/F$，其三足域为 $F_{\mathrm{tpd}}=\mathbb Q(\lambda)$。记 $a,b,i\in F$ 为选定的平方根，满足 $a^2=\lambda$、$b^2=1-\lambda$、$i^2=-1$。设 $w$ 为 $F$ 的有限位，$\nu_w$ 为其乘法赋值，$I$ 为 $F/F_{\mathrm{tpd}}$ 在 $w$ 处的惯性群。`inertiaPlus` 定义子群 $I^+=\{\sigma\in I\mid\sigma(a)=a,\ \sigma(b)=b\}$。 [选定的平方根](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodUnramifiedBase.lean:66) · [惯性子群](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:100)

### 3 挠与 5 挠表示

对 $n=3,5$，几何 $n$ 挠点的坐标均在 $F$ 中。基变换给出 $E_\lambda(F)[n]$ 与 $E_\lambda(\overline{\mathbb Q})[n]$ 的同构。`basisF` 将该群与 $\mathbb F_n^2$ 等同。在这组基下，`repF` 给出

$$
\rho_n\colon\operatorname{Gal}(F/F_{\mathrm{tpd}})\longrightarrow\mathrm{GL}_2(\mathbb F_n),\qquad n\in\{3,5\}.
$$

`mem_repF_ker_iff` 说明，表示的核由固定每个 $n$ 挠点的自同构组成。这些自同构也固定这些点的每个仿射坐标。 [3 挠点坐标](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodUnramifiedBase.lean:75) · [5 挠点坐标](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodUnramifiedBase.lean:78) · [挠点同构](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdTorsionRep.lean:97) · [基](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdTorsionRep.lean:118) · [表示](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdTorsionRep.lean:182) · [表示的核](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdTorsionRep.lean:189) · [坐标固定性](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdTorsionRep.lean:210)

### $I^+$ 的阶

设 $w$ 处的剩余特征避开 $\{2,3,5\}$，并假设 $\nu_w(\lambda)\ne1$ 或 $\nu_w(\lambda-1)\ne1$。若 $s^2$ 属于 $F_{\mathrm{tpd}}$ 且在 $w$ 处为单位，则 $I$ 固定 $s$。惯性条件给出 $\nu_w(\sigma s-s)<1$，而 $\sigma s=-s$ 会给出 $\nu_w(\sigma s-s)=\nu_w(2s)=1$。由此 $I$ 固定 $i$。$I^+$ 也固定 $a$，故 `galF_pow_eq_self_of_mem_inertiaPlus` 可对 $n=3,5$ 应用 Legendre 曲线的惯性作用定理，两者在 $w$ 处的赋值均为一。因此对每个 $\sigma\in I^+$ 和 $n\in\{3,5\}$，都有 $\rho_n(\sigma)^n=1$。 [平方根刚性](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerTorsionRigid.lean:38) · [惯性固定 $i$](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:145) · [$\sigma^n$ 的作用](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:162) · [表示中的幂](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:185)

两个表示在 $I^+$ 上的乘积表示是忠实的。两个核的交中的元素固定全部 3 挠和 5 挠点的坐标。这些坐标与 $i,a,b$ 一起在 $F_{\mathrm{tpd}}$ 上生成 $F$。$\mathrm{GL}_2(\mathbb F_3)$ 和 $\mathrm{GL}_2(\mathbb F_5)$ 的阶分别为 $3\cdot16$ 和 $5\cdot96$。由 3 挠表示的幂条件及有限子群的阶数界，得到 $|\rho_3(I^+)|\le3$。乘积表示的忠实性给出 $\rho_5$ 在 $I^+\cap\ker\rho_3$ 上单射。再由 5 挠表示的幂条件，这个子群在 $\rho_5$ 下的像的阶至多为 $5$。由指数公式得到 `card_inertiaPlus_le`。

$$
|I^+|=|I^+\cap\ker\rho_3|\cdot|\rho_3(I^+)|\le5\cdot3=15.
$$

[域的生成元](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodUnramifiedBase.lean:128) · [乘积表示的忠实性](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:197) · [有限子群的阶数界](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodBadRamIdx.lean:41) · [群阶计算](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:215) · [Lean 定理](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:251) · [参考证明](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/TpdInertia.lean:192)

### 相对分歧指数的界

设 $u$ 为 $w$ 下方的三足域位，且 $u\in\texttt{badT P x}$。把 $u$ 处的条件传到 $w$，得到关于 $\nu_w(\lambda)$ 与 $\nu_w(\lambda-1)$ 的条件。所选平方根 $s$ 的符号同态取值为 $+1$ 当且仅当 $\sigma s=s$。在以下各情形中，该同态在 $I$ 上的核为 $I^+$。 [赋值条件的传递](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodBadRamIdx.lean:79) · [符号同态](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:33) · [指数界](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:116)

| $w$ 处的赋值条件 | 整个 $I$ 固定的元素 | 取符号的平方根 |
| --- | --- | --- |
| $\nu_w(\lambda)<1$ | $b$ | $a$ |
| $\nu_w(\lambda)=1$ | $a$ | $b$ |
| $1<\nu_w(\lambda)$ | $b/a$ | $a$ |

在三种情形下，固定元素的平方在 $w$ 处为单位。最后一种情形中，固定 $a$ 与 $b/a$ 也就固定 $b$。故 $[I:I^+]\le2$。由 $F/F_{\mathrm{tpd}}$ 为 Galois 扩张，`relRamIdx_tpd_le_thirty` 给出 $e(w/u)=|I|\le30$。 [Galois 扩张](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodUnramifiedBase.lean:274) · [分歧指数与惯性](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerInertia.lean:71) · [Lean 定理](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:281) · [参考证明](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/TpdInertia.lean:276)

取奇素数 $\ell$ 及任意 `R : (P.curve x).ModEllRepData ℓ`，记其挠点域为 $K$。设 $v$ 是 $K$ 中位于 $w$ 与 $u$ 上方的有限位，且剩余特征避开 $\{2,3,5,\ell\}$。$v$ 和 $w$ 的剩余特征相同。若 $u\in\texttt{badT P x}$，应用 $F/F_{\mathrm{tpd}}$ 的分歧界。其余 $u$ 处的不分歧定理给出 $e(w/u)=1$。再用 $K/F$ 的界 $e(v/w)\le\ell$ 得到 `relRamIdx_le_thirty_mul`。

$$
e(v/u)=e(v/w)e(w/u)\le30\ell.
$$

[不分歧情形](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodUnramifiedBase.lean:301) · [挠点域分歧界](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodBadRamIdx.lean:131) · [域塔分歧界](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:339) · [参考证明](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/TowerFacts.lean:46)

`Source_TripodTpdInertia.lean` 的 MCP-CI 叶检查 `ci-022222-f3a919cf` 通过，退出码为 0，有两条 `haveI` 风格警告。项目与公理审查通过。 [MCP-CI](../receipts/round-ci-022255-2c5b55c1-result.json) [MCP-CI 回执](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-022222-f3a919cf-result.json)

## 日本語

`P : CurveProviders` と `x : Pt` を固定する。`P.curve x` を $E_\lambda/F$ とし、その三脚体を $F_{\mathrm{tpd}}=\mathbb Q(\lambda)$ とする。選んだ平方根を $a,b,i\in F$ とし、$a^2=\lambda$、$b^2=1-\lambda$、$i^2=-1$ とする。$w$ を $F$ の有限素点、$\nu_w$ をその乗法的付値、$I$ を $F/F_{\mathrm{tpd}}$ の $w$ における惰性群とする。`inertiaPlus` は部分群 $I^+=\{\sigma\in I\mid\sigma(a)=a,\ \sigma(b)=b\}$ である。 [選んだ平方根](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodUnramifiedBase.lean:66) · [惰性部分群](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:100)

### 3-ねじれ点と 5-ねじれ点の表現

$n=3,5$ に対して、幾何的 $n$-ねじれ点の座標はすべて $F$ に属する。基底変換は $E_\lambda(F)[n]$ と $E_\lambda(\overline{\mathbb Q})[n]$ の間の同型を与える。`basisF` でこの群を $\mathbb F_n^2$ と同一視する。この基底で `repF` は次の表現を与える。

$$
\rho_n\colon\operatorname{Gal}(F/F_{\mathrm{tpd}})\longrightarrow\mathrm{GL}_2(\mathbb F_n),\qquad n\in\{3,5\}.
$$

`mem_repF_ker_iff` によれば、表現の核は各 $n$-ねじれ点を固定する自己同型からなる。そのような自己同型は各点のアフィン座標も固定する。 [3-ねじれ点の座標](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodUnramifiedBase.lean:75) · [5-ねじれ点の座標](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodUnramifiedBase.lean:78) · [ねじれ部分群の同型](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdTorsionRep.lean:97) · [基底](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdTorsionRep.lean:118) · [表現](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdTorsionRep.lean:182) · [核](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdTorsionRep.lean:189) · [座標の固定](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdTorsionRep.lean:210)

### $I^+$ の位数

$w$ の剰余標数が $\{2,3,5\}$ の外にあり、$\nu_w(\lambda)\ne1$ または $\nu_w(\lambda-1)\ne1$ と仮定する。$s^2$ が $F_{\mathrm{tpd}}$ に属し、$w$ における単元ならば、$I$ は $s$ を固定する。惰性の条件から $\nu_w(\sigma s-s)<1$ となるが、$\sigma s=-s$ ならば $\nu_w(\sigma s-s)=\nu_w(2s)=1$ となる。従って $I$ は $i$ を固定する。$I^+$ は $a$ も固定するため、`galF_pow_eq_self_of_mem_inertiaPlus` は $n=3,5$ に対して Legendre 曲線の惰性作用の定理を適用できる。どちらの $n$ も付値が 1 である。従って各 $\sigma\in I^+$ と $n\in\{3,5\}$ に対し $\rho_n(\sigma)^n=1$ となる。 [平方根の剛性](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerTorsionRigid.lean:38) · [$i$ の固定](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:145) · [$\sigma^n$ の作用](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:162) · [表現でのべき](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:185)

二つの表現の積は $I^+$ 上で忠実である。両方の核に属する元は 3-ねじれ点と 5-ねじれ点の座標をすべて固定する。これらの座標は $i,a,b$ とともに $F_{\mathrm{tpd}}$ 上で $F$ を生成する。$\mathrm{GL}_2(\mathbb F_3)$ と $\mathrm{GL}_2(\mathbb F_5)$ の位数はそれぞれ $3\cdot16$ と $5\cdot96$ である。3-ねじれ点の表現のべきの条件と有限部分群の位数の上界から $|\rho_3(I^+)|\le3$ を得る。積表現の忠実性により、$\rho_5$ は $I^+\cap\ker\rho_3$ 上で単射である。5-ねじれ点の表現のべきの条件から、この部分群の $\rho_5$ による像の位数は $5$ 以下となる。指数の公式から `card_inertiaPlus_le` が従う。

$$
|I^+|=|I^+\cap\ker\rho_3|\cdot|\rho_3(I^+)|\le5\cdot3=15.
$$

[体の生成元](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodUnramifiedBase.lean:128) · [積表現の忠実性](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:197) · [有限部分群の位数の上界](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodBadRamIdx.lean:41) · [群の位数の計算](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:215) · [Lean の定理](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:251) · [参照元の証明](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/TpdInertia.lean:192)

### 相対分岐指数の上界

$u$ を $w$ の下にある三脚体の素点とし、$u\in\texttt{badT P x}$ と仮定する。$u$ から $w$ への移行により $\nu_w(\lambda)$ と $\nu_w(\lambda-1)$ の条件を得る。選んだ平方根 $s$ の符号準同型が $+1$ となるのは $\sigma s=s$ のときである。以下の各場合で、この準同型の $I$ 上の核は $I^+$ である。 [付値条件の移行](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodBadRamIdx.lean:79) · [符号準同型](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:33) · [指数の上界](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:116)

| $w$ での付値条件 | $I$ 全体が固定する元 | 符号準同型に使う平方根 |
| --- | --- | --- |
| $\nu_w(\lambda)<1$ | $b$ | $a$ |
| $\nu_w(\lambda)=1$ | $a$ | $b$ |
| $1<\nu_w(\lambda)$ | $b/a$ | $a$ |

三つの場合に、固定される元の平方は $w$ で単元である。最後の場合、$a$ と $b/a$ を固定すれば $b$ も固定する。従って $[I:I^+]\le2$ となる。$F/F_{\mathrm{tpd}}$ は Galois 拡大なので、`relRamIdx_tpd_le_thirty` により $e(w/u)=|I|\le30$ となる。 [Galois 拡大](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodUnramifiedBase.lean:274) · [分岐指数と惰性群](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutTowerInertia.lean:71) · [Lean の定理](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:281) · [参照元の証明](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/TpdInertia.lean:276)

奇素数 $\ell$ と任意の `R : (P.curve x).ModEllRepData ℓ` を取り、そのねじれ点体を $K$ とする。$v$ を $w$ と $u$ の上にある $K$ の有限素点とし、剰余標数が $\{2,3,5,\ell\}$ の外にあると仮定する。$v$ と $w$ の剰余標数は一致する。$u\in\texttt{badT P x}$ ならば、$F/F_{\mathrm{tpd}}$ の上界を適用する。それ以外の $u$ では、不分岐性の定理から $e(w/u)=1$ となる。$K/F$ の上界 $e(v/w)\le\ell$ を使うと `relRamIdx_le_thirty_mul` が従う。

$$
e(v/u)=e(v/w)e(w/u)\le30\ell.
$$

[不分岐の場合](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodUnramifiedBase.lean:301) · [ねじれ点体の上界](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodBadRamIdx.lean:131) · [体の塔の上界](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodTpdInertia.lean:339) · [参照元の証明](/home/admin-wsl/Coq/abc/refer/iut/Iut/Tripod/TowerFacts.lean:46)

`Source_TripodTpdInertia.lean` の MCP-CI の葉モジュール検査 `ci-022222-f3a919cf` は終了コード 0 で通過した。`haveI` のスタイル警告が 2 件あった。プロジェクトの検査と公理の監査に合格した。 [MCP-CI](../receipts/round-ci-022255-2c5b55c1-result.json) [MCP-CI の結果](/home/admin-wsl/Coq/abc/prove2me_workspace/.local/adaptation/b1-curve-field-arithmetic-20261118/receipts/round-ci-022222-f3a919cf-result.json)
