# CanLift Galois closure, core criterion, and rigidity under extension of constants

The joint MCP-CI review checked all three declarations and exited with code 0. Lean reported only `propext`, `Classical.choice`, and `Quot.sound` for each declaration. [Review source](../ReviewCanLiftCoreCriterionAndExtendedCover.lean#L11) · [Joint review ci-022911-3f6a3a0a](../receipts/round-ci-022911-3f6a3a0a-result.json)

The source hashes below match the checked files. The reference revisions are orbicurve-cores `61616dcd77fbe45c083a8ebfa7cc80728f86e841` and Pi1 `ca7def953193f861a462aa0831eec8f0a31ff69f`.

| Lean module | Adapted source SHA-256 | Leaf check | Object build |
| --- | --- | --- | --- |
| `Source_ReferenceIutCanLiftUnramifiedClosure` | `dabed72ad1be90754a19e62ca835b8d11e333971887eebc819a5b4342853ffd5` | [ci-022883-f2794060](../receipts/round-ci-022883-f2794060-result.json) | [ci-022889-f4514897](../receipts/round-ci-022889-f4514897-result.json) |
| `Source_ReferenceIutCanLiftCoreCriterion` | `bfed0861f2498b018df1fa1a266c1d2a531694decfbe6f41c0a7db08cd01420b` | [ci-022893-e0f2c3ff](../receipts/round-ci-022893-e0f2c3ff-result.json) | [ci-022900-64b43f34](../receipts/round-ci-022900-64b43f34-result.json) |
| `Source_ReferenceIutCanLiftExtendedCover` | `bdc6f3f8fa51c81881035d0f23bd38a6d2646f8ab0d45ef37608c7e8addfa582` | [ci-022890-ca7a0cb4](../receipts/round-ci-022890-ca7a0cb4-result.json) | [ci-022894-6e421982](../receipts/round-ci-022894-6e421982-result.json) |

The leaf checks and object builds report proof-search suggestions. The two runs for the extended-cover module each also report one unused section variable warning.

## English

### Unramified Galois closure

Work over a field $k$ of characteristic zero. Let $\psi:Z\to Y$ be a cover of affine orbicurve presentations, with multiplicity $1$ at each closed point of $Z$. The theorem `exists_unramified_galoisClosure` constructs a cover $\gamma:T\to Z$ with ramification index $1$ at each closed point of $T$. It gives a group $G$ acting on the coordinate ring $A_T$. For the composite $A_Y\to A_Z\to A_T$, the action satisfies `IsGaloisGroup G Y.A T.A`. In particular, the fixed ring is the image of $A_Y$. [Adapted closure theorem](../../../../Solutions/Source_ReferenceIutCanLiftUnramifiedClosure.lean#L109)

The proof realizes $A_Y$ and $A_Z$ as integral closures of $k[t]$ in fields $F\subseteq L$ inside one algebraic closure of $k(t)$. Take the Galois closure $M$ of $L/F$ inside the normal closure of $L/k(t)$. The cover identity gives $e(w/v)=m_Y(v)$ for each closed point $w$ over $v$. The index therefore depends only on $v$. The ramification lemma gives index $1$ from $M$ to $L$, and the action on the normalization in $M$ fixes precisely the image of $A_Y$. [Ramification lemma](../../../../Solutions/Source_ReferenceIutCanLiftGaloisRamification.lean#L202) · [Fixed ring](../../../../Solutions/Source_ReferenceIutCanLiftGaloisAction.lean#L118) · [Closure in the proof of Theorem G](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/U2/CoreMap.lean#L100)

### Core criterion

Let $\pi:X\to H$ be a cover over $k$ and assume that $X$ has multiplicity $1$ at all closed points. Assume also that for every cover $V\to X$, there is at most one cover $V\to H$. The theorem `isCoreOf_of_unique_covers` gives `IsCoreOf X H`. Thus $H$ shares a cover with $X$, and every $Y$ that shares a cover with $X$ has a unique cover to $H$. [Definition of core](../../../../Solutions/Source_ReferenceIutCanLiftPresentation.lean#L26) · [Adapted criterion](../../../../Solutions/Source_ReferenceIutCanLiftCoreCriterion.lean#L74) · [Pi1 criterion](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/CoreCriterion.lean#L384)

Take a common cover $Z$ with $\varphi:Z\to X$ and $\psi:Z\to Y$. Multiplicity $1$ on $X$ gives multiplicity $1$ on $Z$, so the closure theorem applies to $\psi$. For its cover $T\to Z$, every element of $G$ gives a self-cover of $T$ over $k$. Composing with such a self-cover gives another cover $T\to H$. Uniqueness forces the two covers to agree, so the image of $A_H$ in $A_T$ is fixed by $G$. [Fixed-image argument](../../../../Solutions/Source_ReferenceIutCanLiftCoreCriterion.lean#L50)

The fixed ring property places this image in the image of $A_Y$. Injectivity of $A_Z\to A_T$ gives the factorization of $A_H\to A_Z$ through $A_Y$. The proof uses `Cover.descend` to make the resulting map a cover $Y\to H$. Two such covers agree after composition with $\psi$, so injectivity of $A_Y\to A_Z$ gives uniqueness. [Factorization and descent](../../../../Solutions/Source_ReferenceIutCanLiftCoreCriterion.lean#L81)

### Rigidity under extension of constants

Let $k\to K\to\Omega$ be a field tower in characteristic zero with $\Omega$ algebraically closed. Let $t\in\Omega$ be transcendental over $K$ and $y^2+by=c$ with $b,c\in k(t)$. The theorem `quadraticCoverRigidity_of_constantExtension` takes `QuadraticCoverRigidity K t y` and gives `QuadraticCoverRigidity k t y`. Take any finite $F/k(t)$ in $\Omega$ that contains $k(t)(y)$. Let $A_F$ be the integral closure of $k[t]$ in $F$. Assume $A_F$ is unramified over the integral closure of $k[t]$ in $k(t)(y)$. Rigidity says that an injective integral $k$-algebra map $g:k[t]\to A_F$ equals the canonical inclusion if each ramification index equals the sign-quotient multiplicity at the contracted point. [Rigidity predicate](../../../../Solutions/Source_ReferenceIutCanLiftDescendedCover.lean#L28) · [Adapted descent theorem](../../../../Solutions/Source_ReferenceIutCanLiftExtendedCover.lean#L144) · [Pi1 descent theorem](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L658)

For such an $F$, put $L=K(t)(F)$ inside $\Omega$. Extension of constants preserves the unramified condition over $K(t)(y)$. Put $s=g(t)$ in $\Omega$. The normalization makes $s$ integral over $k[t]$, and integrality of $g$ makes $t$ integral over $k[s]$. The proof uses this to construct the map over $K$ from the same parameter $s$. [Unramified extension](../../../../Solutions/Source_ReferenceIutCanLiftExtendedCover.lean#L84) · [Choice of parameter](../../../../Solutions/Source_ReferenceIutCanLiftExtendedCover.lean#L157)

Changing parameters from $t$ to $s$ puts the ramification identity in the form for extension of constants. Sign-quotient multiplicity is preserved at a closed point whose contraction is nonzero. It is $1$ when the contraction is zero. The extended map therefore satisfies the same cover identity over $K$. Applying rigidity over $K$ and evaluating at the polynomial generator gives $s=t$, so $g$ is the canonical inclusion. [Ramification transport](../../../../Solutions/Source_ReferenceIutCanLiftExtendedCover.lean#L99) · [Pi1 multiplicity comparison](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/HemiTY.lean#L212) · [Comparison of generator images](../../../../Solutions/Source_ReferenceIutCanLiftExtendedCover.lean#L173)

## 中文

### 非分歧伽罗瓦闭包

设 $k$ 为特征零域，$\psi:Z\to Y$ 为仿射轨形曲线表示之间的覆盖，且 $Z$ 的每个闭点重数为 $1$。定理 `exists_unramified_galoisClosure` 构造覆盖 $\gamma:T\to Z$，使 $T$ 每个闭点的分歧指数为 $1$。同时给出作用于坐标环 $A_T$ 的群 $G$。对于复合 $A_Y\to A_Z\to A_T$，该作用满足 `IsGaloisGroup G Y.A T.A`，特别地，不变子环为 $A_Y$ 的像。 [适配闭包定理](../../../../Solutions/Source_ReferenceIutCanLiftUnramifiedClosure.lean#L109)

证明将 $A_Y$ 和 $A_Z$ 实现为 $k[t]$ 在域 $F\subseteq L$ 中的整闭包，两个域位于 $k(t)$ 的同一代数闭包内。在 $L/k(t)$ 的正规闭包中取 $L/F$ 的伽罗瓦闭包 $M$。对 $v$ 上方的每个闭点 $w$，覆盖等式给出 $e(w/v)=m_Y(v)$，因而分歧指数只依赖于 $v$。分歧引理给出 $M$ 在 $L$ 上的分歧指数为 $1$，而在 $M$ 中的整闭包上的群作用恰以 $A_Y$ 的像为不变子环。 [分歧引理](../../../../Solutions/Source_ReferenceIutCanLiftGaloisRamification.lean#L202) · [不变子环](../../../../Solutions/Source_ReferenceIutCanLiftGaloisAction.lean#L118) · [定理 G 证明中的闭包](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/U2/CoreMap.lean#L100)

### 核心判据

设 $\pi:X\to H$ 是 $k$ 上的覆盖，$X$ 的每个闭点重数为 $1$。另假设对每个覆盖 $V\to X$，至多有一个覆盖 $V\to H$。定理 `isCoreOf_of_unique_covers` 给出 `IsCoreOf X H`。也就是 $H$ 和 $X$ 有公共覆盖，而且每个与 $X$ 有公共覆盖的 $Y$ 都有唯一的覆盖 $Y\to H$。 [核心定义](../../../../Solutions/Source_ReferenceIutCanLiftPresentation.lean#L26) · [适配判据](../../../../Solutions/Source_ReferenceIutCanLiftCoreCriterion.lean#L74) · [Pi1 判据](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/CoreCriterion.lean#L384)

取公共覆盖 $Z$，覆盖映射为 $\varphi:Z\to X$ 与 $\psi:Z\to Y$。由 $X$ 的重数为 $1$ 得到 $Z$ 的重数为 $1$，故可对 $\psi$ 应用闭包定理。对所得的覆盖 $T\to Z$，$G$ 的每个元素都给出 $k$ 上 $T$ 的一个自覆盖。将它与 $T\to H$ 复合后仍为覆盖，由唯一性知两个覆盖相同，故 $A_H$ 在 $A_T$ 中的像被 $G$ 固定。 [像的不变性](../../../../Solutions/Source_ReferenceIutCanLiftCoreCriterion.lean#L50)

由不变子环的刻画，该像包含于 $A_Y$ 的像。利用 $A_Z\to A_T$ 的单射性，得到 $A_H\to A_Z$ 经 $A_Y$ 分解。证明用 `Cover.descend` 将所得映射做成覆盖 $Y\to H$。任意两个这样的覆盖与 $\psi$ 复合后相同，再由 $A_Y\to A_Z$ 的单射性得到唯一性。 [分解与下降](../../../../Solutions/Source_ReferenceIutCanLiftCoreCriterion.lean#L81)

### 常数域扩张下的刚性

设 $k\to K\to\Omega$ 为特征零域塔，$\Omega$ 为代数闭域。设 $t\in\Omega$ 在 $K$ 上超越，且 $y^2+by=c$，其中 $b,c\in k(t)$。定理 `quadraticCoverRigidity_of_constantExtension` 从 `QuadraticCoverRigidity K t y` 推出 `QuadraticCoverRigidity k t y`。取 $\Omega$ 内包含 $k(t)(y)$ 的任一有限扩张 $F/k(t)$。设 $A_F$ 是 $k[t]$ 在 $F$ 中的整闭包，并假设 $A_F$ 在 $k[t]$ 于 $k(t)(y)$ 中的整闭包上非分歧。刚性要求单射整 $k$-代数同态 $g:k[t]\to A_F$ 在每个闭点的分歧指数等于收缩点的符号商重数时，$g$ 为规范包含。 [刚性谓词](../../../../Solutions/Source_ReferenceIutCanLiftDescendedCover.lean#L28) · [适配下降定理](../../../../Solutions/Source_ReferenceIutCanLiftExtendedCover.lean#L144) · [Pi1 下降定理](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L658)

对这样的 $F$，在 $\Omega$ 中取 $L=K(t)(F)$。扩张常数域保留了在 $K(t)(y)$ 上的非分歧条件。取 $s=g(t)\in\Omega$。正规化给出 $s$ 在 $k[t]$ 上整，$g$ 的整性给出 $t$ 在 $k[s]$ 上整。用这些条件和同一个参数 $s$ 构造 $K$ 上的映射。 [非分歧条件的扩张](../../../../Solutions/Source_ReferenceIutCanLiftExtendedCover.lean#L84) · [参数的选择](../../../../Solutions/Source_ReferenceIutCanLiftExtendedCover.lean#L157)

将参数从 $t$ 换为 $s$ 后，分歧等式成为可沿常数域扩张搬运的形式。对收缩非零的闭点，符号商的重数保持相同。收缩为零时，符号商的重数为 $1$。因此扩张后的映射在 $K$ 上满足同一覆盖等式。应用 $K$ 上的刚性并在多项式生成元处取值，得到 $s=t$，所以 $g$ 是规范包含。 [分歧的搬运](../../../../Solutions/Source_ReferenceIutCanLiftExtendedCover.lean#L99) · [Pi1 重数比较](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/HemiTY.lean#L212) · [生成元像的比较](../../../../Solutions/Source_ReferenceIutCanLiftExtendedCover.lean#L173)

## 日本語

### 不分岐 Galois 閉包

$k$ を標数零の体とし、$\psi:Z\to Y$ をアフィンオービ曲線の表示の間の被覆とする。$Z$ のすべての閉点で重複度を $1$ と仮定する。定理 `exists_unramified_galoisClosure` は、$T$ の各閉点で分岐指数が $1$ となる被覆 $\gamma:T\to Z$ を構成する。また、座標環 $A_T$ に作用する群 $G$ を与える。合成 $A_Y\to A_Z\to A_T$ に対し、この作用は `IsGaloisGroup G Y.A T.A` を満たす。特に、不変部分環は $A_Y$ の像である。 [適応版の閉包定理](../../../../Solutions/Source_ReferenceIutCanLiftUnramifiedClosure.lean#L109)

証明は $A_Y$ と $A_Z$ を、$k(t)$ の同じ代数閉包の中にある体 $F\subseteq L$ での $k[t]$ の整閉包として実現する。$L/k(t)$ の正規閉包の中で $L/F$ の Galois 閉包 $M$ を取る。$v$ の上にある各閉点 $w$ に対して、被覆の等式から $e(w/v)=m_Y(v)$ を得る。したがって分岐指数は $v$ だけで決まる。分岐補題により $M$ の $L$ 上での分岐指数は $1$ であり、$M$ での整閉包における群作用の不変部分環は $A_Y$ の像に等しい。 [分岐補題](../../../../Solutions/Source_ReferenceIutCanLiftGaloisRamification.lean#L202) · [不変部分環](../../../../Solutions/Source_ReferenceIutCanLiftGaloisAction.lean#L118) · [定理 G の証明での閉包](https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/U2/CoreMap.lean#L100)

### コアの判定条件

$\pi:X\to H$ を $k$ 上の被覆とし、$X$ のすべての閉点で重複度を $1$ と仮定する。さらに、各被覆 $V\to X$ に対し、被覆 $V\to H$ が高々一つあると仮定する。定理 `isCoreOf_of_unique_covers` は `IsCoreOf X H` を与える。すなわち $H$ は $X$ と共通の被覆を持ち、$X$ と共通の被覆を持つ任意の $Y$ から $H$ への被覆が一意に存在する。 [コアの定義](../../../../Solutions/Source_ReferenceIutCanLiftPresentation.lean#L26) · [適応版の判定条件](../../../../Solutions/Source_ReferenceIutCanLiftCoreCriterion.lean#L74) · [Pi1 の判定条件](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/CoreCriterion.lean#L384)

共通の被覆 $Z$ とその被覆写像 $\varphi:Z\to X$、$\psi:Z\to Y$ を取る。$X$ での重複度が $1$ なので $Z$ での重複度も $1$ となり、$\psi$ に閉包定理を適用できる。得られた被覆 $T\to Z$ に対し、$G$ の各元は $k$ 上の $T$ の自己被覆を与える。これを $T\to H$ と合成しても被覆となる。一意性により二つの被覆は一致するため、$A_H$ の $A_T$ での像は $G$ に固定される。 [像の不変性](../../../../Solutions/Source_ReferenceIutCanLiftCoreCriterion.lean#L50)

不変部分環の性質から、この像は $A_Y$ の像に含まれる。$A_Z\to A_T$ の単射性により、$A_H\to A_Z$ は $A_Y$ を経由する。証明は `Cover.descend` を使って、得られた写像を被覆 $Y\to H$ にする。二つの被覆は $\psi$ と合成すると一致するので、$A_Y\to A_Z$ の単射性から一意性を得る。 [分解と降下](../../../../Solutions/Source_ReferenceIutCanLiftCoreCriterion.lean#L81)

### 定数体拡大に沿う剛性

$k\to K\to\Omega$ を標数零の体の塔とし、$\Omega$ を代数閉体とする。$t\in\Omega$ は $K$ 上で超越的で、$b,c\in k(t)$ および $y^2+by=c$ を仮定する。定理 `quadraticCoverRigidity_of_constantExtension` は `QuadraticCoverRigidity K t y` から `QuadraticCoverRigidity k t y` を導く。$\Omega$ 内で $k(t)(y)$ を含む任意の有限拡大 $F/k(t)$ を取る。$A_F$ を $F$ における $k[t]$ の整閉包とし、$k(t)(y)$ における $k[t]$ の整閉包の上で $A_F$ が不分岐であると仮定する。剛性は、単射で整な $k$-代数準同型 $g:k[t]\to A_F$ の各閉点での分岐指数が縮約した点での符号商の重複度に等しければ、$g$ が標準的な包含写像となることをいう。 [剛性の述語](../../../../Solutions/Source_ReferenceIutCanLiftDescendedCover.lean#L28) · [適応版の降下定理](../../../../Solutions/Source_ReferenceIutCanLiftExtendedCover.lean#L144) · [Pi1 の降下定理](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/Lefschetz.lean#L658)

このような $F$ について、$\Omega$ の中で $L=K(t)(F)$ とおく。定数体の拡大により $K(t)(y)$ の上での不分岐条件が保たれる。$s=g(t)$ を $\Omega$ の元とする。正規化の定義から $s$ は $k[t]$ 上で整であり、$g$ の整性から $t$ は $k[s]$ 上で整である。この二つの条件と同じパラメータ $s$ を用いて、$K$ 上の写像を構成する。 [不分岐条件の移送](../../../../Solutions/Source_ReferenceIutCanLiftExtendedCover.lean#L84) · [パラメータの選択](../../../../Solutions/Source_ReferenceIutCanLiftExtendedCover.lean#L157)

パラメータを $t$ から $s$ に変えると、分岐の等式は定数体の拡大で移送できる形になる。縮約が零でない閉点では、符号商の重複度は保たれる。縮約が零なら重複度は $1$ となる。したがって拡大した写像は $K$ 上でも同じ被覆の等式を満たす。$K$ 上の剛性を適用して多項式の生成元で評価すると $s=t$ となり、$g$ は標準的な包含写像となる。 [分岐の移送](../../../../Solutions/Source_ReferenceIutCanLiftExtendedCover.lean#L99) · [Pi1 の重複度の比較](https://github.com/lana-agents/pi1/blob/ca7def953193f861a462aa0831eec8f0a31ff69f/Pi1/Orbicurve/HemiTY.lean#L212) · [生成元の像の比較](../../../../Solutions/Source_ReferenceIutCanLiftExtendedCover.lean#L173)
