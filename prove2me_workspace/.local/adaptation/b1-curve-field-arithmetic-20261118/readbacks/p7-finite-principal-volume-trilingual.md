# Finite principal regions and their log-volume

## English

Let $K$ be a number field, $p$ a fixed rational prime, and $(w_i)_{i\in I}$ a tuple of finite places of $K$, indexed by a finite set $I$, all of residue characteristic $p$. Write $K_{w_i}$ for the completion at $w_i$, $T=\bigotimes_{i\in I}K_{w_i}$ for their tensor product over $\mathbb Q_p$, and $\mathcal O_T$ for the integral closure of $\mathbb Z_p$ in $T$. Fix $j\in I$, set $w=w_j$, and take $x\in K_w^\times$. Let $a\in T$ be the pure tensor with $x$ in the $j$-th factor and $1$ in every other factor. Set $S=a\mathcal O_T=\{ay:y\in\mathcal O_T\}$.

### Orbit (`finiteIndAut_iUnion_incl_smul_integral`)

Let $G$ be the finite family of tensor automorphisms $\bigotimes_i\sigma_i$ obtained by choosing a $\mathbb Q_p$-algebra automorphism $\sigma_i$ of each $K_{w_i}$. Then $\bigcup_{\varphi\in G}\varphi(S)=S$.

### Log-volume (`finiteComponentVol_incl_smul_integral`)

For an additive Haar measure $\mu$ on $T$, the degree-normalized log-volume of $S$ is
$$
\frac{\log\!\big(\mu(S)/\mu(\mathcal O_T)\big)}{\dim_{\mathbb Q_p}T}
=\frac{\log\|x\|_w}{[K_w:\mathbb Q_p]}.
$$
Both Haar masses in the ratio are positive and finite. Here $[K_w:\mathbb Q_p]=e_w f_w$, where $e_w$ is the ramification index and $f_w$ the residue degree. The completion norm satisfies $\|\pi_w\|_w=p^{-f_w}$ for a uniformizer $\pi_w$.

## 中文

设 $K$ 为数域，$p$ 为固定的有理素数，$(w_i)_{i\in I}$ 为由有限集 $I$ 索引的一组有限位，各 $w_i$ 的剩余特征均为 $p$。令 $K_{w_i}$ 为 $K$ 在 $w_i$ 处的完备化，$T=\bigotimes_{i\in I}K_{w_i}$ 为这些完备化在 $\mathbb Q_p$ 上的张量积，$\mathcal O_T$ 为 $\mathbb Z_p$ 在 $T$ 中的整闭包。选取 $j\in I$，令 $w=w_j$，并取 $x\in K_w^\times$。令 $a\in T$ 为第 $j$ 个因子取 $x$、其余因子均取 $1$ 的纯张量，设 $S=a\mathcal O_T=\{ay:y\in\mathcal O_T\}$。

### 轨道（`finiteIndAut_iUnion_incl_smul_integral`）

在每个 $K_{w_i}$ 上各选一个 $\mathbb Q_p$-代数自同构 $\sigma_i$，所得张量积自同构 $\bigotimes_i\sigma_i$ 构成有限族 $G$。则 $\bigcup_{\varphi\in G}\varphi(S)=S$。

### 对数体积（`finiteComponentVol_incl_smul_integral`）

设 $\mu$ 为 $T$ 上的加法 Haar 测度，则 $S$ 按次数归一化的对数体积为
$$
\frac{\log\!\big(\mu(S)/\mu(\mathcal O_T)\big)}{\dim_{\mathbb Q_p}T}
=\frac{\log\|x\|_w}{[K_w:\mathbb Q_p]}.
$$
比值中的两个 Haar 测度值均为有限正数。这里 $[K_w:\mathbb Q_p]=e_w f_w$，$e_w$ 为分歧指数，$f_w$ 为剩余次数。完备化上的范数满足 $\|\pi_w\|_w=p^{-f_w}$，其中 $\pi_w$ 为素元。

## 日本語

$K$ を代数体、$p$ を固定した有理素数とする。有限集合 $I$ で添字付けられた $K$ の有限素点の組 $(w_i)_{i\in I}$ をとり、各 $w_i$ の剰余標数が $p$ であると仮定する。$K_{w_i}$ を $w_i$ における完備化、$T=\bigotimes_{i\in I}K_{w_i}$ をそれらの $\mathbb Q_p$ 上のテンソル積、$\mathcal O_T$ を $T$ における $\mathbb Z_p$ の整閉包とする。$j\in I$ を選び、$w=w_j$ とおき、$x\in K_w^\times$ をとる。第 $j$ 因子が $x$、他の因子がすべて $1$ である純テンソルを $a\in T$ とし、$S=a\mathcal O_T=\{ay:y\in\mathcal O_T\}$ とおく。

### 軌道（`finiteIndAut_iUnion_incl_smul_integral`）

各 $K_{w_i}$ の $\mathbb Q_p$-代数自己同型 $\sigma_i$ から得られるテンソル積の自己同型 $\bigotimes_i\sigma_i$ 全体を有限族 $G$ とすると、$\bigcup_{\varphi\in G}\varphi(S)=S$ が成り立つ。

### 対数体積（`finiteComponentVol_incl_smul_integral`）

$\mu$ を $T$ の加法群上の Haar 測度とすると、次数で正規化した $S$ の対数体積は
$$
\frac{\log\!\big(\mu(S)/\mu(\mathcal O_T)\big)}{\dim_{\mathbb Q_p}T}
=\frac{\log\|x\|_w}{[K_w:\mathbb Q_p]}.
$$
比に現れる二つの Haar 測度の値はいずれも正かつ有限である。ここで $[K_w:\mathbb Q_p]=e_w f_w$、$e_w$ は分岐指数、$f_w$ は剰余次数である。完備化のノルムは、素元 $\pi_w$ に対して $\|\pi_w\|_w=p^{-f_w}$ を満たす。

[Orbit theorem](../../../../Solutions/Source_ReferenceIutConcreteLocalFinitePrincipalOrbit.lean#L107) · [Volume theorem](../../../../Solutions/Source_ReferenceIutConcreteLocalFinitePrincipalVolume.lean#L91) · [Project and axiom review](../receipts/round-ci-023522-f4c700f6-result.json)
