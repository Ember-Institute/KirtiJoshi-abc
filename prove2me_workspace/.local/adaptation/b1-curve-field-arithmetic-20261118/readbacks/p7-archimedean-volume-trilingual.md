## English

### `archComponentVol_archLogShell`

Let $K$ be a field of universe level $u$ equipped with a number-field structure. Let $\iota$ be any finite index type in Lean's `Type 0` and let $c\colon\iota\to\operatorname{Place}(K)$ be any assignment of places of $K$. Write $V_c$ for the real tensor product of the archimedean factors indexed by $\iota$. The factor for $j$ is real or complex according to the infinite place selected by `archPlace` from $c(j)$. This selection uses the given place for an infinite input and an arbitrary infinite place for a finite input. [Place selection](../../../../Solutions/Source_ReferenceIutConcreteLocalPacket.lean#L209)

Set $m=|\iota|$ and $d_c=\dim_{\mathbb R}V_c>0$. Let $B_c$ be the closed unit ball of the projective tensor seminorm on $V_c$ and $\mu_c$ the additive Haar measure normalized by $\mu_c(B_c)=1$. The archimedean log-shell is $S_c=\pi^m B_c$ and has Haar measure $(\pi^m)^{d_c}$. Its normalized component log-volume, with $\log$ denoting the natural logarithm, is

$$
v_c(S_c)=\frac{\log \mu_c(S_c)}{d_c}=m\log\pi.
$$

If $\iota$ is empty, then $m=0$, the shell is $B_c$, and its normalized component log-volume is zero. [Statement](../../../../Solutions/Source_ReferenceIutConcreteLocalArchimedean.lean#L158) · [Normalization](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalArchimedeanTensorHaar.lean#L80)

### `exists_leastHull_infinite`

Let $K$ be a number field of universe level $u$ and $\iota$ a finite index type in Lean's `Type 0`. Take any place assignment $c$ on $\iota$. Let $V_c$ be the real tensor product of the real or complex factors at the places selected by `archPlace`. This function uses the given infinite place or a fixed chosen infinite place for a finite input. Let $B_c$ be the closed unit ball of the projective tensor seminorm on $V_c$. Let $\mu_c$ be the additive Haar measure with $\mu_c(B_c)=1$.

Suppose $U\subseteq V_c$ is nonempty and measurable, has compact closure, and satisfies $0<\mu_c(U)<\infty$. There is a real number $t>0$ such that $U\subseteq t B_c$. For every $t'>0$ with $U\subseteq t' B_c$, one has $t\le t'$. The proof takes $t$ to be the supremum of the projective tensor seminorm on $U$. [Lean statement](../../../../Solutions/Source_ReferenceIutConcreteLocalArchimedean.lean#L136) · [Definition of the radius](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalArchimedeanTensorRadialHull.lean#L80)

### `prop15`

Let $K$ be a number field of universe level $u$ and $\iota$ a finite index type in Lean's `Type 0`. Take any place assignment $c$ on $\iota$. For each $j$, let $F_j$ be the real or complex factor at the infinite place that `archPlace` selects from $c(j)$. The function uses the given infinite place or a fixed chosen infinite place for a finite input. Let $V_c=\bigotimes_{j\in\iota,\mathbb R} F_j$ and let $B_c$ be its closed projective tensor unit ball. The log-shell is $S_c=\pi^{|\iota|}B_c$.

Let $\varphi\colon V_c\to V_c$ belong to `archIndAut c`. This means that some family of real algebra automorphisms $\sigma_j$ of $F_j$ induces $\varphi$ on the tensor product. Then $\varphi(S_c)\subseteq\pi^{|\iota|}B_c$. For an empty index type, the scale is one. [Allowed maps](../../../../Solutions/Source_ReferenceIutConcreteLocalArchimedean.lean#L175) · [Lean statement](../../../../Solutions/Source_ReferenceIutConcreteLocalArchimedean.lean#L188)

### `ThetaLocalData.packetVol_thetaHull_infinite`

At any universe level, take an anabelian geometry, a tempered geometry over it, initial $\Theta$-data $D$ for these geometries, and $\Theta$-local data for $D$ in the concrete local theory attached to its parameter $K_t$. Let $\ell$ be the natural-number parameter of $D$ and put $n=\lfloor\max(\ell-1,0)/2\rfloor$. For every zero-based capsule index $0\le i<n$ in the standard procession, let $L_i=\{0,\ldots,i+1\}$ be its label set and $m_i=|L_i|=i+2$. For $n=0$ the index range is empty. At the infinite place, let $F_\infty$ be the finite fiber supplied by the local theory and $w_\infty$ its real weights, with $\sum_{a\in F_\infty}w_\infty(a)=1$. The components of the packet are indexed by the functions $c\colon L_i\to F_\infty$. The infinite-place region $H_i$ of the $\Theta$-hull for capsule $i$ is the product of their log-shells $S_c$, each obtained by scaling the component's projective unit ball by $\pi^{m_i}$. If $d_c$ is the real dimension of the component tensor space, the normalized Haar measure of $S_c$ is $(\pi^{m_i})^{d_c}$ and its normalized component log-volume $v_c(S_c)$ is $m_i\log\pi$, with $\log$ the natural logarithm. The real packet log-volume at the infinite place satisfies

$$
V_{\mathrm{pkt},\infty}(H_i)
=\sum_{c\colon L_i\to F_\infty}
  \left(\prod_{j\in L_i}w_\infty(c(j))\right)v_c(S_c)
=m_i\log\pi.
$$

[Lean statement](../../../../Solutions/Source_ReferenceIutCor312ArchimedeanVolume.lean#L30)

## 中文

### `archComponentVol_archLogShell`

给定宇宙层级 $u$ 上带有数域结构的域 $K$、Lean 的 `Type 0` 中的任意有限指标类型 $\iota$，以及任意处的指派 $c\colon\iota\to\operatorname{Place}(K)$。记 $V_c$ 为各指标对应的阿基米德分量在 $\mathbb R$ 上的张量积。指标 $j$ 对应实或复因子，由 `archPlace` 从 $c(j)$ 选出的无穷处决定。若 $c(j)$ 是无穷处，就取该处。若 $c(j)$ 是有限处，就取任意选定的无穷处。 [处的选取](../../../../Solutions/Source_ReferenceIutConcreteLocalPacket.lean#L209)

设 $m=|\iota|$，$d_c=\dim_{\mathbb R}V_c>0$。令 $B_c$ 为 $V_c$ 上射影张量半范数的闭单位球，$\mu_c$ 为满足 $\mu_c(B_c)=1$ 的加性 Haar 测度。阿基米德对数壳 $S_c=\pi^m B_c$ 的 Haar 测度为 $(\pi^m)^{d_c}$。它的归一化分量对数体积为

$$
v_c(S_c)=\frac{\log \mu_c(S_c)}{d_c}=m\log\pi,
$$

其中 $\log$ 为自然对数。若 $\iota$ 为空，则 $m=0$，对数壳为 $B_c$，其归一化分量对数体积为零。 [声明](../../../../Solutions/Source_ReferenceIutConcreteLocalArchimedean.lean#L158) · [归一化](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalArchimedeanTensorHaar.lean#L80)

### `exists_leastHull_infinite`

给定宇宙层级 $u$ 上的数域 $K$、Lean 的 `Type 0` 中的有限指标类型 $\iota$，以及对每个指标指定一个处的映射 $c$。记 $V_c$ 为 `archPlace` 选出的无穷处所对应的实或复因子在 $\mathbb R$ 上的张量积。`archPlace` 对无穷处取原处，对有限处取同一个选定的无穷处。设 $B_c$ 为 $V_c$ 的射影张量半范数的闭单位球，$\mu_c$ 为满足 $\mu_c(B_c)=1$ 的加性 Haar 测度。

设 $U\subseteq V_c$ 非空且可测，闭包紧致，并且 $0<\mu_c(U)<\infty$。存在实数 $t>0$ 使 $U\subseteq t B_c$。对所有满足 $U\subseteq t' B_c$ 的 $t'>0$，都有 $t\le t'$。证明取 $t$ 为 $U$ 上射影张量半范数的上确界。 [源码声明](../../../../Solutions/Source_ReferenceIutConcreteLocalArchimedean.lean#L136) · [半径的定义](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalArchimedeanTensorRadialHull.lean#L80)

### `prop15`

给定宇宙层级 $u$ 上的数域 $K$、Lean 的 `Type 0` 中的有限指标类型 $\iota$，以及对每个指标指定一个处的映射 $c$。对每个 $j$，记 $F_j$ 为 `archPlace` 从 $c(j)$ 选出的无穷处对应的实或复因子。`archPlace` 对无穷处取原处，对有限处取同一个选定的无穷处。设 $V_c=\bigotimes_{j\in\iota,\mathbb R} F_j$，$B_c$ 为其中的闭射影单位球。对数壳为 $S_c=\pi^{|\iota|}B_c$。

设 $\varphi\colon V_c\to V_c$ 属于 `archIndAut c`，即存在一族 $F_j$ 的实代数自同构 $\sigma_j$，它们在张量积上诱导 $\varphi$。则 $\varphi(S_c)\subseteq\pi^{|\iota|}B_c$。指标类型为空时，缩放因子为一。 [允许的映射](../../../../Solutions/Source_ReferenceIutConcreteLocalArchimedean.lean#L175) · [源码声明](../../../../Solutions/Source_ReferenceIutConcreteLocalArchimedean.lean#L188)

### `ThetaLocalData.packetVol_thetaHull_infinite`

在任意宇宙层级，给定一个远 Abel 几何、其上的一个缓和几何、关于这两个几何的初始 $\Theta$ 数据 $D$，以及 $D$ 在其参数 $K_t$ 所对应的具体局部理论中的 $\Theta$ 局部数据。设 $\ell$ 为 $D$ 的自然数参数，令 $n=\lfloor\max(\ell-1,0)/2\rfloor$。对标准标签集递增族中每个从零开始的指标 $0\le i<n$，其标签集为 $L_i=\{0,\ldots,i+1\}$，标签数为 $m_i=|L_i|=i+2$。当 $n=0$ 时，指标范围为空。在无穷位，记局部理论给出的有限纤维为 $F_\infty$，其实数权重为 $w_\infty$，满足 $\sum_{a\in F_\infty}w_\infty(a)=1$。分量积包的分量由函数 $c\colon L_i\to F_\infty$ 编号。标签集 $L_i$ 的 $\Theta$-包络在无穷位的区域 $H_i$ 是各分量对数壳 $S_c$ 的乘积，每个 $S_c$ 由相应分量的射影单位球按 $\pi^{m_i}$ 缩放得到。若 $d_c$ 是分量张量空间的实维数，则 $S_c$ 的归一化 Haar 测度为 $(\pi^{m_i})^{d_c}$，其归一化分量对数体积 $v_c(S_c)$ 为 $m_i\log\pi$，其中 $\log$ 为自然对数。无穷位的实数值分量积包对数体积满足

$$
V_{\mathrm{pkt},\infty}(H_i)
=\sum_{c\colon L_i\to F_\infty}
  \left(\prod_{j\in L_i}w_\infty(c(j))\right)v_c(S_c)
=m_i\log\pi.
$$

[源码声明](../../../../Solutions/Source_ReferenceIutCor312ArchimedeanVolume.lean#L30)

## 日本語

### `archComponentVol_archLogShell`

宇宙レベル $u$ の数体 $K$、Lean の `Type 0` に属する任意の有限添字型 $\iota$、および $K$ の素点を割り当てる任意の写像 $c\colon\iota\to\operatorname{Place}(K)$ を取る。$V_c$ を $\iota$ で添字付けられたアルキメデス因子の $\mathbb R$ 上のテンソル積とする。$j$ に対応する因子が実型か複素型かは、`archPlace` が $c(j)$ から選ぶ無限素点で決まる。$c(j)$ が無限素点ならその素点を用い、有限素点なら任意に選んだ無限素点を用いる。 [素点の選択](../../../../Solutions/Source_ReferenceIutConcreteLocalPacket.lean#L209)

$m=|\iota|$、$d_c=\dim_{\mathbb R}V_c>0$ とする。$B_c$ を $V_c$ の射影テンソル半ノルムに関する閉単位球、$\mu_c$ を $\mu_c(B_c)=1$ と正規化した加法的 Haar 測度とする。アルキメデス対数殻 $S_c=\pi^m B_c$ の Haar 測度は $(\pi^m)^{d_c}$ である。$\log$ を自然対数とすると、その正規化成分対数体積は

$$
v_c(S_c)=\frac{\log \mu_c(S_c)}{d_c}=m\log\pi
$$

である。$\iota$ が空の場合は $m=0$ であり、対数殻は $B_c$ となり、その正規化成分対数体積は零である。 [定理](../../../../Solutions/Source_ReferenceIutConcreteLocalArchimedean.lean#L158) · [正規化](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalArchimedeanTensorHaar.lean#L80)

### `exists_leastHull_infinite`

宇宙レベル $u$ の数体 $K$、Lean の `Type 0` に属する有限添字型 $\iota$、および各添字に素点を割り当てる写像 $c$ を取る。$V_c$ を、`archPlace` が選ぶ無限素点に対応する実または複素因子の $\mathbb R$ 上のテンソル積とする。`archPlace` は、無限素点に対してはその素点を、有限素点に対しては固定した無限素点を用いる。$B_c$ を $V_c$ の射影テンソル半ノルムに関する閉単位球、$\mu_c$ を $\mu_c(B_c)=1$ と正規化した加法的 Haar 測度とする。

$U\subseteq V_c$ は空でない可測集合であり、その閉包はコンパクトで、$0<\mu_c(U)<\infty$ を満たすとする。ある実数 $t>0$ に対して $U\subseteq t B_c$ が成り立つ。さらに、$U\subseteq t' B_c$ を満たす任意の $t'>0$ に対し $t\le t'$ が成り立つ。証明では $t$ を $U$ 上での射影テンソル半ノルムの上限に取る。 [定理](../../../../Solutions/Source_ReferenceIutConcreteLocalArchimedean.lean#L136) · [半径の定義](../../../../../ArithmeticTeichmullerSpaces/ArithmeticTeichmullerSpaces/Act1Scene1/LocalArchimedeanTensorRadialHull.lean#L80)

### `prop15`

宇宙レベル $u$ の数体 $K$、Lean の `Type 0` に属する有限添字型 $\iota$、および各添字に素点を割り当てる写像 $c$ を取る。各 $j$ について、$F_j$ を `archPlace` が $c(j)$ から選ぶ無限素点に対応する実または複素因子とする。`archPlace` は、無限素点に対してはその素点を、有限素点に対しては固定した無限素点を用いる。$V_c=\bigotimes_{j\in\iota,\mathbb R} F_j$ とし、$B_c$ をその射影テンソル半ノルムに関する閉単位球とする。対数殻は $S_c=\pi^{|\iota|}B_c$ である。

写像 $\varphi\colon V_c\to V_c$ は `archIndAut c` に属すとする。すなわち、各 $F_j$ の実代数自己同型 $\sigma_j$ の族が存在し、テンソル積上に $\varphi$ を誘導する。このとき $\varphi(S_c)\subseteq \pi^{|\iota|}B_c$ が成り立つ。添字型が空なら倍率は一である。 [写像の定義](../../../../Solutions/Source_ReferenceIutConcreteLocalArchimedean.lean#L175) · [定理](../../../../Solutions/Source_ReferenceIutConcreteLocalArchimedean.lean#L188)

### `ThetaLocalData.packetVol_thetaHull_infinite`

任意の宇宙レベルで、遠アーベル幾何、その上のテンパード幾何、それらに関する初期 $\Theta$ データ $D$、および $D$ のパラメータ $K_t$ に付随する具体的な局所理論における $D$ の $\Theta$ 局所データを取る。$D$ の自然数のパラメータを $\ell$ とし、$n=\lfloor\max(\ell-1,0)/2\rfloor$ とおく。標準プロセッションの各カプセルの添字を $0\le i<n$ とすると、そのラベル集合は $L_i=\{0,\ldots,i+1\}$ であり、ラベル数は $m_i=|L_i|=i+2$ である。$n=0$ のとき、添字の範囲は空である。無限素点において、局所理論が与える有限ファイバーを $F_\infty$、その実数値の重みを $w_\infty$ とし、$\sum_{a\in F_\infty}w_\infty(a)=1$ とする。パケットの成分は写像 $c\colon L_i\to F_\infty$ で添字付けられる。カプセル $i$ の $\Theta$ 包の無限素点における領域 $H_i$ は各成分の対数殻 $S_c$ の直積である。各 $S_c$ は対応する成分の射影単位球を $\pi^{m_i}$ 倍したものである。成分のテンソル空間の実次元を $d_c$ とすると、$S_c$ の正規化 Haar 測度は $(\pi^{m_i})^{d_c}$ であり、その正規化された成分対数体積 $v_c(S_c)$ は $m_i\log\pi$ であり、$\log$ は自然対数を表す。無限素点での実数値のパケット対数体積は次を満たす。

$$
V_{\mathrm{pkt},\infty}(H_i)
=\sum_{c\colon L_i\to F_\infty}
  \left(\prod_{j\in L_i}w_\infty(c(j))\right)v_c(S_c)
=m_i\log\pi.
$$

[定理](../../../../Solutions/Source_ReferenceIutCor312ArchimedeanVolume.lean#L30)

## MCP-CI

The source file for the three local declarations matches the SHA-256 entry in the archived review. The three declarations depend on `propext`, `Classical.choice`, and `Quot.sound`. [Review ci-021744-b251f5a2](../receipts/round-ci-021744-b251f5a2-result.json)
