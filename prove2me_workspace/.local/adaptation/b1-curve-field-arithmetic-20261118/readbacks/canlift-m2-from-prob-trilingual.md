# 从边界核到点映射 · From a boundary kernel to a point map · 境界核から点写像へ

### 简体中文

设 $k$ 是闭球紧致的非平凡赋范域，$Y=\mathbb P^1(k)$ 取一点紧化的博雷尔结构。令 $D_3\subseteq Y^3$ 为坐标两两互异的三元组集合。若 $Y$ 上的概率测度 $\mu$ 满足 $\mu^{\otimes3}(D_3)=0$，`exists_pair_of_triple_null` 给出 $r,s\in Y$，使 $\mu(\{r,s\}^{\mathrm c})=0$。此处允许 $r=s$。若 $r,s$ 互异，二重积在对角线上的质量是 $\mu(\{r\})^2+\mu(\{s\})^2$。对角线质量大于 $1/2$ 时，存在质量大于 $1/2$ 的原子，且它唯一。对角线质量不超过 $1/2$ 时，两个点互异且各有质量 $1/2$。

设 $B=\mathbb P^1(\mathbb R)$，$\beta$ 为沿 $\mathbb R\hookrightarrow B$ 推前的勒贝格测度。取可数 $\Gamma\le\mathrm{SL}_2(\mathbb R)$、带可判定相等性的 $k$，以及 $a:\mathrm{SL}_2(\mathbb R)\to\mathrm{GL}_2(k)$。假定 $\Gamma$ 双遍历，即 $B^2$ 上每个在对角作用下不变的可测集合，其自身或补集的 $\beta\otimes\beta$ 测度为零。假定 $a(gh)y=a(g)(a(h)y)$ 对每个 $g,h\in\Gamma$ 和 $y\in Y$ 成立，且 $\Gamma$ 的每个有限指数子群在 $Y$ 上均无公共不动点。马尔可夫核 $\kappa$ 对每个 $\gamma\in\Gamma$ 满足 $\kappa(\gamma b)=a(\gamma)_*\kappa(b)$ 对 $\beta$ 几乎处处的 $b$ 成立。若 $\kappa(b)^{\otimes3}(D_3)=0$ 亦对 $\beta$ 几乎处处的 $b$ 成立，`exists_pointMap_of_triple_null` 给出可测 $\psi:B\to Y$，使 $\psi(\gamma b)=a(\gamma)\psi(b)$ 对每个 $\gamma\in\Gamma$ 以及相应几乎处处的 $b$ 成立。

证明在大原子分支可测地选取该原子。在等质量分支，证明从受限的二重积核可测地选出有序点对，再用 `noPair` 排除所得同变无序点对。`commensurator_superrigidity` 将点映射交给 `ae_ne_of_equivariant` 和 `equivariant_commensurator`。

### English

Let $k$ be a nontrivially normed field whose closed balls are compact. Give $Y=\mathbb P^1(k)$ the Borel structure of the one-point compactification. Let $D_3\subseteq Y^3$ be the set of triples with pairwise distinct coordinates. Suppose a probability measure $\mu$ on $Y$ satisfies $\mu^{\otimes3}(D_3)=0$. Then `exists_pair_of_triple_null` gives $r,s\in Y$ with $\mu(\{r,s\}^{\mathrm c})=0$, allowing $r=s$. If $r$ and $s$ are distinct, the diagonal mass of the double product is $\mu(\{r\})^2+\mu(\{s\})^2$. When this mass exceeds $1/2$, there is a unique atom of mass greater than $1/2$. When the diagonal mass is at most $1/2$, the two points are distinct and each has mass $1/2$.

Let $B=\mathbb P^1(\mathbb R)$ and let $\beta$ be the pushforward of Lebesgue measure along $\mathbb R\hookrightarrow B$. Take a countable $\Gamma\le\mathrm{SL}_2(\mathbb R)$ and let $a:\mathrm{SL}_2(\mathbb R)\to\mathrm{GL}_2(k)$, with decidable equality on $k$. Assume double ergodicity. For each measurable subset of $B^2$ invariant under the diagonal $\Gamma$-action, either the subset or its complement has $\beta\otimes\beta$ measure zero. Assume $a(gh)y=a(g)(a(h)y)$ for all $g,h\in\Gamma$ and $y\in Y$. Assume every finite-index subgroup of $\Gamma$ has no common fixed point in $Y$.

Take a Markov kernel $\kappa$ from $B$ to $Y$. For each $\gamma\in\Gamma$, assume $\kappa(\gamma b)=a(\gamma)_*\kappa(b)$ for $\beta$-almost every $b$. Suppose also $\kappa(b)^{\otimes3}(D_3)=0$ for $\beta$-almost every $b$. Then `exists_pointMap_of_triple_null` gives a measurable $\psi:B\to Y$. For each $\gamma\in\Gamma$, $\psi(\gamma b)=a(\gamma)\psi(b)$ holds for $\beta$-almost every $b$.

The proof selects the heavy atom measurably when it exists. In the equal-mass case, it selects an ordered pair from a restricted double product kernel. It then uses `noPair` to exclude the associated equivariant unordered pair. The theorem `commensurator_superrigidity` passes the point map to `ae_ne_of_equivariant` and `equivariant_commensurator`.

### 日本語

$k$ を閉球がコンパクトな非自明なノルム付き体とし、$Y=\mathbb P^1(k)$ に一点コンパクト化のボレル構造を入れる。$D_3\subseteq Y^3$ を座標が互いに異なる三つ組全体とする。$Y$ 上の確率測度 $\mu$ が $\mu^{\otimes3}(D_3)=0$ を満たすなら、`exists_pair_of_triple_null` は $\mu(\{r,s\}^{\mathrm c})=0$ を満たす $r,s\in Y$ を与える。$r=s$ の場合も含む。$r,s$ が相異なる場合、二重積が対角線に与える測度は $\mu(\{r\})^2+\mu(\{s\})^2$ である。対角線の測度が $1/2$ を超える場合、質量が $1/2$ を超える原子がただ一つ存在する。対角線の測度が $1/2$ 以下の場合、二点は相異なり、それぞれの質量は $1/2$ である。

$B=\mathbb P^1(\mathbb R)$ とし、$\beta$ を $\mathbb R\hookrightarrow B$ によるルベーグ測度の押し出しとする。可算な $\Gamma\le\mathrm{SL}_2(\mathbb R)$ と $a:\mathrm{SL}_2(\mathbb R)\to\mathrm{GL}_2(k)$ を取り、$k$ の等号を決定可能とする。$\Gamma$ に二重エルゴード性を仮定する。すなわち、$B^2$ 上の対角作用で不変な可測集合について、その集合または補集合の $\beta\otimes\beta$ 測度は零である。各 $g,h\in\Gamma$ と $y\in Y$ について $a(gh)y=a(g)(a(h)y)$ が成り立つと仮定する。また $\Gamma$ のすべての有限指数部分群は $Y$ 上に共通の固定点をもたないと仮定する。マルコフ核 $\kappa$ が各 $\gamma\in\Gamma$ に対し $\kappa(\gamma b)=a(\gamma)_*\kappa(b)$ を $\beta$ に関してほとんどすべての $b$ で満たすとする。さらに $\kappa(b)^{\otimes3}(D_3)=0$ がほとんど至る所で成り立つなら、`exists_pointMap_of_triple_null` は可測写像 $\psi:B\to Y$ で、各 $\gamma\in\Gamma$ に対し $\psi(\gamma b)=a(\gamma)\psi(b)$ がほとんどすべての $b$ で成り立つものを与える。

証明では、質量が $1/2$ を超える原子がある場合にその原子を可測に選ぶ。質量が等しい場合、二重積核の制限から順序付きの点の組を可測に選ぶ。そこから得られる順序なしの同変な点の組は `noPair` により排除される。`commensurator_superrigidity` は得られた点写像を `ae_ne_of_equivariant` と `equivariant_commensurator` に渡す。 [FromProb](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftFromProb.lean:213) · [Superrigidity](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftSuperrigidity.lean:85)
