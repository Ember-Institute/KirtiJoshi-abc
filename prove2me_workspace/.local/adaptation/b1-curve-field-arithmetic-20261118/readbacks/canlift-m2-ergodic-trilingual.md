# Mautner 现象与双遍历性 · Mautner phenomenon and double ergodicity · Mautner 現象と二重エルゴード性

## ErgodicMautner

### 简体中文

令 $G=\mathrm{SL}_2(\mathbb R)$，$m=\mathrm{hopfMeasure}$，$i\in\mathbb H$ 为虚单位对应的点。设 $\Gamma\le G$ 可数，$F\subseteq\mathbb H$ 可测且双曲面积有限。对每个 $z\in\mathbb H$，使 $\gamma z\in F$ 的 $\gamma\in\Gamma$ 的数目 $M(z)$ 有限且至少为一。权函数 $\chi(g)=1_F(g i)/M(g i)$ 满足 $\sum_{\gamma\in\Gamma}\chi(\gamma g)=1$，且 $\int\chi\,dm<\infty$。若右乘 $h\in G$ 保持 $m$ 下所有非负可测函数的积分，对任意非负可测且左 $\Gamma$ 不变的 $\Xi$，加权积分 $\int\chi(g)\Xi(gh)\,dm(g)$ 等于 $\int\chi(g)\Xi(g)\,dm(g)$。

给定可测 $\Phi:G\to\mathbb R$，假定对所有 $g$ 有 $|\Phi(g)|\le1$，且 $\Phi(\gamma g)=\Phi(g)$ 对每个 $\gamma\in\Gamma$ 和 $g\in G$ 成立。再假定 $\Phi(ga_\sigma)=\Phi(g)$ 对所有 $\sigma\in\mathbb R$ 和 $g\in G$ 成立，其中 $a_\sigma=\operatorname{diag}(e^\sigma,e^{-\sigma})$。`ae_mul_unip_eq` 断言，对每个 $t\in\mathbb R$，$\Phi(gn_t)=\Phi(g)$ 对 $m$ 几乎处处的 $g$ 成立，其中 $n_t=\left(\begin{smallmatrix}1&t\\0&1\end{smallmatrix}\right)$。`Ergodic` 对边界不变集合的指示函数提升应用该定理。

### English

Let $G=\mathrm{SL}_2(\mathbb R)$, $m=\mathrm{hopfMeasure}$, and let $i\in\mathbb H$ be the imaginary unit. Take countable $\Gamma\le G$ and measurable $F\subseteq\mathbb H$ of finite hyperbolic area. For each $z\in\mathbb H$, let $M(z)$ count the $\gamma\in\Gamma$ with $\gamma z\in F$. Assume $1\le M(z)<\infty$. The weight $\chi(g)=1_F(g i)/M(g i)$ satisfies $\sum_{\gamma\in\Gamma}\chi(\gamma g)=1$ and $\int\chi\,dm<\infty$. Suppose right multiplication by $h\in G$ preserves the $m$-integral of all nonnegative measurable functions. Then $\int\chi(g)\Xi(gh)\,dm(g)=\int\chi(g)\Xi(g)\,dm(g)$ for every nonnegative measurable left $\Gamma$-invariant $\Xi$.

Let $\Phi:G\to\mathbb R$ be measurable with $|\Phi(g)|\le1$ for all $g$. Assume $\Phi(\gamma g)=\Phi(g)$ for every $\gamma\in\Gamma$ and $g\in G$. Put $a_\sigma=\operatorname{diag}(e^\sigma,e^{-\sigma})$ and assume $\Phi(ga_\sigma)=\Phi(g)$ for every real $\sigma$ and every $g\in G$. Put $n_t=\left(\begin{smallmatrix}1&t\\0&1\end{smallmatrix}\right)$. For each real $t$, `ae_mul_unip_eq` gives $\Phi(gn_t)=\Phi(g)$ for $m$-almost every $g$. `Ergodic` applies this theorem to a lifted indicator of an invariant boundary set.

### 日本語

$G=\mathrm{SL}_2(\mathbb R)$、$m=\mathrm{hopfMeasure}$ とし、$i\in\mathbb H$ を虚数単位とする。$\Gamma\le G$ を可算とし、$F\subseteq\mathbb H$ を双曲面積が有限の可測集合とする。各 $z\in\mathbb H$ に対し、$\gamma z\in F$ を満たす $\gamma\in\Gamma$ の個数 $M(z)$ は有限かつ一以上であると仮定する。重み $\chi(g)=1_F(g i)/M(g i)$ は $\sum_{\gamma\in\Gamma}\chi(\gamma g)=1$ と $\int\chi\,dm<\infty$ を満たす。$h\in G$ による右乗法がすべての非負可測関数の $m$ に関する積分を保つなら、左 $\Gamma$ 不変な非負可測関数 $\Xi$ に対し、$\int\chi(g)\Xi(gh)\,dm(g)=\int\chi(g)\Xi(g)\,dm(g)$ が成り立つ。

可測関数 $\Phi:G\to\mathbb R$ は、すべての $g$ で $|\Phi(g)|\le1$ を満たすとする。各 $\gamma\in\Gamma$ と $g\in G$ で $\Phi(\gamma g)=\Phi(g)$ を仮定する。$a_\sigma=\operatorname{diag}(e^\sigma,e^{-\sigma})$ とし、各 $\sigma\in\mathbb R$ と $g\in G$ で $\Phi(ga_\sigma)=\Phi(g)$ も仮定する。$n_t=\left(\begin{smallmatrix}1&t\\0&1\end{smallmatrix}\right)$ とすると、`ae_mul_unip_eq` により、各 $t\in\mathbb R$ に対し $\Phi(gn_t)=\Phi(g)$ が $m$ に関してほとんどすべての $g$ で成り立つ。`Ergodic` はこの定理を、境界の不変集合の指示関数を持ち上げたものに適用する。 [轨道权重](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftErgodicMautner.lean:92) · [Mautner 定理](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftErgodicMautner.lean:171)

## Ergodic

### 简体中文

取 $B=\mathbb P^1(\mathbb R)$，令 $\beta$ 是实直线的勒贝格测度沿 $\mathbb R\hookrightarrow B$ 的推前。`GoodLattice Γ` 给出离散性，以及一个可测、双曲面积有限、每个轨道均以有限正重数相交的上半平面集合。`GoodLattice.countable` 推出 $\Gamma$ 可数。若 $E\subseteq B^2$ 可测且在 $\Gamma$ 的对角作用下不变，`GoodLattice.ae_slice` 断言，对勒贝格几乎处处的 $x\in\mathbb R$，集合 $\{w\in\mathbb R:(x,w)\in E\}$ 或其补集是零测集。`GoodLattice.isDoublyErgodic` 将同样的切片结论应用于交换坐标后的 $E$，得到 $E$ 或其补集的 $\beta\otimes\beta$ 测度为零。

`GoodLattice.ae_eq_const` 对第二可数且满足 $T_0$ 的博雷尔目标空间给出可测、几乎处处 $\Gamma$ 不变的 $B^2$ 上映射几乎处处为常值。`isDoublyErgodic_of_le_normal` 将双遍历性用于满足正性、Fricke 关系和三个严格三角不等式的正规形群的所有有限指数子群。`commensurator_superrigidity` 使用格子和有限指数子群的双遍历性，分别取得点映射并推广其同变性。

### English

Let $B=\mathbb P^1(\mathbb R)$ and let $\beta$ be the pushforward of Lebesgue measure along $\mathbb R\hookrightarrow B$. The property `GoodLattice Γ` gives discreteness and a measurable upper half-plane set of finite hyperbolic area. Each orbit meets this set with positive finite multiplicity. By `GoodLattice.countable`, $\Gamma$ is countable. Take measurable $E\subseteq B^2$ invariant under the diagonal $\Gamma$-action. By `GoodLattice.ae_slice`, for Lebesgue-almost every $x\in\mathbb R$, the set $\{w\in\mathbb R:(x,w)\in E\}$ or its complement has measure zero. The theorem `GoodLattice.isDoublyErgodic` applies the slice result to both coordinate orders. Thus $E$ or its complement has $\beta\otimes\beta$ measure zero.

Let $Z$ be a second-countable $T_0$ space with its Borel structure. By `GoodLattice.ae_eq_const`, a measurable map from $B^2$ to $Z$ invariant almost everywhere under each $\gamma\in\Gamma$ is almost everywhere constant. For positive Fricke parameters satisfying the Fricke relation and strict triangle inequalities, `isDoublyErgodic_of_le_normal` gives double ergodicity for every finite-index subgroup. The theorem `commensurator_superrigidity` uses double ergodicity for the lattice to obtain a point map. It uses double ergodicity for finite-index subgroups to extend the map's equivariance.

### 日本語

$B=\mathbb P^1(\mathbb R)$ とし、$\beta$ を $\mathbb R\hookrightarrow B$ によるルベーグ測度の押し出しとする。`GoodLattice Γ` は離散性と、双曲面積が有限で各軌道と有限かつ正の重複度で交わる上半平面内の可測集合を与える。`GoodLattice.countable` により $\Gamma$ は可算である。$\Gamma$ の対角作用で不変な可測集合 $E\subseteq B^2$ を取る。`GoodLattice.ae_slice` により、ルベーグ測度に関してほとんどすべての $x\in\mathbb R$ について、$\{w\in\mathbb R:(x,w)\in E\}$ またはその補集合の測度が零となる。`GoodLattice.isDoublyErgodic` は両方の座標順に対して切片の結論を用いて、$E$ またはその補集合の $\beta\otimes\beta$ 測度が零であることを導く。

$Z$ を第二可算な $T_0$ 空間とし、ボレル構造を入れる。`GoodLattice.ae_eq_const` によれば、各 $\gamma\in\Gamma$ に関してほとんど至る所で不変な可測写像 $B^2\to Z$ は、ほとんど至る所で定数である。正の Fricke パラメータが Fricke 関係式と狭義の三角不等式を満たすとき、`isDoublyErgodic_of_le_normal` は標準形の群のすべての有限指数部分群に二重エルゴード性を与える。`commensurator_superrigidity` は格子の二重エルゴード性を点写像の構成に、有限指数部分群の二重エルゴード性を同変性の拡張に用いる。 [切片与双遍历](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftErgodic.lean:277) · [有限指数子群](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftErgodic.lean:428) · [超刚性消费者](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftSuperrigidity.lean:77)
