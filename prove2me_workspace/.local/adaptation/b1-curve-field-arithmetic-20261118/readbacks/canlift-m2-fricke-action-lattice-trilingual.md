# M2 非初等性、逐素数射影作用与格 · M2 non-elementarity, p-adic actions, and lattices · M2 の非初等性、p 進射影作用、格子

## 中文

- **非初等性。** 设 $\Gamma\le\mathrm{SL}_2(\mathbb R)$ 在特征零赋范域的射影直线上满足 `ActsOn`。若 $K\in\Gamma$ 作用为平移 $2$，且 $A\in\Gamma$ 移动 $\infty$，则每个有限指数子群都没有公共不动点。该子群含 $K$ 和 $AKA^{-1}$ 的正幂，两者的唯一不动点分别为 $\infty$ 与 $a(A)\infty$。本地 `nonElem_slMap` 调用 `nonElem_of`，用 $x\ne0$ 证明首个 Fricke 生成元 $A_0$ 移动 $\infty$。上游 `sq_fixed_of_dense` 与 `padicNorm_trace_sq_le_one` 把相应的 `NonElem` 交给可公度化群超刚性。 [本地证明][non-elem] · [本地复分支][non-elem-slmap] · [上游复分支][complex-call] · [上游逐素数分支][padic-non-elem-call]
- **逐素数射影作用。** 对素数 $p$，给定有理矩阵代表后，`aP_commK` 给出交换子 $K$ 的平移 $2$，`aP_nA_infty` 在 $x\ne0$ 时给出 $A_0$ 移动 $\infty$。上游以这两式应用 `nonElem_of`。`aP_uU_two` 给出上三角幺幂矩阵 $u_U(2)$ 的同一平移。上游用延拓等式把该作用传给连续延拓，再调用 `padic_contradiction`。 [交换子][ap-k] · [首个生成元][ap-a] · [上三角幺幂矩阵][ap-u] · [上游非初等性调用][padic-non-elem-call] · [上游延拓后的调用][padic-transl-call]
- **范数比较。** 设 $R$ 为 $\gamma$ 的选定有理矩阵代表。若 $\operatorname{padicNorm}_p((\operatorname{tr}R)^2/\det R)>1$，则 `aP_det_norm_lt_trace_norm_sq` 给出 $\|\det a_P(\gamma)\|<\|\operatorname{tr}a_P(\gamma)\|^2$。上游 `Padic.exists_degenerate_limit` 用该严格不等式证明幂作用下的三点组趋于退化。该退化极限及最终的逐素数范数界 $\operatorname{padicNorm}_p((\operatorname{tr}R)^2/\det R)\le1$ 各需单独验收。 [本地比较][ap-norm] · [上游退化极限调用][padic-limit-call] · [上游范数界][padic-bound]
- **格。** `GoodLattice.of_le` 从基本集的有限个陪集平移构造有限指数子群的基本集，保留有限双曲面积、轨道覆盖与有限重数。上游超刚性用它对有限指数子群建立双遍历性。对含非平凡平移的离散子群，`finite_strip_multiplicity` 给出实部有界、虚部有正下界的条带中的有限重数。上游 `goodLattice_normal` 以 $K^2$ 的平移 $4$ 使用此结论。完整正规形 `GoodLattice` 仍需验收离散性、条带覆盖和组装。 [有限指数][finite-index] · [有限重数][strip] · [上游双遍历性][subgroup-ergodicity] · [上游正规形组装][normal-lattice]

## English

- **Non-elementarity.** Let $\Gamma\le\mathrm{SL}_2(\mathbb R)$ act on the projective line of a normed field of characteristic zero. Assume `ActsOn`. Suppose $K\in\Gamma$ acts by translation by $2$ and $A\in\Gamma$ moves infinity. Each finite-index subgroup contains positive powers of $K$ and $AKA^{-1}$. These powers have distinct unique fixed points, infinity and $a(A)\infty$. The local theorem `nonElem_slMap` uses $x\ne0$ to show that the first Fricke generator $A_0$ moves infinity. It then applies `nonElem_of`. Upstream, `sq_fixed_of_dense` and `padicNorm_trace_sq_le_one` pass `NonElem` to commensurator superrigidity. [Local proof][non-elem] · [Local complex case][non-elem-slmap] · [Upstream complex case][complex-call] · [Upstream p-adic case][padic-non-elem-call]
- **P-adic projective actions.** Fix a prime $p$. The action $a_P$ uses rational matrix representatives. The theorem `aP_commK` gives translation by $2$ for the commutator $K$. The theorem `aP_nA_infty` shows that $A_0$ moves infinity when $x\ne0$. The upstream proof uses both facts as hypotheses for `nonElem_of`. The theorem `aP_uU_two` gives the same translation for the upper unipotent $u_U(2)$. The upstream proof transfers this action to the continuous extension and calls `padic_contradiction`. [Commutator][ap-k] · [First generator][ap-a] · [Upper unipotent][ap-u] · [Upstream non-elementarity call][padic-non-elem-call] · [Upstream use after extension][padic-transl-call]
- **Norm comparison.** Let $R$ be the chosen rational matrix representative of $\gamma$. If $\operatorname{padicNorm}_p((\operatorname{tr}R)^2/\det R)>1$, then `aP_det_norm_lt_trace_norm_sq` gives $\|\det a_P(\gamma)\|<\|\operatorname{tr}a_P(\gamma)\|^2$. The upstream theorem `Padic.exists_degenerate_limit` uses this strict inequality. Powers of $a_P(\gamma)$ move the standard triple to a sequence with a degenerate limit. The degenerate limit and the final bound $\operatorname{padicNorm}_p((\operatorname{tr}R)^2/\det R)\le1$ at each prime require separate checks. [Local comparison][ap-norm] · [Upstream degenerate limit call][padic-limit-call] · [Upstream norm bound][padic-bound]
- **Lattices.** The theorem `GoodLattice.of_le` uses finitely many coset translates of a fundamental set to construct one for a finite-index subgroup. The union retains finite hyperbolic area, orbit coverage, and finite multiplicity. Upstream, commensurator superrigidity uses it to obtain double ergodicity for finite-index subgroups. Let a discrete group contain a nontrivial translation. The theorem `finite_strip_multiplicity` gives finite multiplicity in a strip with bounded real part and a positive lower height. Upstream, `goodLattice_normal` applies it to $K^2$, which translates by $4$. The full normal-form `GoodLattice` still requires checks for discreteness, strip coverage, and assembly. [Finite index][finite-index] · [Finite multiplicity][strip] · [Upstream double ergodicity][subgroup-ergodicity] · [Upstream normal-form assembly][normal-lattice]

## 日本語

- **非初等性。** $\Gamma\le\mathrm{SL}_2(\mathbb R)$ が標数零のノルム体の射影直線に作用し、`ActsOn` を満たすとする。$K\in\Gamma$ が $2$ の平行移動として作用し、$A\in\Gamma$ が無限遠点を動かすなら、有限指数部分群は共通固定点をもたない。各部分群は $K$ と $AKA^{-1}$ の正のべきを含み、それぞれの唯一の固定点は $\infty$ と $a(A)\infty$ である。ローカルの `nonElem_slMap` は $x\ne0$ を用いて最初の Fricke 生成元 $A_0$ について `nonElem_of` を適用する。上流の `sq_fixed_of_dense` と `padicNorm_trace_sq_le_one` は、それぞれの `NonElem` を可公度化群の超剛性に渡す。 [ローカルの証明][non-elem] · [ローカルの複素数の場合][non-elem-slmap] · [上流の複素数の場合][complex-call] · [上流の p 進の場合][padic-non-elem-call]
- **p 進射影作用。** 素数 $p$ を固定し、各元に有理行列の代表元を与える。`aP_commK` は交換子 $K$ が $2$ の平行移動として作用することを示す。`aP_nA_infty` は $x\ne0$ のとき $A_0$ が無限遠点を動かすことを示す。上流ではこの二つを `nonElem_of` に渡す。`aP_uU_two` は上三角ユニポテント行列 $u_U(2)$ に同じ平行移動を与える。上流の証明はこの作用を連続延長に移し、`padic_contradiction` を適用する。 [交換子][ap-k] · [最初の生成元][ap-a] · [上三角ユニポテント行列][ap-u] · [上流の非初等性の適用][padic-non-elem-call] · [上流の延長後の適用][padic-transl-call]
- **ノルムの比較。** $R$ を $\gamma$ の選んだ有理行列の代表元とする。$\operatorname{padicNorm}_p((\operatorname{tr}R)^2/\det R)>1$ なら、`aP_det_norm_lt_trace_norm_sq` により $\|\det a_P(\gamma)\|<\|\operatorname{tr}a_P(\gamma)\|^2$ が成り立つ。上流の `Padic.exists_degenerate_limit` はこの狭義不等式を使い、べきによる標準三点組の像が退化した三点組に収束することを示す。この退化極限と素数ごとの最終的な上界 $\operatorname{padicNorm}_p((\operatorname{tr}R)^2/\det R)\le1$ は、それぞれ検証が必要である。 [ローカルの比較][ap-norm] · [上流の退化極限の適用][padic-limit-call] · [上流のノルムの上界][padic-bound]
- **格子。** `GoodLattice.of_le` は基本集合の有限個の剰余類による移動から、有限指数部分群の基本集合を構成する。この和集合は有限な双曲面積、各軌道との交わり、有限重複度を保つ。上流の可公度化群の超剛性はこれを有限指数部分群の二重エルゴード性に使う。`finite_strip_multiplicity` は非自明な平行移動を含む離散部分群について、実部が有界で虚部に正の下界がある帯で重複度が有限であることを示す。上流の `goodLattice_normal` はこれを $4$ の平行移動である $K^2$ に適用する。標準形の `GoodLattice` の構成には、離散性、帯での軌道被覆、全体の組み立ての検証が必要である。 [有限指数][finite-index] · [有限重複度][strip] · [上流の二重エルゴード性][subgroup-ergodicity] · [上流の標準形の構成][normal-lattice]

## MCP-CI

| Module | Leaf check | Artifact |
| --- | --- | --- |
| `NonElementary` | `ci-024685-1418cf24` | `ci-024698-a1d068e6` |
| `FrickePadicAction` | `ci-024684-7f5b71cd` | `ci-024700-18ff5a9a` |
| `GoodLatticeBasic` | `ci-024667-271fa1ff` | `ci-024679-39cab1e3` |

Review `ci-024720-29535532` reports only `propext`, `Classical.choice`, and `Quot.sound` for the eight checked declarations. [Review source][review]

[non-elem]: ../../../../Solutions/Source_ReferenceIutCanLiftNonElementary.lean#L55
[non-elem-slmap]: ../../../../Solutions/Source_ReferenceIutCanLiftNonElementary.lean#L102
[ap-norm]: ../../../../Solutions/Source_ReferenceIutCanLiftFrickePadicAction.lean#L34
[ap-k]: ../../../../Solutions/Source_ReferenceIutCanLiftFrickePadicAction.lean#L54
[ap-a]: ../../../../Solutions/Source_ReferenceIutCanLiftFrickePadicAction.lean#L68
[ap-u]: ../../../../Solutions/Source_ReferenceIutCanLiftFrickePadicAction.lean#L81
[finite-index]: ../../../../Solutions/Source_ReferenceIutCanLiftGoodLatticeBasic.lean#L25
[strip]: ../../../../Solutions/Source_ReferenceIutCanLiftGoodLatticeBasic.lean#L175
[review]: ../ReviewCanLiftFrickeActionLattice.lean#L11
[complex-call]: https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L235
[padic-non-elem-call]: https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L495
[padic-limit-call]: https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L517
[padic-transl-call]: https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L529
[padic-bound]: https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Final.lean#L451
[subgroup-ergodicity]: https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/Superrigidity.lean#L64
[normal-lattice]: https://github.com/lana-agents/orbicurve-cores/blob/61616dcd77fbe45c083a8ebfa7cc80728f86e841/OrbicurveCores/M2/GoodLattice.lean#L187
