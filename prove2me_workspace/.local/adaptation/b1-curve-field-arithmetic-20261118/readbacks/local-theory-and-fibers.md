# `LocalTheory` and `ConcreteFibers`

```text
e_w = ramIdx K w
f_w = inertDeg K w
p_w = residueChar w
localDeg K w = e_w · f_w
placeWeight K w = (e_w · f_w) / [K : ℚ]
infPlaceWeight K w = mult(w) / [K : ℚ]
ordp K w x = −log ‖x‖ / (e_w · f_w · log p_w)
differentExponent K w = ordDifferent K w / e_w

vol(m_p⁻¹(U)) = vol(U) + log p,   m_p(x) = p · x
vol(a · O) ≤ (−ordp K w x + ∑ᵢ dᵢ + 1) · log p + ∑_{i : p−2 < eᵢ} (3 + log eᵢ)
```

## English

- The local theory module defines the arithmetic quantities above for a number field `K`. The completion is `K_w`, and `ordDifferent K w` counts the prime of `w` in the factorization of the global different. The `LocalTheory K` record supplies the positivity and finiteness laws, the degree sums, and vanishing of the different exponent at unramified places. Its valuation fields give `ordp(p_w) = 1` and additivity on products of nonzero elements.
- `toRational` sends a finite place to its residue prime and every infinite place to `∞`. `fiberFiniteEquiv` identifies the fiber over `p` with finite places of residue characteristic `p`. `fiberInfiniteEquiv` identifies the fiber over `∞` with `InfinitePlace K`. These equivalences give `fiberFintype`. The projection `tuple` forgets the fiber proof, and `tuple_isOver` recovers the common residue characteristic. `weight_pos` and `weight_sum_one` prove that the displayed weights are positive and sum to `1` in each fiber. The latter uses `sum_localDeg` at a prime and `sum_mult` at infinity.
- `LocalTensor` supplies the tensor carrier indexed by a rational place and a finite tuple of places of `K`. It gives a commutative ring structure and topology, and an `ℝ`-algebra structure at infinity. `LocalTheory` keeps the factor maps, integral region `O`, log-shell, normalized log-volume, admissible regions, and indeterminacy maps as fields. At finite primes, the log-shell contains `O`. They agree at odd primes when every factor is unramified. The volume fields include volume `0` for `O` and volume `log t` for a positive real radial scaling `t` at infinity. The field `componentVol_prime_preimage` gives the prime preimage formula above. It requires an admissible region `U` and a tuple whose every place lies over `p`.
- The field `exists_leastHull` gives a least unit-scaled integral region containing an admissible region at a prime. The field `exists_leastHull_infinite` gives the least positive real scale of the projective unit ball in the real tensor space that contains the admissible region at infinity. Radial monotonicity is also a field. The concrete container uses these fields to construct least hulls for products of admissible components.
- `prop14_iii` supplies the displayed finite bound for a common-`p` tuple and nonzero factor scalar `x ∈ K_w` with `ordp K w x ≥ 0`. Here `dᵢ` and `eᵢ` are the normalized different exponent and the ramification index of the `i`-th place. One unit-scaled region `a · O` contains the image of the scaled integral region under every `φ ∈ indAut`. The fields `prop14_iv` and `prop15` give integral-region containment at finite primes and containment in `π^{|ι|} · O` for archimedean log-shell images. These bounds are inputs to the constructions.

## 中文

- `LocalTheory K` 对数域 `K` 使用上式中的显式算术量。位点完备化为 `K_w`，`ordDifferent K w` 是 `w` 对应的素理想在全局不同理想分解中的重数。结构体提供正性、有限性、次数求和和非分歧处不同理想阶为零的条件。赋值字段给出 `ordp(p_w) = 1`，以及非零元素相乘时赋值相加。
- `toRational` 将有限位点映到剩余特征对应的有理素数，将无穷位点映到 `∞`。`fiberFiniteEquiv` 将 `p` 上方的纤维与剩余特征为 `p` 的有限位点等同。`fiberInfiniteEquiv` 将 `∞` 上方的纤维与 `InfinitePlace K` 等同。两个等价给出 `fiberFintype`。`tuple` 取出各位点，`tuple_isOver` 给出它们共同的剩余特征。`weight_pos` 和 `weight_sum_one` 证明上式中的权重为正，且每个纤维中的权重和为 `1`。求和分别使用有限位点的 `sum_localDeg` 和无穷位点的 `sum_mult`。
- `LocalTensor` 提供以有理位点和 `K` 的有限位点元组为指标的张量载体，以及交换环结构和拓扑。它在无穷位点提供 `ℝ`-代数结构。`LocalTheory` 的字段包括因子映射、整区域 `O`、对数壳、归一化对数体积、容许区域和不定性映射。在有限素数处，对数壳包含 `O`。在每个因子均不分歧的奇素数处，两者相等。体积字段给出 `O` 的对数体积为 `0`，以及在无穷位点按正实数 `t` 径向缩放后的对数体积为 `log t`。`componentVol_prime_preimage` 给出上式中的素数原像公式，要求 `U` 是容许区域，且元组中所有位点均在 `p` 上方。
- `exists_leastHull` 在有限素数处给出包含容许区域的最小可逆元缩放整区域。`exists_leastHull_infinite` 在无穷处给出包含该区域的最小正实数径向缩放，所缩放的是该分量实张量空间中的射影单位球。径向缩放的单调性也是字段。具体容器使用这些字段构造容许分量直积的最小包络。
- `prop14_iii` 给出上式中的有限位点体积界。它要求元组各位点均在同一 `p` 上方，且因子中的 `x ∈ K_w` 非零并满足 `ordp K w x ≥ 0`。`dᵢ` 和 `eᵢ` 分别为第 `i` 个位点的归一化不同理想指数和分歧指数。同一个可逆元缩放区域 `a · O` 包含所有 `φ ∈ indAut` 对缩放整区域的像。`prop14_iv` 给出有限素数处整区域像的包含关系，`prop15` 将无穷位点对数壳的像限制在 `π^{|ι|} · O` 内。这些估计作为构造的输入。

## 日本語

- `LocalTheory K` は数体 `K` に対して上の算術量を用いる。素点での完備化は `K_w` であり、`ordDifferent K w` は大域ディファレントの素イデアル分解における `w` の重複度である。正値性、有限性、次数の和、および不分岐な素点でディファレントの指数が零になる条件は構造体のフィールドである。付値のフィールドは `ordp(p_w) = 1` と非零元の積に対する加法性を与える。
- `toRational` は有限素点を剰余標数に対応する有理素数へ、無限素点を `∞` へ送る。`fiberFiniteEquiv` は `p` 上のファイバーを剰余標数 `p` の有限素点と同一視し、`fiberInfiniteEquiv` は `∞` 上のファイバーを `InfinitePlace K` と同一視する。この同値から `fiberFintype` を得る。`tuple` は各素点を取り出し、`tuple_isOver` は共通の剰余標数を与える。`weight_pos` と `weight_sum_one` は、上の重みが正で各ファイバーでの和が `1` であることを証明する。有限素点では `sum_localDeg`、無限素点では `sum_mult` を用いる。
- `LocalTensor` は、有理素点と `K` の素点の有限個の組を添字とするテンソルの台、可換環構造、位相、および無限素点での `ℝ`-代数構造を与える。因子の写像、整領域 `O`、対数殻、正規化対数体積、許容領域、不定性の写像は `LocalTheory` のフィールドである。有限素数では対数殻が `O` を含む。すべての因子が不分岐な奇素数では、両者が一致する。`O` の対数体積は `0` であり、無限素点では正の実数 `t` による動径方向の拡大後の対数体積が `log t` になる。`componentVol_prime_preimage` は上の逆像の式を与える。この式には、許容領域 `U` と、すべての素点が `p` の上にある組が必要である。
- `exists_leastHull` は、有限素数で許容領域を含む最小の単元倍の整領域を与える。`exists_leastHull_infinite` は、無限素点で当該領域を含むように実テンソル空間の射影単位球を正の実数倍するとき、その倍率の最小値を与える。動径方向の拡大の単調性もフィールドである。具体的な容器はこれらを用いて、許容な成分の積の最小包を構成する。
- `prop14_iii` は上の有限素点での体積評価を与える。すべての素点が同じ `p` の上にあり、因子の `x ∈ K_w` が非零で `ordp K w x ≥ 0` を満たすと仮定する。`dᵢ` と `eᵢ` は第 `i` 素点の正規化ディファレント指数と分岐指数である。一つの単元倍 `a · O` が、拡大した整領域のすべての `φ ∈ indAut` による像を含む。`prop14_iv` は有限素数で整領域の像の包含を与え、`prop15` は無限素点で対数殻の像が `π^{|ι|} · O` に含まれることを与える。これらの評価は構成の入力である。

[Local arithmetic and tensor data](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean:64) · [Local hull fields](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_LocalTheory.lean:226) · [Concrete fibers and weight proofs](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteFibers.lean:27) · [Concrete container hull construction](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutConcreteContainer.lean:259)
