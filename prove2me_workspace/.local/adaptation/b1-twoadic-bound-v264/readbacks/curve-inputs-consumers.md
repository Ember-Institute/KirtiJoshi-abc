# English

For the supplied Legendre curve data $P$ and compactly bounded subset $K$, the source chooses

$$B=\max(4K.c,0).$$

The theorem `curveInputs_B_nonneg K` proves $0\leq B$ for every $K$. For any natural number $d$ and any point $x\in K$ of degree at most $d$, `curveInputs_heightEq_two_le P K d x` proves that the contribution at $2$ from the same curve, arithmetic certificate, and Tate inputs is at most $B$. Its proof uses only $x\in K$; the degree condition matches the complete input record's domain.

These results supply the exact `CurveInputs` fields `B_nonneg` and `heightEq_two_le`, with the source's chosen value of `B`. The source forwards all three fields unchanged to `Corollary22Inputs`. In its theorem `c2`, the bound has three concrete uses. It controls the height remaining after the contribution at $2$ is removed, in the argument excluding a cyclic subgroup. It helps prove that a place of multiplicative reduction exists away from both $2$ and the selected prime. It also controls the error when recovering the all-primes height from the height away from those two primes. The same $B$ occurs in the height threshold and in the final additive term $40\eta+B/3$, where $\eta$ is the supplied prime-counting constant.

The results retain the actual supplied curve data. They establish these two field values for every such input; they do not construct the complete curve-input record or the additional data required by `c2`. Mochizuki's IUT IV, proof of Corollary 2.2(ii), uses a bound for the difference between all-primes height and height away from $2$ in the corresponding arithmetic estimate.

# 简体中文

对所提供的 Legendre 曲线数据 $P$ 和【译名待定：compactly bounded subset】$K$，源码选取

$$B=\max(4K.c,0)。$$

定理 `curveInputs_B_nonneg K` 对任意 $K$ 证明 $0\leq B$。对任意自然数 $d$ 及满足 $x\in K$、次数至多为 $d$ 的点 $x$，`curveInputs_heightEq_two_le P K d x` 证明：由同一曲线、算术证书和 Tate 输入计算的素数 $2$ 处高度贡献至多为 $B$。证明只使用 $x\in K$；次数条件用于匹配完整输入记录的定义范围。

这两个结果给出 `CurveInputs` 中 `B_nonneg` 和 `heightEq_two_le` 两个字段的精确值，并保留源码选择的 `B`。源码将这三个字段原样传给 `Corollary22Inputs`。其定理 `c2` 在三个具体步骤中使用此界：在排除循环子群的论证中，控制去掉素数 $2$ 处贡献后的高度；在证明素数 $2$ 和所选素数之外存在乘法约化素位时提供高度控制；在从去掉这两个素数后的高度恢复全部素位高度时控制误差。同一个 $B$ 还进入高度阈值和最终加法项 $40\eta+B/3$，其中 $\eta$ 是所提供的素数计数常数。

这些结果保留实际给定的曲线数据，对每个此类输入证明两个字段所需结论；它们没有构造完整的曲线输入记录，也没有构造 `c2` 所需的其他数据。Mochizuki《IUT IV》推论 2.2(ii) 的证明同样在相应算术估计中使用全部素位高度与去掉素数 $2$ 后的高度之差的上界。

# 日本語

与えられた Legendre 曲線のデータ $P$ とコンパクト有界部分集合 $K$ に対し、ソースは

$$B=\max(4K.c,0)$$

を選ぶ。定理 `curveInputs_B_nonneg K` は、任意の $K$ に対して $0\leq B$ を証明する。任意の自然数 $d$ と、$x\in K$ かつ次数が $d$ 以下である点 $x$ に対し、`curveInputs_heightEq_two_le P K d x` は、同じ曲線、算術的証明書、および Tate 入力から計算した素数 $2$ における高さの寄与が $B$ 以下であることを証明する。証明は $x\in K$ のみを用い、次数条件は完全な入力レコードの定義域に合わせるためにある。

この二つの結果は、ソースが選ぶ `B` とともに、`CurveInputs` のフィールド `B_nonneg` と `heightEq_two_le` の正確な値を与える。ソースは三つのフィールドをそのまま `Corollary22Inputs` に渡す。その定理 `c2` は、この上限を三つの段階で用いる。巡回部分群を排除する議論で、素数 $2$ の寄与を除いた高さを制御する。素数 $2$ と選んだ素数の両方から離れた場所に、乗法的還元をもつ素点が存在することを示す際にも用いる。さらに、この二つの素数を除いた高さから全素点の高さを復元する際の誤差を制御する。同じ $B$ は高さの閾値と、最後の加法項 $40\eta+B/3$ にも現れる。$\eta$ は与えられた素数計数定数である。

これらの結果は実際に与えられた曲線データを保ち、そのような各入力に対して二つのフィールドに必要な結論を証明する。完全な曲線入力レコードや、`c2` に必要な他のデータを構成するものではない。Mochizuki の IUT IV、系 2.2(ii) の証明も、対応する算術評価において、全素点の高さと素数 $2$ を除いた高さとの差の上限を用いる。
