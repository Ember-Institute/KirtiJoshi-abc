# The prime lower bound in `c2`

## English

### `ThetaDataExistenceAtLeast`

Fix the height theory $T$, the geometric interfaces $AG,TG$, the compactly bounded data $K$, and a natural degree bound $d$. Let $W=T.\mathrm{cbsSet}(K)\cap T.\mathrm{ptLE}(T.\mathrm{tripod},d)$. Write $h(x)=I.h(x)$ for the height from the Corollary 2.2 inputs $I$. Take a natural number $N$, written `minimum` in Lean, and a predicate $P$ on Corollary 3.12 variant data. [Structure and parameters](Corollary22Inputs_c2.lean#L69)

The field `thetaData` of `ThetaDataExistenceAtLeast N P I` applies to each $x\in W$ outside `I.excCore` and every prime $\ell$ with $7\le\ell$ and $N\le\ell$. Write `L = I.localData x hx` for the local data at this point. The field takes these conditions.

- (P2) $\ell$ divides none of the local orders `L.hv v` at places in `L.bad`.
- (P3) At each place in `L.bad` of residue characteristic $\ell$, `L.hv v` is strictly less than $\sqrt{h(x)}$.
- (P5) Some bad place has residue characteristic different from both $2$ and $\ell$.
- (P6) `I.SL2Image x ℓ` holds.

It supplies one bundle $X$ and invariants `inv` on that bundle, with $P(X)$, a `Theorem110Certificate inv`, and a witness of `Nonempty inv.LocalEstimate`. The field also gives $X.\ell=\ell$ and $X.\mathrm{dmod}\le d$. The equality `X.qPilot.logQ = L.heightOther 2 ℓ` gives the local height contribution away from $2$ and $\ell$. With $D(x)=T.\mathrm{logDiff}(T.\mathrm{tripod},x)$ and $C(x)=T.\mathrm{logCond}(T.\mathrm{tripod},x)$, the comparisons are

$$
D(x)=\mathrm{inv.logDtpd},\qquad
\mathrm{inv.logFtpd}\le C(x)\le\mathrm{inv.logFtpd}+\log(2\ell).
$$

[Local conditions and witnesses](Corollary22Inputs_c2.lean#L73)

### `Corollary22Inputs.c2_of_prime_lower_bound`

The Lean entry for the prime-bounded `c2` is `Corollary22Inputs.c2_of_prime_lower_bound`. It takes $1\le d$, the above P7 input `ex`, Chebyshev and prime-counting bounds `cheb` and `pnt`, and an input `h312`. The input `h312` gives `Corollary312Variant X` for every $X$ with $P(X)$ and $N\le X.\ell$. For $x\in W$ outside `I.excCore`, the theorem requires both `I.threshold cheb ≤ I.h x` and $N\le\sqrt{h(x)}$, with $N$ cast to a real. [Pointwise theorem](Corollary22Inputs_c2.lean#L89)

Prime selection gives $\sqrt{h(x)}\le\ell$. Combining the two real inequalities gives the natural-number inequality $N\le\ell$. The proof passes it to `ex.thetaData` with (P2), (P3), (P5), and (P6). It uses the absence of an $\ell$-cyclic subgroup in (P4) to prove (P6). The returned equality $X.\ell=\ell$ transfers $N\le\ell$ to $N\le X.\ell$. The proof applies `h312` to this $X$ and uses its certificate and local estimate in `inv.theorem110`. [Prime selection](Corollary22Inputs_c2.lean#L145) · [Prime identity and variant](Corollary22Inputs_c2.lean#L232)

With $\varepsilon=\mathrm{epsilonE}(\mathrm{deltaBound}(d),h(x))$, the theorem gives

$$
\frac{h(x)}6\le (1+\varepsilon)\bigl(D(x)+C(x)\bigr)+40\,\mathrm{pnt}.\eta+\frac{I.B}{3},
\qquad
\varepsilon\le1,
\qquad
0\le D(x)+C(x).
$$

The original `Corollary22Inputs.c2` uses this entry with $N=0$. Its P7 and `h312` inputs supply the corresponding hypotheses, and $\sqrt{h(x)}\ge0$ supplies the height condition for $N=0$. [Estimate](Corollary22Inputs_c2.lean#L100) · [Zero-bound specialization](Corollary22Inputs_c2.lean#L272)

### Northcott finiteness for fixed \(K,d\)

The theorem `canonicalCorollary22HighHeightEstimate_of_thetaDataExistenceAtLeast` takes `minimum : CompactlyBounded → ℕ → ℕ`. It builds $I$ from `curveInputs_from_source` for the fixed family. It takes P7 and `h312` inputs for that family and its lower bound. After fixing $K,d$, use $N=\mathrm{minimum}(K,d)$ for all points in $W$. The proof uses `I.northcott` at the real height cutoff $N^2$. It takes the union

$$
E=(\mathrm{I.excCore}\cap W)\ \cup\ \{x\in W\mid h(x)\le N^2\}.
$$

Core finiteness gives finiteness of the first set. Northcott finiteness gives finiteness of the second set, including its boundary $h(x)=N^2$. For $x\in W\setminus E$, we have $x\notin\mathrm{I.excCore}$ and $N^2<h(x)$. This gives $N\le\sqrt{h(x)}$. [Family inputs](Source_TripodCanonicalCorollary22PrimeBound.lean#L31) · [Finite exceptional set](Source_TripodCanonicalCorollary22PrimeBound.lean#L47)

The canonical theorem reports `I.threshold cheb` as its height threshold and $40\,\mathrm{pnt}.\eta+I.B/3$ as its additive constant. To apply the pointwise theorem, it rewrites the height using `I.h x = auxiliaryHeight x`. The `statementII_of_thetaDataExistenceAtLeast` theorem uses the canonical estimate with the explicit Chebyshev and prime-counting bounds. It takes both the family P7 hypothesis and `h312` at the supplied bounds. [Canonical estimate](Source_TripodCanonicalCorollary22PrimeBound.lean#L52) · [StatementII composition](Source_TripodCanonicalCorollary22PrimeBound.lean#L73)

## 简体中文

### `ThetaDataExistenceAtLeast`

固定高度理论 $T$、几何接口 $AG,TG$、紧有界数据 $K$ 和自然数次数界 $d$。令 $W=T.\mathrm{cbsSet}(K)\cap T.\mathrm{ptLE}(T.\mathrm{tripod},d)$，以 $h(x)=I.h(x)$ 表示推论 2.2 的输入 $I$ 给出的高度。取自然数 $N$，即 Lean 中的 `minimum`，以及推论 3.12 变体数据上的谓词 $P$。 [结构与参数](Corollary22Inputs_c2.lean#L69)

`ThetaDataExistenceAtLeast N P I` 的 `thetaData` 字段适用于 `I.excCore` 外的每个 $x\in W$，以及满足 $7\le\ell$ 和 $N\le\ell$ 的每个素数 $\ell$。记 `L = I.localData x hx` 为该点的局部数据。该字段需要以下条件。

- (P2) 对 `L.bad` 中每个位，$\ell$ 不整除局部阶数 `L.hv v`。
- (P3) 对 `L.bad` 中每个剩余特征为 $\ell$ 的位，`L.hv v` 严格小于 $\sqrt{h(x)}$。
- (P5) 存在一个坏位，其剩余特征同时异于 $2$ 和 $\ell$。
- (P6) `I.SL2Image x ℓ` 成立。

它给出一个数据包 $X$ 及该数据包上的不变量 `inv`，并给出 $P(X)$、`Theorem110Certificate inv` 和 `Nonempty inv.LocalEstimate` 的见证。它还给出 $X.\ell=\ell$ 和 $X.\mathrm{dmod}\le d$。等式 `X.qPilot.logQ = L.heightOther 2 ℓ` 给出 $2$ 和 $\ell$ 以外的局部高度贡献。记 $D(x)=T.\mathrm{logDiff}(T.\mathrm{tripod},x)$、$C(x)=T.\mathrm{logCond}(T.\mathrm{tripod},x)$，则有

$$
D(x)=\mathrm{inv.logDtpd},\qquad
\mathrm{inv.logFtpd}\le C(x)\le\mathrm{inv.logFtpd}+\log(2\ell).
$$

[局部条件与见证](Corollary22Inputs_c2.lean#L73)

### `Corollary22Inputs.c2_of_prime_lower_bound`

带素数下界的 `c2` 在 Lean 中的入口是 `Corollary22Inputs.c2_of_prime_lower_bound`。它接受 $1\le d$、上述 P7 输入 `ex`、Chebyshev 界 `cheb`、素数计数界 `pnt` 及输入 `h312`。`h312` 对每个满足 $P(X)$ 和 $N\le X.\ell$ 的 $X$ 给出 `Corollary312Variant X`。对 `I.excCore` 外的 $x\in W$，定理同时要求 `I.threshold cheb ≤ I.h x` 和 $N\le\sqrt{h(x)}$，其中 $N$ 在后一不等式中转为实数。 [逐点定理](Corollary22Inputs_c2.lean#L89)

素数选择给出 $\sqrt{h(x)}\le\ell$。合并两个实数不等式，得到自然数不等式 $N\le\ell$。证明把它与 (P2)、(P3)、(P5)、(P6) 一同传给 `ex.thetaData`。证明用 (P4) 中不存在 $\ell$-循环子群这一条件得到 (P6)。返回的等式 $X.\ell=\ell$ 将 $N\le\ell$ 转为 $N\le X.\ell$。证明把 `h312` 用于这个 $X$，并在 `inv.theorem110` 中使用其证书和局部估计。 [素数选择](Corollary22Inputs_c2.lean#L145) · [素数等式与变体](Corollary22Inputs_c2.lean#L232)

令 $\varepsilon=\mathrm{epsilonE}(\mathrm{deltaBound}(d),h(x))$，定理给出

$$
\frac{h(x)}6\le (1+\varepsilon)\bigl(D(x)+C(x)\bigr)+40\,\mathrm{pnt}.\eta+\frac{I.B}{3},
\qquad
\varepsilon\le1,
\qquad
0\le D(x)+C(x).
$$

原入口 `Corollary22Inputs.c2` 取 $N=0$ 调用这一定理。原有的 P7 和 `h312` 输入提供相应的假设，而 $\sqrt{h(x)}\ge0$ 提供 $N=0$ 时的高度条件。 [估计式](Corollary22Inputs_c2.lean#L100) · [零下界特化](Corollary22Inputs_c2.lean#L272)

### 固定 \(K,d\) 后的 Northcott 有限性

定理 `canonicalCorollary22HighHeightEstimate_of_thetaDataExistenceAtLeast` 接受 `minimum : CompactlyBounded → ℕ → ℕ`。它用 `curveInputs_from_source` 构造固定族的 $I$，并接收该族在所给下界上的 P7 和 `h312` 输入。固定 $K,d$ 后，$W$ 中的所有点共用 $N=\mathrm{minimum}(K,d)$。证明以实数高度界 $N^2$ 调用 `I.northcott`，并取并集

$$
E=(\mathrm{I.excCore}\cap W)\ \cup\ \{x\in W\mid h(x)\le N^2\}.
$$

核心例外的有限性给出第一部分有限。Northcott 有限性给出第二部分有限，其中包含边界 $h(x)=N^2$。若 $x\in W\setminus E$，则 $x\notin\mathrm{I.excCore}$ 且 $N^2<h(x)$，从而 $N\le\sqrt{h(x)}$。 [族的输入](Source_TripodCanonicalCorollary22PrimeBound.lean#L31) · [有限例外集](Source_TripodCanonicalCorollary22PrimeBound.lean#L47)

规范定理返回的高度阈值是 `I.threshold cheb`，加法常数是 $40\,\mathrm{pnt}.\eta+I.B/3$。应用逐点定理时，证明用 `I.h x = auxiliaryHeight x` 改写高度。`statementII_of_thetaDataExistenceAtLeast` 用显式 Chebyshev 界和显式素数计数界接入这一规范估计。它要求在给定下界上的 P7 族假设和 `h312`。 [规范估计](Source_TripodCanonicalCorollary22PrimeBound.lean#L52) · [StatementII 组合](Source_TripodCanonicalCorollary22PrimeBound.lean#L73)

## 日本語

### `ThetaDataExistenceAtLeast`

高さ理論 $T$、幾何のインターフェース $AG,TG$、コンパクト有界データ $K$、自然数の次数上界 $d$ を固定する。$W=T.\mathrm{cbsSet}(K)\cap T.\mathrm{ptLE}(T.\mathrm{tripod},d)$ と置く。$h(x)=I.h(x)$ は系 2.2 の入力 $I$ が与える高さである。Lean で `minimum` と書く自然数 $N$ と、系 3.12 の変種のデータ上の述語 $P$ を取る。 [構造体とパラメータ](Corollary22Inputs_c2.lean#L69)

`ThetaDataExistenceAtLeast N P I` のフィールド `thetaData` は、`I.excCore` の外の各 $x\in W$ と、$7\le\ell$ かつ $N\le\ell$ を満たす各素数 $\ell$ に適用する。この点の局所データを `L = I.localData x hx` と書く。このフィールドは次の条件を受け取る。

- (P2) `L.bad` の各素点で、$\ell$ は局所位数 `L.hv v` を割り切らない。
- (P3) `L.bad` のうち剰余標数が $\ell$ の各素点で、`L.hv v` は $\sqrt{h(x)}$ より真に小さい。
- (P5) 剰余標数が $2$ とも $\ell$ とも異なる悪い素点が存在する。
- (P6) `I.SL2Image x ℓ` が成り立つ。

このフィールドは一つのデータ $X$ とその上の不変量 `inv` を与える。$P(X)$、`Theorem110Certificate inv`、`Nonempty inv.LocalEstimate` の証拠を与える。さらに $X.\ell=\ell$ と $X.\mathrm{dmod}\le d$ を与える。等式 `X.qPilot.logQ = L.heightOther 2 ℓ` は、$2$ と $\ell$ 以外の局所高さの寄与を与える。$D(x)=T.\mathrm{logDiff}(T.\mathrm{tripod},x)$、$C(x)=T.\mathrm{logCond}(T.\mathrm{tripod},x)$ と書くと、次が成り立つ。

$$
D(x)=\mathrm{inv.logDtpd},\qquad
\mathrm{inv.logFtpd}\le C(x)\le\mathrm{inv.logFtpd}+\log(2\ell).
$$

[局所条件と証拠](Corollary22Inputs_c2.lean#L73)

### `Corollary22Inputs.c2_of_prime_lower_bound`

素数の下界を取る `c2` の Lean での入口は `Corollary22Inputs.c2_of_prime_lower_bound` である。$1\le d$、上記の P7 入力 `ex`、チェビシェフの評価 `cheb`、素数計数関数の評価 `pnt`、および `h312` を受け取る。`h312` は、$P(X)$ と $N\le X.\ell$ を満たす各 $X$ に対して `Corollary312Variant X` を与える。`I.excCore` の外にある $x\in W$ について、定理は `I.threshold cheb ≤ I.h x` と $N\le\sqrt{h(x)}$ の両方を要求する。後者では $N$ を実数に移す。 [点ごとの定理](Corollary22Inputs_c2.lean#L89)

素数選択は $\sqrt{h(x)}\le\ell$ を与える。二つの実数の不等式をつないで、自然数の不等式 $N\le\ell$ を得る。証明はこれを (P2)、(P3)、(P5)、(P6) とともに `ex.thetaData` に渡す。(P6) の証明では、(P4) の $\ell$-巡回部分群が存在しないことを使う。返った等式 $X.\ell=\ell$ により、$N\le\ell$ を $N\le X.\ell$ に移す。この $X$ に `h312` を適用し、その証明書と局所評価を `inv.theorem110` で使う。 [素数選択](Corollary22Inputs_c2.lean#L145) · [素数の等式と変種](Corollary22Inputs_c2.lean#L232)

$\varepsilon=\mathrm{epsilonE}(\mathrm{deltaBound}(d),h(x))$ と置くと、定理は次を与える。

$$
\frac{h(x)}6\le (1+\varepsilon)\bigl(D(x)+C(x)\bigr)+40\,\mathrm{pnt}.\eta+\frac{I.B}{3},
\qquad
\varepsilon\le1,
\qquad
0\le D(x)+C(x).
$$

元の入口 `Corollary22Inputs.c2` は、この定理を $N=0$ として使う。元の P7 と `h312` の入力が対応する仮定を与え、$\sqrt{h(x)}\ge0$ が $N=0$ での高さ条件を与える。 [評価式](Corollary22Inputs_c2.lean#L100) · [下界を零とする特別化](Corollary22Inputs_c2.lean#L272)

### \(K,d\) を固定したときの Northcott 有限性

定理 `canonicalCorollary22HighHeightEstimate_of_thetaDataExistenceAtLeast` は `minimum : CompactlyBounded → ℕ → ℕ` を受け取る。`curveInputs_from_source` から固定した族の $I$ を構成し、その族と下界に対する P7 と `h312` を受け取る。$K,d$ を固定すると、$W$ のすべての点に同じ $N=\mathrm{minimum}(K,d)$ を用いる。証明では実数の高さの上界 $N^2$ に `I.northcott` を適用し、次の和集合を取る。

$$
E=(\mathrm{I.excCore}\cap W)\ \cup\ \{x\in W\mid h(x)\le N^2\}.
$$

コアの例外集合の有限性により、第一の集合が有限である。Northcott 有限性により、第二の集合が有限である。境界 $h(x)=N^2$ も第二の集合に含まれる。$x\in W\setminus E$ なら、$x\notin\mathrm{I.excCore}$ と $N^2<h(x)$ が成り立つ。ここから $N\le\sqrt{h(x)}$ を得る。 [族ごとの入力](Source_TripodCanonicalCorollary22PrimeBound.lean#L31) · [有限な例外集合](Source_TripodCanonicalCorollary22PrimeBound.lean#L47)

標準の定理が返す高さの閾値は `I.threshold cheb` であり、加法定数は $40\,\mathrm{pnt}.\eta+I.B/3$ である。点ごとの定理を使う際に、`I.h x = auxiliaryHeight x` で高さを書き換える。`statementII_of_thetaDataExistenceAtLeast` は、明示的なチェビシェフの評価と素数計数関数の評価で、この標準の評価を使う。与えられた下界ごとに、族の P7 仮定と `h312` を要求する。 [標準の評価](Source_TripodCanonicalCorollary22PrimeBound.lean#L52) · [StatementII の合成](Source_TripodCanonicalCorollary22PrimeBound.lean#L73)
