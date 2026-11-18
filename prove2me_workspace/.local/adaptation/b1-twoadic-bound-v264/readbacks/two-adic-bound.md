# English

Let $P$ supply the actual Legendre curves, their arithmetic certificates, and their Tate inputs. Let $K$ be a compactly bounded subset with local bound $c=K.c$ and finite prime support $V=K.V$, where $2\in V$. The local conditions bound the absolute logarithms of $\lambda$ and $\lambda-1$ by $c$ at the specified finite places and at every archimedean place. Here $\lambda$ is the coordinate of a point of the projective line with $0,1,\infty$ removed.

For $x\in K$, let $E_x/F_x=P.\mathrm{curve}(x)$. Let $S_2(x)$ be the set of all finite places of $F_x$ where $E_x$ has multiplicative reduction and the residue characteristic is $2$. For each $w\in S_2(x)$, let $n_w$ be the order of the supplied Tate parameter, and let $f_w$ be the residue degree over $2$. Define the contribution at $2$ by

$$h_2(x)=\frac{\displaystyle\sum_{w\in S_2(x)}n_w f_w\log 2}{[F_x:\mathbb Q]}.$$

This is exactly `(P.localData x).heightEq 2`. The theorem `twoAdicBound P K` proves

$$h_2(x)\leq \max(4c,0)\qquad\text{for every }x\in K.$$

The proof first gives the stronger bound $h_2(x)\leq4c$. At each contributing place, the Legendre formula for the $j$-invariant bounds the Tate order using the valuations of $\lambda$ and $\lambda-1$. Transport to the corresponding place of the intermediate field isomorphic to $\mathbb Q(\lambda)$ preserves the required local bounds and records the ramification and residue-degree factors. Thus the local term is at most $4c[F_{x,w}:\mathbb Q_2]$. Summing the local degrees and dividing by $[F_x:\mathbb Q]$ gives $4c$. Taking the maximum gives a nonnegative bound even when $K$ is empty. No bound on the degree of $x$ is required.

In Mochizuki's IUT IV, Corollary 2.2(i), the all-primes q-height and the q-height away from $2$ differ by a bounded quantity on the specified subset. The proof of Corollary 2.2(ii) uses that bounded difference in its final height estimate. The theorem above gives an explicit bound for the unscaled contribution $h_2$ in the stated local normalization.

# 简体中文

设 $P$ 提供实际的 Legendre 曲线、相应算术证书和 Tate 输入。设 $K$ 是一个【译名待定：compactly bounded subset】，其局部界为 $c=K.c$，有限素数支集为 $V=K.V$，且 $2\in V$。局部条件要求：在指定有限素位及所有阿基米德位处，$\lambda$ 与 $\lambda-1$ 的绝对值之对数的绝对值均不超过 $c$。这里 $\lambda$ 是射影直线去掉 $0,1,\infty$ 后的点坐标。

对 $x\in K$，令 $E_x/F_x=P.\mathrm{curve}(x)$。记 $S_2(x)$ 为 $F_x$ 的所有满足以下条件的有限素位：$E_x$ 在该处具有乘法约化，且剩余特征为 $2$。对每个 $w\in S_2(x)$，记所提供 Tate 参数的阶为 $n_w$，在 $2$ 上方的剩余次数为 $f_w$。定义素数 $2$ 处的高度贡献为

$$h_2(x)=\frac{\displaystyle\sum_{w\in S_2(x)}n_w f_w\log 2}{[F_x:\mathbb Q]}.$$

这恰是 `(P.localData x).heightEq 2`。定理 `twoAdicBound P K` 证明

$$h_2(x)\leq\max(4c,0)\qquad(x\in K)。$$

证明先给出更强的界 $h_2(x)\leq4c$。在每个有贡献的素位处，利用 Legendre 曲线的 $j$ 不变量公式，以 $\lambda$ 和 $\lambda-1$ 的赋值控制 Tate 参数的阶。将这些数据移到与 $\mathbb Q(\lambda)$ 同构的中间域的对应素位时，保留所需局部界，并计入分歧指数与剩余次数。因此，每个局部项至多为 $4c[F_{x,w}:\mathbb Q_2]$。对局部次数求和，再除以 $[F_x:\mathbb Q]$，得到 $4c$。取最大值使上界在 $K$ 为空时仍为非负。这里不要求点 $x$ 的次数有上界。

Mochizuki《IUT IV》推论 2.2(i) 比较包含全部有限素位的 q-高度与去掉素数 $2$ 后的 q-高度，说明二者在指定子集上的差有界。推论 2.2(ii) 的证明在最终高度估计中使用这一有界差。上述定理在所述局部归一化下，为未经 $1/6$ 缩放的贡献 $h_2$ 给出显式上界。

# 日本語

$P$ が実際の Legendre 曲線、その算術的証明書、および Tate 入力を与えるとする。$K$ を局所上限 $c=K.c$ と有限素数台 $V=K.V$ をもつコンパクト有界部分集合とし、$2\in V$ とする。局所条件は、指定した有限素点とすべてのアルキメデス素点において、$\lambda$ と $\lambda-1$ の絶対値の対数の絶対値が $c$ 以下であることを要求する。$\lambda$ は、射影直線から $0,1,\infty$ を除いた曲線上の点の座標である。

$x\in K$ に対し、$E_x/F_x=P.\mathrm{curve}(x)$ とおく。$S_2(x)$ を、$E_x$ が乗法的還元をもち、剰余標数が $2$ である $F_x$ のすべての有限素点の集合とする。各 $w\in S_2(x)$ に対し、与えられた Tate パラメータの位数を $n_w$、$2$ の上の剰余次数を $f_w$ とする。素数 $2$ における高さの寄与を

$$h_2(x)=\frac{\displaystyle\sum_{w\in S_2(x)}n_w f_w\log 2}{[F_x:\mathbb Q]}$$

と定める。これは正確に `(P.localData x).heightEq 2` である。定理 `twoAdicBound P K` は

$$h_2(x)\leq\max(4c,0)\qquad(x\in K)$$

を証明する。まず、より強い評価 $h_2(x)\leq4c$ を示す。寄与する各素点では、Legendre 曲線の $j$ 不変量の公式により、$\lambda$ と $\lambda-1$ の付値から Tate パラメータの位数を評価する。 $\mathbb Q(\lambda)$ と同型な中間体の対応する素点へ移す際、必要な局所上限を保ち、分岐指数と剰余次数を記録する。その結果、各局所項は $4c[F_{x,w}:\mathbb Q_2]$ 以下となる。局所次数を足し、$[F_x:\mathbb Q]$ で割ると $4c$ を得る。最大値を取ることで、$K$ が空の場合にも非負の上限を得る。点 $x$ の次数上限は要求しない。

Mochizuki の IUT IV、系 2.2(i) は、すべての有限素点を含む q-高さと、素数 $2$ を除いた q-高さとの差が、指定した部分集合上で有界であることを述べる。系 2.2(ii) の証明は、この有界差を最終的な高さの評価に用いる。上の定理は、示された局所正規化において、$1/6$ 倍する前の寄与 $h_2$ に明示的な上限を与える。
