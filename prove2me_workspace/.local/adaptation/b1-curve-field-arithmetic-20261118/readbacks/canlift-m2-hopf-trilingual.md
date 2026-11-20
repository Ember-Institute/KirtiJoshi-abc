# Hopf 坐标与测度 · Hopf coordinates and measure · Hopf 座標と測度

令 $G=\mathrm{SL}_2(\mathbb R)$，$p=(x,u,s)\in\mathbb R^3$，$\lambda^3$ 为三维勒贝格测度。下式给出 `hopf`、右乘的两组矩阵及 `hopfMeasure` $m$。

$$
H(x,u,s)=
\begin{pmatrix}xe^s&(xu-1)e^{-s}\\ e^s&ue^{-s}\end{pmatrix},
\qquad
n_t=\begin{pmatrix}1&t\\0&1\end{pmatrix},
\qquad
a_\sigma=\begin{pmatrix}e^\sigma&0\\0&e^{-\sigma}\end{pmatrix},
\qquad
m=H_*\lambda^3+(-H)_*\lambda^3.
$$

### 简体中文

`hopf_mul_unip` 和 `hopf_mul_diagA` 分别将右乘 $n_t$ 与 $a_\sigma$ 写成坐标变换 $N_t(x,u,s)=(x,u+e^{2s}t,s)$ 和 $(x,u,s+\sigma)$。对任意可测 $F:G\to[0,\infty]$，它关于 $m$ 的积分在任意左乘、右乘 $n_t$ 或右乘 $a_\sigma$ 下保持不变。

设 $i\in\mathbb H$ 是虚单位对应的上半平面点。对每个可测集 $E\subseteq\mathbb H$，`hopfMeasure_basept` 给出 $m(\{g:g\cdot i\in E\})=\pi\,\operatorname{area}_{\mathbb H}(E)$。`ErgodicMautner` 对有限双曲面积的轨道覆盖集 $F$ 应用该式，证明覆盖权函数的积分有限。

对关于勒贝格测度可积的 $\varphi:\mathbb R^3\to\mathbb R$，`tendsto_lintegral_hopfN` 断言 $\int|\varphi(N_t p)-\varphi(p)|\,d\lambda^3(p)\to0$ 当 $t\to0$。对可测 $\psi:G\to\mathbb R$，若 $\int|\psi|\,dm<\infty$，`tendsto_lintegral_hopfMeasure_unip` 断言 $\int|\psi(gn_t)-\psi(g)|\,dm(g)\to0$ 当 $t\to0$。`ErgodicMautner` 用右乘的不变性和该连续性，将准确的对角右不变性转化为几乎处处的幺幂右不变性。

### English

Let $G=\mathrm{SL}_2(\mathbb R)$, $p=(x,u,s)\in\mathbb R^3$, and let $\lambda^3$ be three-dimensional Lebesgue measure. The formulas above give the chart $H$, two real matrix families, and the measure $m$. Right multiplication by $n_t$ corresponds to $N_t(x,u,s)=(x,u+e^{2s}t,s)$. Right multiplication by $a_\sigma$ corresponds to $(x,u,s+\sigma)$. The $m$-integral of each measurable $F:G\to[0,\infty]$ is invariant under left multiplication by any group element. It is also invariant under right multiplication by $n_t$ and $a_\sigma$.

Let $i$ be the imaginary unit in the upper half-plane $\mathbb H$. For any measurable $E\subseteq\mathbb H$, `hopfMeasure_basept` gives $m(\{g:g\cdot i\in E\})=\pi\,\operatorname{area}_{\mathbb H}(E)$. `ErgodicMautner` applies this identity to a set $F$ of finite hyperbolic area that meets every orbit. It obtains a finite integral for the weight associated with $F$.

For Lebesgue-integrable $\varphi:\mathbb R^3\to\mathbb R$, `tendsto_lintegral_hopfN` gives $\int|\varphi(N_t p)-\varphi(p)|\,d\lambda^3(p)\to0$ as $t\to0$. Let $\psi:G\to\mathbb R$ be measurable and satisfy $\int|\psi|\,dm<\infty$. Then `tendsto_lintegral_hopfMeasure_unip` gives $\int|\psi(gn_t)-\psi(g)|\,dm(g)\to0$ as $t\to0$. `ErgodicMautner` uses right invariance and this continuity to pass from diagonal right invariance to almost-everywhere unipotent right invariance.

### 日本語

$G=\mathrm{SL}_2(\mathbb R)$、$p=(x,u,s)\in\mathbb R^3$ とし、$\lambda^3$ を三次元ルベーグ測度とする。上の式は座標写像 $H$、二つの行列族、および測度 $m$ を与える。$n_t$ による右乗法は $N_t(x,u,s)=(x,u+e^{2s}t,s)$ に対応し、$a_\sigma$ による右乗法は $(x,u,s+\sigma)$ に対応する。任意の可測関数 $F:G\to[0,\infty]$ の $m$ に関する積分は、任意の群元による左乗法と、$n_t$ および $a_\sigma$ による右乗法で不変である。

$i$ を上半平面 $\mathbb H$ 内の虚数単位とする。任意の可測集合 $E\subseteq\mathbb H$ に対し、`hopfMeasure_basept` は $m(\{g:g\cdot i\in E\})=\pi\,\operatorname{area}_{\mathbb H}(E)$ を与える。`ErgodicMautner` はこの等式を、各軌道と交わる双曲面積有限の集合 $F$ に適用して、その重みの積分が有限であることを示す。

ルベーグ可積分関数 $\varphi:\mathbb R^3\to\mathbb R$ に対し、`tendsto_lintegral_hopfN` は $t\to0$ のとき $\int|\varphi(N_t p)-\varphi(p)|\,d\lambda^3(p)\to0$ を与える。可測関数 $\psi:G\to\mathbb R$ が $\int|\psi|\,dm<\infty$ を満たすなら、`tendsto_lintegral_hopfMeasure_unip` により $t\to0$ のとき $\int|\psi(gn_t)-\psi(g)|\,dm(g)\to0$ となる。`ErgodicMautner` は右不変性とこの連続性を用いて、対角行列による右不変性から冪単行列によるほとんど至る所の右不変性を得る。 [HopfCoords](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftHopfCoords.lean:56) · [HopfFinite](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftHopfFinite.lean:240) · [HopfContinuity](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftHopfContinuity.lean:127) · [ErgodicMautner](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftErgodicMautner.lean:171)
