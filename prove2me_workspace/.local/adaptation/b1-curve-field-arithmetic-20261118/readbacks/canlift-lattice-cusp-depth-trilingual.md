# Lean 定理复述 · Lean theorem readback · Lean 定理の読み取り

下文取 $t\in\mathbb H$ 及其周期对的覆盖数据 $U$。记 $\Gamma=U.\mathrm{deckGroup}$，$\psi=U.\psi$，$C=\mathrm{Cm}\,U$，$\Sigma(s)=\mathrm{Sig}\,U\,s$，$e_0=e_0(U)$。$d_U(\tau)$ 是双曲距离 $\operatorname{dist}_{\mathbb H}(e_0,\gamma\cdot\tau)$ 对 $\gamma\in\Gamma$ 的下确界。记 $B_r=\{w\in\mathbb C:|w|<r\}$，$H_r(t)=\{s\in\mathbb C:\operatorname{Re}s<\log r_0(t)\}$，$D^*(t)=B_{r_0(t)}\setminus\{0\}$。在 $H_r(t)$ 上，提升满足 $\psi(\Sigma(s))=e^s$。复对数写作 $\operatorname{Log}$，实对数写作 $\log$。

Fix $t\in\mathbb H$ and covering data $U$ for its period pair. Use $\Gamma=U.\mathrm{deckGroup}$, $\psi=U.\psi$, $C=\mathrm{Cm}\,U$, $\Sigma(s)=\mathrm{Sig}\,U\,s$, and $e_0=e_0(U)$. The depth $d_U(\tau)$ is the infimum over $\gamma\in\Gamma$ of the hyperbolic distance $\operatorname{dist}_{\mathbb H}(e_0,\gamma\cdot\tau)$. Write $B_r$ for the open disk of radius $r$ about zero, $H_r(t)$ for the left half-plane $\{s\in\mathbb C:\operatorname{Re}s<\log r_0(t)\}$, and $D^*(t)$ for $B_{r_0(t)}\setminus\{0\}$. On $H_r(t)$ the lift satisfies $\psi(\Sigma(s))=e^s$. Use $\operatorname{Log}$ for Lean's complex logarithm and $\log$ for the real logarithm.

$t\in\mathbb H$ と、その周期対に対する被覆データ $U$ を固定する。$\Gamma=U.\mathrm{deckGroup}$ を被覆変換群とし、$\psi=U.\psi$、$C=\mathrm{Cm}\,U$、$\Sigma(s)=\mathrm{Sig}\,U\,s$、$e_0=e_0(U)$ と書く。深さ $d_U(\tau)$ は、$\gamma\in\Gamma$ に対する双曲距離 $\operatorname{dist}_{\mathbb H}(e_0,\gamma\cdot\tau)$ の下限である。$B_r$ は原点を中心とする半径 $r$ の開円板、$H_r(t)$ は左半平面 $\{s\in\mathbb C:\operatorname{Re}s<\log r_0(t)\}$、$D^*(t)$ は穴あき円板 $B_{r_0(t)}\setminus\{0\}$ を表す。$H_r(t)$ では持ち上げは $\psi(\Sigma(s))=e^s$ を満たす。複素対数を $\operatorname{Log}$、実対数を $\log$ と書く。

## CuspCoordinates

**中文**　`differentiableOn_comp_log` 设 $E:\mathbb C\to\mathbb C$ 在 $H_r(t)$ 上全纯，且对其中每个 $s$ 有 $E(s+2\pi i)=E(s)$。则 $w\mapsto E(\operatorname{Log}w)$ 在 $D^*(t)$ 上全纯，并且对每个 $s\in H_r(t)$ 有 $E(\operatorname{Log}(e^s))=E(s)$。`exists_conj_translation` 给出 $M\in\mathrm{SL}_2(\mathbb R)$ 和实数 $\kappa\ne0$，使 $N=M^{-1}CM$ 对所有 $z\in\mathbb H$ 按 $z\mapsto z+\kappa$ 作用。对每个 $M$，归一化坐标 $\tau_M(s)=M^{-1}\cdot\Sigma(s)$ 对所有 $s\in\mathbb C$ 有正虚部，并在 $H_r(t)$ 上全纯。只要 $N$ 按上述平移作用，对每个 $m\in\mathbb Z$ 有 $N^m\cdot z=z+m\kappa$，对每个 $s\in H_r(t)$ 有 $\tau_M(s+2\pi i)=\tau_M(s)+\kappa$。

**English**　`differentiableOn_comp_log` assumes $E:\mathbb C\to\mathbb C$ is holomorphic on $H_r(t)$ and $E(s+2\pi i)=E(s)$ for every $s$ there. It gives holomorphy of $w\mapsto E(\operatorname{Log}w)$ on $D^*(t)$, and $E(\operatorname{Log}(e^s))=E(s)$ for every $s\in H_r(t)$. `exists_conj_translation` gives $M\in\mathrm{SL}_2(\mathbb R)$ and $\kappa\in\mathbb R\setminus\{0\}$ such that $N=M^{-1}CM$ acts by $z\mapsto z+\kappa$ on every $z\in\mathbb H$. For every $M$, the normalized coordinate $\tau_M(s)=M^{-1}\cdot\Sigma(s)$ has positive imaginary part for every $s\in\mathbb C$ and is holomorphic on $H_r(t)$. Under the translation hypothesis for $N$, its integer powers act by $N^m\cdot z=z+m\kappa$, and $\tau_M(s+2\pi i)=\tau_M(s)+\kappa$ for every $s\in H_r(t)$.

**日本語**　`differentiableOn_comp_log` は、$E:\mathbb C\to\mathbb C$ が $H_r(t)$ 上で正則であり、その中のすべての $s$ について $E(s+2\pi i)=E(s)$ を満たすと仮定する。このとき $w\mapsto E(\operatorname{Log}w)$ は $D^*(t)$ 上で正則で、任意の $s\in H_r(t)$ に対し $E(\operatorname{Log}(e^s))=E(s)$ が成り立つ。`exists_conj_translation` は $M\in\mathrm{SL}_2(\mathbb R)$ と実数 $\kappa\ne0$ の存在を述べる。$N=M^{-1}CM$ は任意の $z\in\mathbb H$ に $z\mapsto z+\kappa$ で作用する。任意の $M$ に対し、正規化座標 $\tau_M(s)=M^{-1}\cdot\Sigma(s)$ の虚部はすべての $s\in\mathbb C$ で正であり、$H_r(t)$ 上で正則である。$N$ が上記の平行移動で作用するとき、任意の $m\in\mathbb Z$ について $N^m\cdot z=z+m\kappa$ となり、任意の $s\in H_r(t)$ について $\tau_M(s+2\pi i)=\tau_M(s)+\kappa$ が成り立つ。

**中文**　对每个 $m\in\mathbb Z$ 和 $\nu\in\mathbb H$，有 $\psi(C^m\cdot\nu)=\psi(\nu)$。对任意 $M$ 及 $N=M^{-1}CM$，还有 $M\cdot(N^m\cdot(M^{-1}\cdot\nu))=C^m\cdot\nu$。$\exp^{-1}(\{1\})$ 是离散集合。若 $S\subseteq\mathbb C$ 预连通，连续函数 $k:S\to\mathbb C$ 对每个 $s\in S$ 满足 $\exp(k(s))=1$，则对所有 $x,y\in S$ 有 $k(x)=k(y)$。

**English**　$\psi(C^m\cdot\nu)=\psi(\nu)$ and $M\cdot(N^m\cdot(M^{-1}\cdot\nu))=C^m\cdot\nu$ hold for every $m\in\mathbb Z$ and $\nu\in\mathbb H$, with the second identity valid for every $M$ and $N=M^{-1}CM$. The fiber $\exp^{-1}(\{1\})$ is discrete. If $S\subseteq\mathbb C$ is preconnected and $k:S\to\mathbb C$ is continuous with $\exp(k(s))=1$ throughout $S$, then $k(x)=k(y)$ for all $x,y\in S$.

**日本語**　任意の $m\in\mathbb Z$ と $\nu\in\mathbb H$ に対して $\psi(C^m\cdot\nu)=\psi(\nu)$ が成り立つ。さらに、任意の $M$ と $N=M^{-1}CM$ について $M\cdot(N^m\cdot(M^{-1}\cdot\nu))=C^m\cdot\nu$ が成り立つ。$\exp^{-1}(\{1\})$ は離散集合である。$S\subseteq\mathbb C$ が前連結であり、連続関数 $k:S\to\mathbb C$ がすべての $s\in S$ で $\exp(k(s))=1$ を満たすなら、任意の $x,y\in S$ について $k(x)=k(y)$ となる。 [CuspCoordinates.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftLatticeCuspCoordinates.lean:31)

## CuspExponential

**中文**　`exists_cusp_exponential` 设 $M\in\mathrm{SL}_2(\mathbb R)$、实数 $\kappa\ne0$，且 $M^{-1}CM$ 对每个 $z\in\mathbb H$ 作用为 $z+\kappa$。存在 $G:\mathbb C\to\mathbb C$，它在整个 $B_{r_0(t)}$ 上全纯，在原点有一阶零点，并且对每个 $s\in H_r(t)$ 满足下式。

**English**　`exists_cusp_exponential` assumes $M\in\mathrm{SL}_2(\mathbb R)$, $\kappa\in\mathbb R\setminus\{0\}$, and $(M^{-1}CM)\cdot z=z+\kappa$ for every $z\in\mathbb H$. There is a function $G:\mathbb C\to\mathbb C$ holomorphic on $B_{r_0(t)}$ with a simple zero at the origin. It satisfies the identity below for every $s\in H_r(t)$.

**日本語**　`exists_cusp_exponential` では $M\in\mathrm{SL}_2(\mathbb R)$、実数 $\kappa\ne0$ とし、任意の $z\in\mathbb H$ について $(M^{-1}CM)\cdot z=z+\kappa$ と仮定する。$B_{r_0(t)}$ 上で正則で原点に単純零点をもつ $G:\mathbb C\to\mathbb C$ が存在し、すべての $s\in H_r(t)$ について次式を満たす。

$$
G(0)=0,\qquad G'(0)\ne0,\qquad
\exp\!\left(\frac{2\pi i\,\tau_M(s)}{|\kappa|}\right)=G(e^s).
$$

[CuspExponential.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftLatticeCuspExponential.lean:30)

## CuspNormalForm

**中文**　`exists_cusp_normalForm` 对给定的 $t,U$ 给出 $M\in\mathrm{SL}_2(\mathbb R)$、实数 $\kappa>0$、$0<r_1\le r_0(t)$、函数 $\phi:\mathbb C\to\mathbb C$ 和实常数 $\Phi$。共轭作用对每个 $z\in\mathbb H$ 为 $z+\kappa$，且对所有 $w\in B_{r_1}$ 有 $|\phi(w)|\le\Phi$。还存在 $G:\mathbb C\to\mathbb C$，在 $B_{r_1}$ 上全纯，在原点有一阶零点。下面的两个恒等式对每个 $\operatorname{Re}s<\log r_1$ 的 $s\in\mathbb C$ 同时成立。

**English**　`exists_cusp_normalForm` gives $M\in\mathrm{SL}_2(\mathbb R)$, a positive real $\kappa$, $0<r_1\le r_0(t)$, a function $\phi:\mathbb C\to\mathbb C$, and a real constant $\Phi$, for the given $t,U$. The conjugate acts by $z+\kappa$ for every $z\in\mathbb H$, and $|\phi(w)|\le\Phi$ for every $w\in B_{r_1}$. There is a $G:\mathbb C\to\mathbb C$ holomorphic on $B_{r_1}$ with a simple zero at the origin. Both identities below hold for every $s\in\mathbb C$ with $\operatorname{Re}s<\log r_1$.

**日本語**　`exists_cusp_normalForm` は、与えられた $t,U$ に対して $M\in\mathrm{SL}_2(\mathbb R)$、正の実数 $\kappa$、$0<r_1\le r_0(t)$、関数 $\phi:\mathbb C\to\mathbb C$、実定数 $\Phi$ の存在を述べる。共役変換は任意の $z\in\mathbb H$ に $z+\kappa$ で作用し、任意の $w\in B_{r_1}$ に対して $|\phi(w)|\le\Phi$ が成り立つ。さらに、$B_{r_1}$ 上で正則で原点に単純零点をもつ $G:\mathbb C\to\mathbb C$ が存在する。$\operatorname{Re}s<\log r_1$ を満たすすべての $s\in\mathbb C$ について、次の二つの式が成り立つ。

$$
\tau_M(s)=\frac{\kappa}{2\pi i}\bigl(s+\phi(e^s)\bigr),\qquad
\exp\!\left(\frac{2\pi i\,\tau_M(s)}{\kappa}\right)=G(e^s).
$$

[CuspNormalForm.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftLatticeCuspNormalForm.lean:27)

## CuspHeight

**中文**　`CuspData U` 收录上述标准形的数据及性质，`cuspData U` 给出一个选择。对任意这种数据 $c$，`exists_height` 给出一个实数 $h$，使每个满足 $\operatorname{Im}((c.M)^{-1}\cdot\nu)>h$ 的 $\nu\in\mathbb H$ 都可写成 $C^k\cdot\Sigma(\operatorname{Log}w)$，其中 $0<|w|<c.r_1$，$k\in\mathbb Z$ 可依赖于 $\nu$。`exists_orbit_height` 给出一个实数 $h$，使对每个 $\gamma\in\Gamma$ 有 $\operatorname{Im}((c.M)^{-1}\cdot(\gamma\cdot e_0))\le h$。`τ'_im`、`τ'_re` 在 $\operatorname{Re}s<\log(c.r_1)$ 时分别给出下列虚部和实部公式。

**English**　`CuspData U` packages the normal form and its properties, and `cuspData U` chooses such data. For any $c$ of this type, `exists_height` finds a real $h$ such that every $\nu\in\mathbb H$ with $\operatorname{Im}((c.M)^{-1}\cdot\nu)>h$ equals $C^k\cdot\Sigma(\operatorname{Log}w)$ for some $0<|w|<c.r_1$ and $k\in\mathbb Z$. These witnesses may depend on $\nu$. `exists_orbit_height` finds a real $h$ with $\operatorname{Im}((c.M)^{-1}\cdot(\gamma\cdot e_0))\le h$ for every $\gamma\in\Gamma$. For $\operatorname{Re}s<\log(c.r_1)$, `τ'_im` and `τ'_re` give the imaginary and real parts below.

**日本語**　`CuspData U` は標準形のデータと性質をまとめた型であり、`cuspData U` はそのようなデータを一つ選ぶ。任意の $c$ に対し、`exists_height` は実数 $h$ の存在を述べる。$\operatorname{Im}((c.M)^{-1}\cdot\nu)>h$ を満たす任意の $\nu\in\mathbb H$ について、$0<|w|<c.r_1$ を満たす $w$ と $k\in\mathbb Z$ が存在し、$\nu=C^k\cdot\Sigma(\operatorname{Log}w)$ となる。これらの $w,k$ は $\nu$ に依存してよい。`exists_orbit_height` は任意の $\gamma\in\Gamma$ について $\operatorname{Im}((c.M)^{-1}\cdot(\gamma\cdot e_0))\le h$ となる実数 $h$ の存在を述べる。$\operatorname{Re}s<\log(c.r_1)$ のとき、`τ'_im` と `τ'_re` はそれぞれ次の虚部と実部の式を与える。

$$
\operatorname{Im}\tau_{c.M}(s)=\frac{c.\kappa}{2\pi}
\bigl(-\operatorname{Re}s-\operatorname{Re}(c.\phi(e^s))\bigr),\qquad
\operatorname{Re}\tau_{c.M}(s)=\frac{c.\kappa}{2\pi}
\bigl(\operatorname{Im}s+\operatorname{Im}(c.\phi(e^s))\bigr).
$$

**中文**　若 $0<|w|<c.r_1$，则 $\operatorname{Re}\operatorname{Log}w<\log(c.r_1)$ 且 $w\in D^*(t)$。

**English**　If $0<|w|<c.r_1$, then $\operatorname{Re}\operatorname{Log}w<\log(c.r_1)$ and $w\in D^*(t)$.

**日本語**　$0<|w|<c.r_1$ なら $\operatorname{Re}\operatorname{Log}w<\log(c.r_1)$ かつ $w\in D^*(t)$ である。 [CuspHeight.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftLatticeCuspHeight.lean:26)

## DepthDomain

**中文**　对每个 $\tau\in\mathbb H$ 和 $\gamma\in\Gamma$，`depth_le` 给出 $d_U(\tau)\le\operatorname{dist}_{\mathbb H}(\gamma\cdot\tau,e_0)$，`depth_smul` 给出 $d_U(\gamma\cdot\tau)=d_U(\tau)$。`le_depth` 断言，若实数 $r$ 是所有这些距离的下界，则 $r\le d_U(\tau)$。令 $K_\varepsilon$ 由闭平行四边形 $\{x+yt:0\le x,y\le1\}$ 中距四个角 $0,1,t,1+t$ 均至少为 $\varepsilon$ 的点组成。四个角都在周期格中。$K_\varepsilon$ 对每个实数 $\varepsilon$ 都紧，当 $\varepsilon>0$ 时包含于 $K(t)$。对 $K(t)$ 中的点 $k$，$s_K(U,k)$ 是满足 $\psi(s_K(U,k))=k$ 的选定提升。`compact_or_cusp` 设 $\varepsilon\le r_0(t)$，对每个 $\tau\in\mathbb H$ 给出如下析取式，各分支各自量化 $\gamma$。

**English**　For every $\tau\in\mathbb H$ and $\gamma\in\Gamma$, `depth_le` gives $d_U(\tau)\le\operatorname{dist}_{\mathbb H}(\gamma\cdot\tau,e_0)$, and `depth_smul` gives $d_U(\gamma\cdot\tau)=d_U(\tau)$. `le_depth` states that any real lower bound $r$ for all these distances satisfies $r\le d_U(\tau)$. The set $K_\varepsilon$ consists of the points of the closed parallelogram $\{x+yt:0\le x,y\le1\}$ at distance at least $\varepsilon$ from all four corners $0,1,t,1+t$. All four corners belong to the period lattice. The set $K_\varepsilon$ is compact for each real $\varepsilon$, and lies in $K(t)$ when $\varepsilon>0$. For $k\in K(t)$, $s_K(U,k)$ is the chosen lift with $\psi(s_K(U,k))=k$. Given $\varepsilon\le r_0(t)$, `compact_or_cusp` gives the disjunction below for each $\tau\in\mathbb H$, with $\gamma$ quantified in each branch.

**日本語**　任意の $\tau\in\mathbb H$ と $\gamma\in\Gamma$ に対し、`depth_le` は $d_U(\tau)\le\operatorname{dist}_{\mathbb H}(\gamma\cdot\tau,e_0)$ を、`depth_smul` は $d_U(\gamma\cdot\tau)=d_U(\tau)$ を与える。`le_depth` は、これらの距離すべての実数の下界 $r$ に対して $r\le d_U(\tau)$ が成り立つことを述べる。閉平行四辺形 $\{x+yt:0\le x,y\le1\}$ のうち、四頂点 $0,1,t,1+t$ のどれからも距離が $\varepsilon$ 以上の点を $K_\varepsilon$ とする。四頂点はいずれも周期格子に属する。任意の実数 $\varepsilon$ に対し $K_\varepsilon$ はコンパクトであり、$\varepsilon>0$ なら $K(t)$ に含まれる。$k\in K(t)$ に対し、$s_K(U,k)$ は $\psi(s_K(U,k))=k$ を満たすように選んだ持ち上げである。$\varepsilon\le r_0(t)$ のもとで、`compact_or_cusp` は任意の $\tau\in\mathbb H$ に対して次の選言を与える。$\gamma$ は各場合で個別に量化される。

$$
\bigl(\exists\gamma\in\Gamma\ \exists k\in K_\varepsilon:\ \gamma\cdot\tau=s_K(U,k)\bigr)
\ \lor\
\bigl(\exists\gamma\in\Gamma\ \exists w\in\mathbb C,\ 0<|w|<\varepsilon:\
       \gamma\cdot\tau=\Sigma(\operatorname{Log}w)\bigr).
$$

[Cusp decomposition and truncated parallelogram](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftLatticeDepthDomain.lean:118)

## DepthGeometry

**中文**　`im_le_bound_mul_exp_depth` 给定任意 $M\in\mathrm{SL}_2(\mathbb R)$ 和 $H>0$，若每个 $\gamma\in\Gamma$ 都满足 $\operatorname{Im}(M^{-1}\cdot(\gamma\cdot e_0))\le H$，则对每个 $\tau\in\mathbb H$ 都有 $\operatorname{Im}(M^{-1}\cdot\tau)\le H\exp(d_U(\tau))$。`exp_depth_le_of_cusp_coordinates` 对任意 $M,\tau,R$ 设 $z=M^{-1}\cdot\tau$、$z_0=M^{-1}\cdot e_0$。若 $|\operatorname{Re}z-\operatorname{Re}z_0|\le R$ 且 $\operatorname{Im}z\ge1$，则深度的指数满足下列上界。

**English**　`im_le_bound_mul_exp_depth` takes any $M\in\mathrm{SL}_2(\mathbb R)$ and $H>0$ with $\operatorname{Im}(M^{-1}\cdot(\gamma\cdot e_0))\le H$ for every $\gamma\in\Gamma$. It gives $\operatorname{Im}(M^{-1}\cdot\tau)\le H\exp(d_U(\tau))$ for every $\tau\in\mathbb H$. For any $M,\tau,R$, `exp_depth_le_of_cusp_coordinates` puts $z=M^{-1}\cdot\tau$ and $z_0=M^{-1}\cdot e_0$. If $|\operatorname{Re}z-\operatorname{Re}z_0|\le R$ and $\operatorname{Im}z\ge1$, it gives the following upper bound on the exponential of depth.

**日本語**　`im_le_bound_mul_exp_depth` では、任意の $M\in\mathrm{SL}_2(\mathbb R)$ と $H>0$ に対し、すべての $\gamma\in\Gamma$ について $\operatorname{Im}(M^{-1}\cdot(\gamma\cdot e_0))\le H$ と仮定する。このとき任意の $\tau\in\mathbb H$ に対し $\operatorname{Im}(M^{-1}\cdot\tau)\le H\exp(d_U(\tau))$ が成り立つ。`exp_depth_le_of_cusp_coordinates` では任意の $M,\tau,R$ に対して $z=M^{-1}\cdot\tau$、$z_0=M^{-1}\cdot e_0$ とおく。$|\operatorname{Re}z-\operatorname{Re}z_0|\le R$ かつ $\operatorname{Im}z\ge1$ なら、深さの指数に対して次の上界を得る。

$$
\exp(d_U(\tau))\le
\frac{R^2+(\operatorname{Im}z_0)^2}{\operatorname{Im}z_0}
+\frac{\operatorname{Im}z}{\operatorname{Im}z_0}.
$$

[DepthGeometry.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftLatticeDepthGeometry.lean:25)

## CuspGrowth

**中文**　`cusp_estimates` 对任意标准形数据 $c$ 给出 $0<\varepsilon\le c.r_1$ 及实常数 $A,B$。同一对常数对每个 $0<|w|<\varepsilon$ 同时给出下列两式，其中 $P(w)=|\wp_t(w)|$，$D(w)=\exp(d_U(\Sigma(\operatorname{Log}w)))$，$\wp_t$ 是该周期对的 Weierstrass $\wp$ 函数。

**English**　For any normal-form data $c$, `cusp_estimates` gives $0<\varepsilon\le c.r_1$ and real $A,B$. The same constants give both inequalities below for every $w$ with $0<|w|<\varepsilon$. Here $P(w)=|\wp_t(w)|$, with $\wp_t$ the Weierstrass function for the period pair, and $D(w)=\exp(d_U(\Sigma(\operatorname{Log}w)))$.

**日本語**　`cusp_estimates` は任意の標準形データ $c$ に対し、$0<\varepsilon\le c.r_1$ と実定数 $A,B$ の存在を述べる。$0<|w|<\varepsilon$ を満たすすべての $w$ について、次の二つの不等式が同じ定数で成り立つ。ここで $P(w)=|\wp_t(w)|$ とし、$\wp_t$ は周期対の Weierstrass の $\wp$ 関数、$D(w)=\exp(d_U(\Sigma(\operatorname{Log}w)))$ である。

$$
\log(1+P(w))\le A D(w)+B,\qquad
D(w)\le A\log(2+P(w))+B.
$$

[CuspGrowth.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftLatticeCuspGrowth.lean:78)

## DepthGrowth

**中文**　令 $F(\tau)=\wp_t(\psi(\tau))$，即 `wpΨ U`。`wpΨ_smul` 断言对每个 $\gamma\in\Gamma$ 及 $\tau\in\mathbb H$ 有 $F(\gamma\cdot\tau)=F(\tau)$。`exists_growth` 给出实常数 $A\ge0,B$，使下列两个估计对整个上半平面的每个 $\tau$ 同时成立。`exists_poly_bound_smul` 对任意 $\sigma\in\mathrm{SL}_2(\mathbb R)$，若 $\Gamma$ 与 $\sigma\Gamma\sigma^{-1}$ 可公度，即其交集在二者中都有有限指数，则 $\tau\mapsto|F(\sigma\cdot\tau)|$ 相对于 $F$ 多项式有界，结论使用 `PolyBdd` 表述。

**English**　Let $F(\tau)=\wp_t(\psi(\tau))$, the function `wpΨ U`. `wpΨ_smul` gives $F(\gamma\cdot\tau)=F(\tau)$ for every $\gamma\in\Gamma$ and $\tau\in\mathbb H$. `exists_growth` gives real $A\ge0$ and $B$ for which both estimates below hold throughout $\mathbb H$. For every $\sigma\in\mathrm{SL}_2(\mathbb R)$ in the commensurator of $\Gamma$ (so $\Gamma\cap\sigma\Gamma\sigma^{-1}$ has finite index in both subgroups), `exists_poly_bound_smul` gives polynomial boundedness of $\tau\mapsto|F(\sigma\cdot\tau)|$ relative to $F$, expressed by `PolyBdd`.

**日本語**　`wpΨ U` で表す関数を $F(\tau)=\wp_t(\psi(\tau))$ とする。`wpΨ_smul` は、任意の $\gamma\in\Gamma$ と $\tau\in\mathbb H$ に対して $F(\gamma\cdot\tau)=F(\tau)$ が成り立つことを述べる。`exists_growth` は実定数 $A\ge0,B$ の存在を述べ、上半平面のすべての $\tau$ に対して次の二つの不等式が成り立つ。`exists_poly_bound_smul` では $\sigma\in\mathrm{SL}_2(\mathbb R)$ に対し、$\Gamma\cap\sigma\Gamma\sigma^{-1}$ が両方の部分群で有限指数だと仮定する。このとき $\tau\mapsto|F(\sigma\cdot\tau)|$ は $F$ に関して多項式で抑えられ、結論は `PolyBdd` で表される。

$$
\log(1+|F(\tau)|)\le A\exp(d_U(\tau))+B,\qquad
\exp(d_U(\tau))\le A\log(2+|F(\tau)|)+B.
$$

`PolyBdd (wpΨ U) (fun τ ↦ ‖wpΨ U (σ • τ)‖)`. [DepthGrowth.lean](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftLatticeDepthGrowth.lean:39)

## 术语与陈述边界 · Terminology and scope · 用語と主張の範囲

- `PolyBdd` 在这些文件中仅以谓词出现。要确定多项式界怎样量化常数与次数，以及如何归一化自变量，需要查阅该谓词的定义。此处保留准确的谓词应用。 / The quantifiers over constants and degrees and the normalization of the polynomial argument require the definition of `PolyBdd`. The eight files give the predicate application. / 多項式の定数と次数の量化、および引数の正規化を確定するには `PolyBdd` の定義が必要である。ここでは命題の適用形を記した。 [Polynomial boundedness](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftLatticeDepthGrowth.lean:103)
- `Cm U` 可按这些文件称为指定的尖点单值变换（monodromy）。已读的声明给出其共轭后的 Möbius **作用**。该证明中的矩阵迹为 $-2$。`ψ_Cm_zpow_smul` 中的逐点相等是对 $C^m$ 的，`wpΨ_smul` 才把 $\wp_t\circ\psi$ 的不变性量化到整个 $\Gamma$。 / “Cusp monodromy” refers to the designated `Cm U`. Its conjugation theorem gives the Möbius **action**, and the proof uses matrix trace $-2$. Pointwise invariance of $\psi$ is given for $C^m$, and that of $\wp_t\circ\psi$ for every element of $\Gamma$. / 「カスプのモノドロミー」は指定された `Cm U` を指す。共役の定理が述べるのは Möbius **作用**であり、証明では行列のトレース $-2$ を用いる。$\psi$ の不変性は $C^m$ に対し、$\wp_t\circ\psi$ の不変性は $\Gamma$ の全要素に対して述べられている。 [Translation action](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftLatticeCuspCoordinates.lean:73) [Deck invariance](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftLatticeDepthGrowth.lean:31)
- `differentiableOn_comp_log` 的正则性结论作用于复合函数 $E\circ\operatorname{Log}$。`exists_cusp_exponential` 证明中的单射性用于推出 $G'(0)\ne0$，标准形声明对 $\phi$ 列出的逐点性质是有界性。 / Holomorphy in `differentiableOn_comp_log` concerns the composite $E\circ\operatorname{Log}$. The exponential proof uses injectivity to derive $G'(0)\ne0$, and the normal-form statement specifies a bound on $\phi$. / `differentiableOn_comp_log` の正則性は合成 $E\circ\operatorname{Log}$ に対するものである。指数関数の定理の証明は単射性を使って $G'(0)\ne0$ を導き、標準形の定理文は $\phi$ の有界性を指定する。 [Descent](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftLatticeCuspCoordinates.lean:31) [Exponential proof](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftLatticeCuspExponential.lean:207) [Normal form](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceIutCanLiftLatticeCuspNormalForm.lean:27)
