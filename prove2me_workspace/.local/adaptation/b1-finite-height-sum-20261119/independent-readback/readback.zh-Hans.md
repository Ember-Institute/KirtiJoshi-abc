本文译自同目录的独立英文读回，原稿 SHA-256 为 2f6af20086afbea181645ade811218d07c5363dbeab38eac26d8e9aeddc3c579。英文读回涵盖求和定理及其辅助引理。

## deg_mul_height

任取指标类型 $I$、$I$ 的有限子集 $S$、从 $I$ 到 $\mathbb N$ 的函数 $p,a,f$，以及满足 $d\ge 1$ 的 $d\in\mathbb N$。假定对每个 $v\in S$，$p(v)$ 是素数，且 $a(v)\ge 1$、$f(v)\ge 1$。还假定对每个 $r\in\mathbb N$，都有 $\sum_{v\in S,\ p(v)=r}f(v)\le d$。定义 $H=\bigl(\sum_{v\in S}a(v)f(v)\log p(v)\bigr)/d$，其中 $\log$ 为自然对数，实数表达式中的自然数按实数计算。$S$ 可以为空，此时 $H=0$。对每组这样的输入，下列实数等式成立。
$$
dH=\sum_{v\in S}a(v)f(v)\log p(v).
$$

## finrank_mul_h_eq_finHeight

记 $\overline{\mathbb Q}$ 为 $\mathbb Q$ 的代数闭包，记 $E_\lambda$ 为 Legendre Weierstrass 模型 $Y^2=X(X-1)(X-\lambda)$。该模型在 $\overline{\mathbb Q}$ 上的点群由非奇异仿射点和无穷远点组成。输入数据 $P$ 保证对每个 $\lambda\in\overline{\mathbb Q}$，包括 $0$ 和 $1$，$E_\lambda$ 的点群中被 $3$ 消去的点集和被 $5$ 消去的点集都有限。对每个 $y\in\overline{\mathbb Q}\setminus\{0,1\}$，令 $F_y$ 为在 $\mathbb Q$ 上添入 $y$、为 $-1$、$y$ 和 $1-y$ 所选的平方根，以及 $E_y$ 在 $\overline{\mathbb Q}$ 上被 $3$ 或 $5$ 消去的每个仿射点的两个坐标所生成的 $\overline{\mathbb Q}$ 子域。将 $F_y$ 视为以 $\overline{\mathbb Q}$ 为代数闭包的数域，并将 $E_y$ 视为此模型定义的 $F_y$ 上的椭圆曲线。记 $j_y=j(E_y)$、$d_y=[F_y:\mathbb Q]$，并令 $K_y=\mathbb Q(j_y)\subseteq F_y$。记 $M_F^0$ 为数域 $F$ 的有限处集合。对 $w\in M_F^0$，绝对值 $|\cdot|_w$ 是把 $F$ 的整数环 $\mathcal O_F$ 中相应非零素理想 $\mathfrak m_w$ 处的完备化范数拉回 $F$ 所得。记 $p(w)$ 为剩余域 $\mathcal O_F/\mathfrak m_w$ 的特征，记 $f(w)$ 为此剩余域在 $\mathbb F_{p(w)}$ 上的次数，各处均采用所属的数域。令 $S_y$ 为 $F_y$ 上使 $E_y$ 有乘法约化的有限处的集合。此处某处的良好约化或乘法约化，指存在定义在 $F_y$ 上的 Weierstrass 变量变换，使变换后的模型延拓到该处的完备化后，在完备化的整数环上具有相应约化。对每个这样的 $y$，$P$ 保证 $-1$ 在 $F_y$ 中是平方，曲线在每个有限处都有良好约化或乘法约化，并且 $E_y$ 在 $\overline{\mathbb Q}$ 上被 $6$ 消去的每个点都是 $F_y$ 上一个点在基变换下的像。对每个素数 $\ell\ge 7$，$F_y/K_y$ 是伽罗瓦扩张，且其次数与 $\ell$ 互素。$F_y$ 的每个有限处 $w$ 位于 $K_y$ 的某个有限处 $v$ 上方，且只要 $w$ 位于 $v$ 上方，就有 $p(w)=p(v)$。对 $K_y$ 的每个满足 $p(v)\ne 2$ 的有限处 $v$，若 $v$ 上方有一个处属于 $S_y$，则其上方每个处都属于 $S_y$。$S_y$ 有限，$F_y$ 的每个有限处 $w$ 均满足 $f(w)>0$，且对每个 $r\in\mathbb N$，有 $\sum_{w\in S_y,\ p(w)=r}f(w)\le d_y$。对每个这样的 $y$ 和每个素数 $\ell$，$P$ 还给出从 $E_y$ 在 $\overline{\mathbb Q}$ 上被 $\ell$ 消去的点群到 $(\mathbb Z/\ell\mathbb Z)^2$ 的加法群同构 $\beta$，以及群同态 $\rho\colon\operatorname{Aut}_{F_y}(\overline{\mathbb Q})\to\operatorname{GL}_2(\mathbb Z/\ell\mathbb Z)$，其核在自同构群的拓扑中是开集。对每个这样的点 $T$ 和每个这样的自同构 $\sigma$，有 $\beta(\sigma T)=\rho(\sigma)\beta(T)$，其中 $\sigma$ 作用在点的坐标上。给定任意这样的 $P$ 和任意 $x\in\overline{\mathbb Q}\setminus\{0,1\}$，定义 $h_P(x)=d_x^{-1}\sum_{w\in S_x}a(w)f(w)\log p(w)$。对每个 $w\in S_x$，在 $w$ 处的完备化中选取范数严格小于 $1$ 的非零 Tate 参数 $q_w$，使其 Tate $j$ 不变量等于 $j_x$ 在该完备化中的像。还在该完备化中选取范数严格小于 $1$ 的非零素元 $\pi_w$，使每个非零元素的范数都可写为 $\|\pi_w\|^n$，其中 $n\in\mathbb Z$。局部值 $a(w)$ 是满足 $\|q_w\|=\|\pi_w\|^{a(w)}$ 的正整数，在 $S_x$ 外取 $a(w)=0$。实数表达式中的自然数按实数计算。下式中的 $\sum^{\mathrm f}$ 在非零项有限时取这些项之和，在非零项无限时取 $0$。自然对数采用 $\log 0=0$ 的约定，因此 $j_x=0$ 时每一项都为 $0$。$S_x$ 为空时左边为零，等式断言右边也为零。命题断言以下实数等式成立。
$$
d_x h_P(x)=\sum_{w\in M_{F_x}^0}^{\mathrm f}\max\{0,\log|j_x|_w\}.
$$
