# The CanLift polynomial generator

Let $W$ be a nonsingular complex Weierstrass curve with a given uniformization $\pi$ and deck generators $A,B$. Write $G=\langle A,B\rangle$ and $N=\operatorname{Comm}(G)$ in $\mathrm{SL}_2(\mathbb R)$. The first-coordinate fibers are the orbits of a subgroup $\Gamma$ with $G\le \Gamma\le N$, obtained by adjoining a lift of Weierstrass negation. Assume $[N:G]<\infty$ and, for each $g\in N$, a polynomial bound for $|\pi_1(g\tau)|$ in $2+|\pi_1(\tau)|$. There is a positive-degree complex polynomial $s$ for which $s(\pi_1(g\tau))=s(\pi_1(\tau))$ for all $g\in N$. Equality of $s\circ\pi_1$ at two arguments implies that one argument is sent to the other by an element of $N$. The first-coordinate rigidity theorem consumes this polynomial when $j(W)\ne0,1728$.

## 中文

令 $W$ 为非奇异复 Weierstrass 曲线，给定一致化 $\pi$ 及覆盖变换的生成元 $A,B$。在 $\mathrm{SL}_2(\mathbb R)$ 中记 $G=\langle A,B\rangle$、$N=\operatorname{Comm}(G)$。第一坐标的纤维是某个子群 $\Gamma$ 的轨道，其中 $G\le\Gamma\le N$。该子群由 $G$ 添入 Weierstrass 取逆的一个提升得到。假定 $[N:G]<\infty$，并对每个 $g\in N$ 假定 $|\pi_1(g\tau)|$ 可由 $2+|\pi_1(\tau)|$ 的多项式增长界控制。则存在正次数复多项式 $s$，对所有 $g\in N$ 满足 $s(\pi_1(g\tau))=s(\pi_1(\tau))$。若两个参数在 $s\circ\pi_1$ 下取值相等，则 $N$ 中有元素把第一个参数送到第二个。对 $j(W)\ne0,1728$ 的情形，第一坐标刚性定理使用此多项式。

## 日本語

$W$ を非特異な複素 Weierstrass 曲線とし、一様化 $\pi$ と被覆変換の生成元 $A,B$ を与える。$\mathrm{SL}_2(\mathbb R)$ において $G=\langle A,B\rangle$、$N=\operatorname{Comm}(G)$ とする。第一座標のファイバーは $G\le\Gamma\le N$ を満たす部分群 $\Gamma$ の軌道である。この部分群は $G$ に Weierstrass 曲線の反転の持ち上げを加えて得られる。$[N:G]<\infty$ と仮定し、各 $g\in N$ に対して $|\pi_1(g\tau)|$ は $2+|\pi_1(\tau)|$ の多項式によって抑えられるとする。すべての $g\in N$ に対して $s(\pi_1(g\tau))=s(\pi_1(\tau))$ を満たす正次数の複素多項式 $s$ が存在する。$s\circ\pi_1$ の値が二点で一致するならば、$N$ の元が一方の点をもう一方へ移す。$j(W)\ne0,1728$ の場合は、この多項式を第一座標の剛性定理に適用する。

[First-coordinate fibers](../../../../Solutions/Source_ReferenceIutCanLiftFirstCoordinateFibres.lean) · [Polynomial generator](../../../../Solutions/Source_ReferenceIutCanLiftInvariantPolynomialGenerator.lean)
