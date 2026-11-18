## `logDifferentDeg`

### English

For any number field $L$, including degree one over $\mathbb Q$, let $\mathfrak D_L$ be the different ideal of the ring of integers $\mathcal O_L$ over $\mathbb Z$. This definition assigns to $L$ the real number $\frac{\log\mathrm N_{\mathrm{abs}}(\mathfrak D_L)}{[L:\mathbb Q]}$, where $\mathrm N_{\mathrm{abs}}$ is the absolute ideal norm, $[L:\mathbb Q]$ is the dimension of $L$ over $\mathbb Q$, and $\log$ is the real natural logarithm. The norm and the dimension are taken as real numbers in this expression.

### 简体中文

设 $L$ 为任意数域，允许 $L$ 在 $\mathbb Q$ 上的次数为 $1$。记 $\mathfrak D_L$ 为 $L$ 的整数环 $\mathcal O_L$ 相对于 $\mathbb Z$ 的不同理想（different ideal）。该定义赋予 $L$ 实数 $\frac{\log\mathrm N_{\mathrm{abs}}(\mathfrak D_L)}{[L:\mathbb Q]}$，其中 $\mathrm N_{\mathrm{abs}}$ 是理想的绝对范数，$[L:\mathbb Q]$ 是 $L$ 在 $\mathbb Q$ 上的向量空间维数，$\log$ 是实数上的自然对数。式中的范数和维数都视为实数。

### 日本語

$L$ を任意の数体とし、$\mathbb Q$ 上の拡大次数が $1$ の場合も含める。$\mathfrak D_L$ を整数環 $\mathcal O_L$ の $\mathbb Z$ 上の相対差積イデアル（different ideal）とする。この定義は $L$ に実数 $\frac{\log\mathrm N_{\mathrm{abs}}(\mathfrak D_L)}{[L:\mathbb Q]}$ を対応させる。ここで $\mathrm N_{\mathrm{abs}}$ はイデアルの絶対ノルム、$[L:\mathbb Q]$ は $L$ の $\mathbb Q$ 上のベクトル空間としての次元、$\log$ は実数上の自然対数である。式中のノルムと次元は実数として扱う。

## `logDifferentDeg_eq_of_algEquiv`

### English

Let $K$ and $L$ be arbitrary number fields, and let $f\colon K\xrightarrow{\sim}L$ be a $\mathbb Q$-algebra isomorphism. For $A\in\{K,L\}$, let $\mathfrak D_A$ be the different ideal of the ring of integers $\mathcal O_A$ over $\mathbb Z$, let $\mathrm N_{\mathrm{abs}}$ be the absolute ideal norm in the corresponding ring of integers, and write $[A:\mathbb Q]$ for the dimension of $A$ over $\mathbb Q$. Then $\frac{\log\mathrm N_{\mathrm{abs}}(\mathfrak D_K)}{[K:\mathbb Q]}=\frac{\log\mathrm N_{\mathrm{abs}}(\mathfrak D_L)}{[L:\mathbb Q]}$, with real natural logarithms and real division.

### 简体中文

设 $K$ 和 $L$ 均为数域，并给定一个 $\mathbb Q$-代数同构 $f\colon K\xrightarrow{\sim}L$。对 $A\in\{K,L\}$，记 $\mathfrak D_A$ 为 $A$ 的整数环 $\mathcal O_A$ 相对于 $\mathbb Z$ 的不同理想（different ideal），$\mathrm N_{\mathrm{abs}}$ 为相应整数环中理想的绝对范数，$[A:\mathbb Q]$ 为 $A$ 在 $\mathbb Q$ 上的向量空间维数。则 $\frac{\log\mathrm N_{\mathrm{abs}}(\mathfrak D_K)}{[K:\mathbb Q]}=\frac{\log\mathrm N_{\mathrm{abs}}(\mathfrak D_L)}{[L:\mathbb Q]}$，其中取实数上的自然对数，并在实数中做除法。

### 日本語

$K,L$ を任意の数体とし、$f\colon K\xrightarrow{\sim}L$ を $\mathbb Q$-代数の同型とする。$A\in\{K,L\}$ について、$\mathfrak D_A$ を整数環 $\mathcal O_A$ の $\mathbb Z$ 上の相対差積イデアル（different ideal）、$\mathrm N_{\mathrm{abs}}$ を対応する整数環のイデアルの絶対ノルム、$[A:\mathbb Q]$ を $A$ の $\mathbb Q$ 上のベクトル空間としての次元とする。このとき $\frac{\log\mathrm N_{\mathrm{abs}}(\mathfrak D_K)}{[K:\mathbb Q]}=\frac{\log\mathrm N_{\mathrm{abs}}(\mathfrak D_L)}{[L:\mathbb Q]}$ が成り立つ。対数は実数上の自然対数であり、除法は実数で行う。

## `logDiff_eq_logDifferentDeg`

### English

Let $x$ be any input consisting of an element $\lambda$ of the algebraic closure $\overline{\mathbb Q}$ of $\mathbb Q$ with $\lambda\ne 0$ and $\lambda\ne 1$, allowing rational $\lambda$ that meet these conditions. Let $K=\mathbb Q(\lambda)$ be the subfield of $\overline{\mathbb Q}$ generated over $\mathbb Q$ by $\lambda$, and let $m_\lambda\in\mathbb Q[X]$ be the minimal polynomial of $\lambda$ over $\mathbb Q$, of natural-number degree $\deg m_\lambda$. Write $\operatorname{disc}(K)$ for the number field discriminant of $K$, $\mathfrak D_K$ for the different ideal of its ring of integers $\mathcal O_K$ over $\mathbb Z$, $\mathrm N_{\mathrm{abs}}$ for the absolute ideal norm, and $[K:\mathbb Q]$ for the degree of $K$ over $\mathbb Q$. Then $\frac{\log|\operatorname{disc}(K)|}{\deg m_\lambda}=\frac{\log\mathrm N_{\mathrm{abs}}(\mathfrak D_K)}{[K:\mathbb Q]}$, with real natural logarithms and real division.

### 简体中文

任取输入 $x$，其元素 $\lambda$ 属于 $\mathbb Q$ 的代数闭包 $\overline{\mathbb Q}$，并满足 $\lambda\ne 0$ 和 $\lambda\ne 1$，其中允许满足这两个条件的有理数。设 $K=\mathbb Q(\lambda)$ 为 $\lambda$ 在 $\mathbb Q$ 上生成的 $\overline{\mathbb Q}$ 的子域，$m_\lambda\in\mathbb Q[X]$ 为 $\lambda$ 在 $\mathbb Q$ 上的最小多项式，其次数 $\deg m_\lambda$ 为自然数。记 $\operatorname{disc}(K)$ 为数域 $K$ 的判别式，$\mathfrak D_K$ 为其整数环 $\mathcal O_K$ 相对于 $\mathbb Z$ 的不同理想（different ideal），$\mathrm N_{\mathrm{abs}}$ 为理想的绝对范数，$[K:\mathbb Q]$ 为 $K$ 在 $\mathbb Q$ 上的次数。则 $\frac{\log|\operatorname{disc}(K)|}{\deg m_\lambda}=\frac{\log\mathrm N_{\mathrm{abs}}(\mathfrak D_K)}{[K:\mathbb Q]}$，其中取实数上的自然对数，并在实数中做除法。

### 日本語

$x$ を、$\mathbb Q$ の代数閉包 $\overline{\mathbb Q}$ の元 $\lambda$ であって $\lambda\ne 0$ かつ $\lambda\ne 1$ を満たすものを表す任意の入力とする。これらの条件を満たす有理数 $\lambda$ も含める。$K=\mathbb Q(\lambda)$ を $\lambda$ が $\mathbb Q$ 上生成する $\overline{\mathbb Q}$ の部分体とし、$m_\lambda\in\mathbb Q[X]$ を $\lambda$ の $\mathbb Q$ 上の最小多項式とし、その自然数としての次数を $\deg m_\lambda$ とする。$\operatorname{disc}(K)$ を数体 $K$ の判別式、$\mathfrak D_K$ をその整数環 $\mathcal O_K$ の $\mathbb Z$ 上の相対差積イデアル（different ideal）、$\mathrm N_{\mathrm{abs}}$ をイデアルの絶対ノルム、$[K:\mathbb Q]$ を $K$ の $\mathbb Q$ 上の拡大次数とする。このとき $\frac{\log|\operatorname{disc}(K)|}{\deg m_\lambda}=\frac{\log\mathrm N_{\mathrm{abs}}(\mathfrak D_K)}{[K:\mathbb Q]}$ が成り立つ。対数は実数上の自然対数であり、除法は実数で行う。

## `logDiff_eq`

### English

Let $x$ be any input consisting of an element $\lambda$ of the algebraic closure $\overline{\mathbb Q}$ of $\mathbb Q$ with $\lambda\ne 0$ and $\lambda\ne 1$, allowing rational $\lambda$ that meet these conditions. Over $\overline{\mathbb Q}$ use the Weierstrass equation $Y^2=X^3-(\lambda+1)X^2+\lambda X$, with group identity the point at infinity $O$. The points over $\overline{\mathbb Q}$ consist of the nonsingular affine points and $O$. For $n\in\{3,5\}$ let $T_n$ be the set of those points whose $n$-fold multiple is $O$. Take hypotheses $h_3$ and $h_5$ asserting that $T_3$ and $T_5$, respectively, are finite. Let $C_n$ be the union of the coordinate sets $\{a,b\}$ of the affine points $(a,b)$ in $T_n$. The point $O$ belongs to both torsion sets and contributes the empty set. Let $u,v,w$ be the chosen square roots in $\overline{\mathbb Q}$ of $-1,\lambda,1-\lambda$, respectively, and let $F$ be the subfield of $\overline{\mathbb Q}$ generated over $\mathbb Q$ by $\{\lambda,u,v,w\}\cup C_3\cup C_5$. The finiteness assumptions give that $F$ is finite over $\mathbb Q$. Regard $\lambda$ as an element of $F$ and let $E$ be the elliptic curve over $F$ given by the same Weierstrass equation, with $\overline{\mathbb Q}$ as the ambient algebraically closed field. Let $S$ consist of every $a\in F$ for which some $b\in F$ makes $(a,b)$ a nonsingular affine point of $E$ whose double is the point at infinity. Let $M$ be the subfield of $F$ generated over $\mathbb Q$ by the $j$-invariant $j(E)$ and the elements of $S$. Write $K=\mathbb Q(\lambda)$ for the subfield of $\overline{\mathbb Q}$ generated by $\lambda$ over $\mathbb Q$, $m_\lambda\in\mathbb Q[X]$ for the minimal polynomial of $\lambda$ over $\mathbb Q$ with natural-number degree $\deg m_\lambda$, and $\operatorname{disc}(K)$ for the number field discriminant of $K$. With $\mathfrak D_M$ the different ideal of the ring of integers $\mathcal O_M$ over $\mathbb Z$, $\mathrm N_{\mathrm{abs}}$ the absolute ideal norm, and $[M:\mathbb Q]$ the degree of $M$ over $\mathbb Q$, the assertion is $\frac{\log|\operatorname{disc}(K)|}{\deg m_\lambda}=\frac{\log\mathrm N_{\mathrm{abs}}(\mathfrak D_M)}{[M:\mathbb Q]}$, with real natural logarithms and real division.

### 简体中文

任取输入 $x$，其元素 $\lambda$ 属于 $\mathbb Q$ 的代数闭包 $\overline{\mathbb Q}$，并满足 $\lambda\ne 0$ 和 $\lambda\ne 1$，其中允许满足这两个条件的有理数。在 $\overline{\mathbb Q}$ 上取魏尔斯特拉斯方程 $Y^2=X^3-(\lambda+1)X^2+\lambda X$，以无穷远点 $O$ 为群单位元。该曲线的 $\overline{\mathbb Q}$-有理点由非奇异仿射点和 $O$ 组成。对 $n\in\{3,5\}$，记 $T_n$ 为其中 $n$ 倍等于 $O$ 的点集。给定两个假设 $h_3$ 和 $h_5$，分别断言 $T_3$ 和 $T_5$ 是有限集。记 $C_n$ 为 $T_n$ 中各仿射点 $(a,b)$ 的坐标集合 $\{a,b\}$ 的并集。$O$ 属于这两个挠点集，在取并集时它对应的坐标集合为空集。记 $u,v,w$ 分别为 $-1,\lambda,1-\lambda$ 在 $\overline{\mathbb Q}$ 中选定的平方根，令 $F$ 为 $\{\lambda,u,v,w\}\cup C_3\cup C_5$ 在 $\mathbb Q$ 上生成的 $\overline{\mathbb Q}$ 的子域。这两个有限性假设使得 $F$ 是 $\mathbb Q$ 的有限扩域。把 $\lambda$ 视为 $F$ 的元素，令 $E$ 为在 $F$ 上由同一个魏尔斯特拉斯方程给出的椭圆曲线，以 $\overline{\mathbb Q}$ 为其基域 $F$ 的代数闭包。令 $S$ 为所有满足以下条件的 $a\in F$ 所成的集合，即存在 $b\in F$ 使 $(a,b)$ 是 $E$ 的非奇异仿射点，且该点的两倍是无穷远点。令 $M$ 为 $E$ 的 $j$-不变量 $j(E)$ 与 $S$ 的所有元素在 $\mathbb Q$ 上生成的 $F$ 的子域。记 $K=\mathbb Q(\lambda)$ 为 $\lambda$ 在 $\mathbb Q$ 上生成的 $\overline{\mathbb Q}$ 的子域，$m_\lambda\in\mathbb Q[X]$ 为 $\lambda$ 在 $\mathbb Q$ 上的最小多项式，其次数 $\deg m_\lambda$ 为自然数。记 $\operatorname{disc}(K)$ 为数域 $K$ 的判别式。记 $\mathfrak D_M$ 为 $M$ 的整数环 $\mathcal O_M$ 相对于 $\mathbb Z$ 的不同理想（different ideal），$\mathrm N_{\mathrm{abs}}$ 为理想的绝对范数，$[M:\mathbb Q]$ 为 $M$ 在 $\mathbb Q$ 上的次数。则 $\frac{\log|\operatorname{disc}(K)|}{\deg m_\lambda}=\frac{\log\mathrm N_{\mathrm{abs}}(\mathfrak D_M)}{[M:\mathbb Q]}$，其中取实数上的自然对数，并在实数中做除法。

### 日本語

$x$ を、$\mathbb Q$ の代数閉包 $\overline{\mathbb Q}$ の元 $\lambda$ であって $\lambda\ne 0$ かつ $\lambda\ne 1$ を満たすものを表す任意の入力とする。これらの条件を満たす有理数 $\lambda$ も含める。$\overline{\mathbb Q}$ 上のワイエルシュトラス方程式 $Y^2=X^3-(\lambda+1)X^2+\lambda X$ を取り、無限遠点 $O$ を群の単位元とする。$n\in\{3,5\}$ について、この曲線の $\overline{\mathbb Q}$ 上の非特異なアフィン点と $O$ のうち、$n$ 倍が $O$ になる点の集合を $T_n$ とする。$T_3$ が有限集合であるという仮定を $h_3$、$T_5$ が有限集合であるという仮定を $h_5$ とする。$C_n$ を、$T_n$ に属するアフィン点 $(a,b)$ の座標集合 $\{a,b\}$ の和集合とする。無限遠点 $O$ は二つのねじれ点集合に属し、$O$ に対応する座標集合は空集合とする。$u,v,w$ をそれぞれ $-1,\lambda,1-\lambda$ の $\overline{\mathbb Q}$ 内で選ばれた平方根とし、$F$ を $\{\lambda,u,v,w\}\cup C_3\cup C_5$ を $\mathbb Q$ に添加して得られる $\overline{\mathbb Q}$ の部分体とする。二つの有限性の仮定により、$F$ は $\mathbb Q$ の有限次拡大となる。$\lambda$ を $F$ の元とみなし、同じワイエルシュトラス方程式で定まる $F$ 上の楕円曲線を $E$ とする。ここで $F$ の代数閉包として $\overline{\mathbb Q}$ を用いる。ある $b\in F$ について、$(a,b)$ が $E$ の非特異なアフィン点であり、その $2$ 倍が無限遠点となるような $a\in F$ 全体の集合を $S$ とする。$M$ を、$E$ の $j$-不変量 $j(E)$ と $S$ の元をすべて $\mathbb Q$ に添加して得られる $F$ の部分体とする。$K=\mathbb Q(\lambda)$ を $\lambda$ が $\mathbb Q$ 上生成する $\overline{\mathbb Q}$ の部分体、$m_\lambda\in\mathbb Q[X]$ を $\lambda$ の $\mathbb Q$ 上の最小多項式とし、その自然数としての次数を $\deg m_\lambda$ とする。$\operatorname{disc}(K)$ を数体 $K$ の判別式とする。$\mathfrak D_M$ を $M$ の整数環 $\mathcal O_M$ の $\mathbb Z$ 上の相対差積イデアル（different ideal）、$\mathrm N_{\mathrm{abs}}$ をイデアルの絶対ノルム、$[M:\mathbb Q]$ を $M$ の $\mathbb Q$ 上の拡大次数とすると、$\frac{\log|\operatorname{disc}(K)|}{\deg m_\lambda}=\frac{\log\mathrm N_{\mathrm{abs}}(\mathfrak D_M)}{[M:\mathbb Q]}$ が成り立つ。対数は実数上の自然対数であり、除法は実数で行う。
