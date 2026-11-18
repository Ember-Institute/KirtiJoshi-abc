# English

Let $K$ be a complete ultrametric normed field. For a Tate parameter with value $q$, set $Q_n(q)=q^{n+1}/(1-q^{n+1})$. For every function $c:\mathbb N\to\mathbb N$, the series $S_c(q)=\sum_{n\geq0}(c(n):K)Q_n(q)$ is summable. Each term has norm at most $\lVert q\rVert^{n+1}$, and $\lVert S_c(q)\rVert\leq\lVert q\rVert$. If $c(0)=1$, splitting off the first term gives $\lVert S_c(q)-q\rVert\leq\lVert q\rVert^2$.

For two Tate parameters, put $M=\max(\lVert q_1\rVert,\lVert q_2\rVert)$. The factor estimate is $\lVert Q_n(q_1)-Q_n(q_2)\rVert\leq M^n\lVert q_1-q_2\rVert$. It gives $\lVert S_c(q_1)-S_c(q_2)\rVert\leq\lVert q_1-q_2\rVert$. When $c(0)=1$, subtracting the leading term improves this bound to $\lVert(S_c(q_1)-q_1)-(S_c(q_2)-q_2)\rVert\leq M\lVert q_1-q_2\rVert$.

Now assume $(12:K)\ne0$ and take $c(n)=(5(n+1)^3+7(n+1)^5)/12$, with exact division in $\mathbb N$. Summing the coefficient identity gives $5s_3(q)+7s_5(q)=12S_c(q)$, hence $a_6(q)=-S_c(q)$. Therefore $\lVert a_6(q)\rVert\leq\lVert q\rVert$ and $\lVert a_6(q)+q\rVert\leq\lVert q\rVert^2$. The two parameter bounds also apply, with leading term $-q$. These results require no norm-one assumption on $12$.

# 简体中文

设 $K$ 是完备超度量赋范域。对取值为 $q$ 的 Tate 参数，记 $Q_n(q)=q^{n+1}/(1-q^{n+1})$。任取函数 $c:\mathbb N\to\mathbb N$，级数 $S_c(q)=\sum_{n\geq0}(c(n):K)Q_n(q)$ 可求和。每项范数至多为 $\lVert q\rVert^{n+1}$，且 $\lVert S_c(q)\rVert\leq\lVert q\rVert$。若 $c(0)=1$，则分离首项得到 $\lVert S_c(q)-q\rVert\leq\lVert q\rVert^2$。

对两个 Tate 参数，令 $M=\max(\lVert q_1\rVert,\lVert q_2\rVert)$。公共因子满足 $\lVert Q_n(q_1)-Q_n(q_2)\rVert\leq M^n\lVert q_1-q_2\rVert$，从而 $\lVert S_c(q_1)-S_c(q_2)\rVert\leq\lVert q_1-q_2\rVert$。若 $c(0)=1$，减去首项后有更强的估计：$\lVert(S_c(q_1)-q_1)-(S_c(q_2)-q_2)\rVert\leq M\lVert q_1-q_2\rVert$。

再假设 $(12:K)\ne0$，并取 $c(n)=(5(n+1)^3+7(n+1)^5)/12$，这里是自然数中的整除。对系数恒等式求和得到 $5s_3(q)+7s_5(q)=12S_c(q)$，因此 $a_6(q)=-S_c(q)$。于是 $\lVert a_6(q)\rVert\leq\lVert q\rVert$，且 $\lVert a_6(q)+q\rVert\leq\lVert q\rVert^2$。两参数估计也随之成立，其首项为 $-q$。这些结果不要求 $12$ 的范数等于一。

# 日本語

$K$ を完備な超距離ノルム体とする。値が $q$ である Tate パラメータに対し、$Q_n(q)=q^{n+1}/(1-q^{n+1})$ とおく。任意の関数 $c:\mathbb N\to\mathbb N$ に対し、級数 $S_c(q)=\sum_{n\geq0}(c(n):K)Q_n(q)$ は総和可能である。各項のノルムは $\lVert q\rVert^{n+1}$ 以下であり、$\lVert S_c(q)\rVert\leq\lVert q\rVert$ となる。$c(0)=1$ ならば、初項を分離することにより $\lVert S_c(q)-q\rVert\leq\lVert q\rVert^2$ を得る。

二つの Tate パラメータに対し、$M=\max(\lVert q_1\rVert,\lVert q_2\rVert)$ とおく。共通因子は $\lVert Q_n(q_1)-Q_n(q_2)\rVert\leq M^n\lVert q_1-q_2\rVert$ を満たす。したがって $\lVert S_c(q_1)-S_c(q_2)\rVert\leq\lVert q_1-q_2\rVert$ となる。$c(0)=1$ ならば、主要項を引くことで $\lVert(S_c(q_1)-q_1)-(S_c(q_2)-q_2)\rVert\leq M\lVert q_1-q_2\rVert$ という評価を得る。

さらに $(12:K)\ne0$ とし、$c(n)=(5(n+1)^3+7(n+1)^5)/12$ を用いる。ここでの除算は自然数の範囲で割り切れる。係数の恒等式を総和すると $5s_3(q)+7s_5(q)=12S_c(q)$ となり、$a_6(q)=-S_c(q)$ を得る。よって $\lVert a_6(q)\rVert\leq\lVert q\rVert$ かつ $\lVert a_6(q)+q\rVert\leq\lVert q\rVert^2$ である。主要項を $-q$ とする二つのパラメータの評価も従う。これらの結果では $12$ のノルムが一であるという仮定は必要ない。
