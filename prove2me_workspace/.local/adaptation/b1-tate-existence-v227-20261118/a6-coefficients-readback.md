# English

For a natural number $n$, write $m=n+1$ and $c_m=(5m^3+7m^5)/12$. The division is exact in the natural numbers: checking the residues modulo $12$ shows that $12$ divides the numerator. Consequently $12c_m=5m^3+7m^5$, and $c_1=1$. The Lean index of this first coefficient is zero.

For a Tate parameter with value $q$ in a normed field, write $Q_n=q^{n+1}/(1-q^{n+1})$. Each Eisenstein series can be written as the sum of the terms $m^kQ_n$. The coefficient identity also gives $5(m^3Q_n)+7(m^5Q_n)=12(c_m Q_n)$ after casting the natural coefficients into the field. This is a termwise identity; it does not divide by $12$ in the field. The later step that solves for the sixth Weierstrass coefficient does require $12\ne0$ in that field.

# 简体中文

对自然数 $n$，令 $m=n+1$，并令 $c_m=(5m^3+7m^5)/12$。逐一检查模 $12$ 的剩余类可知，分子能被 $12$ 整除。因此 $12c_m=5m^3+7m^5$，且首项系数 $c_1=1$。这个首项在形式代码中的索引为零。

设赋范域中 Tate 参数的取值为 $q$，记 $Q_n=q^{n+1}/(1-q^{n+1})$。每个 Eisenstein 级数都可写成以 $m^kQ_n$ 为通项的和。把自然数系数代入域中后，还有逐项恒等式 $5(m^3Q_n)+7(m^5Q_n)=12(c_m Q_n)$。这一步没有在域中除以 $12$；后续解出第六个 Weierstrass 系数时才需要域中的 $12$ 非零。

# 日本語

自然数 $n$ に対して $m=n+1$ とし、$c_m=(5m^3+7m^5)/12$ とおく。法 $12$ の剰余類を調べると、分子は $12$ で割り切れる。したがって $12c_m=5m^3+7m^5$ であり、初項の係数は $c_1=1$ である。この初項の形式コードでの添字は零である。

ノルム体における Tate パラメータの値を $q$ とし、$Q_n=q^{n+1}/(1-q^{n+1})$ とおく。各 Eisenstein 級数は一般項 $m^kQ_n$ の和として表せる。自然数の係数を体の元とみなすと、項ごとに $5(m^3Q_n)+7(m^5Q_n)=12(c_m Q_n)$ が成り立つ。この等式では体の中で $12$ による除算を行わない。第六 Weierstrass 係数について解く後の段階では、体の中で $12\ne0$ が必要となる。
