## Thm_AbcAdaptation_Reference_Iut_log_pi_le_two.lean

本声明没有显式或隐式参数，也没有前提；实数常量 $\pi$ 的自然对数满足 $\ln(\pi)\leq 2$，其中 $2$ 是实数。声明没有可能产生退化情形的变量。证明体为 `by sorry`，即承认结论的占位符。

## Thm_AbcAdaptation_Reference_Iut_log_pi_nonneg.lean

本声明没有显式或隐式参数，也没有前提；实数常量 $\pi$ 的自然对数满足 $0\leq\ln(\pi)$，其中 $0$ 是实数零。声明没有可能产生退化情形的变量。证明体为 `by sorry`，即承认结论的占位符。

## Thm_AbcAdaptation_Reference_Iut_sum_affine_quadratic.lean

对于每一个自然数 $L$ 和任意三个实数 $a,b,c$，这四个参数均为显式参数，没有隐式参数或前提，声明断言以下实数等式：$$\sum_{i\in\{0,\ldots,L-1\}}\left(a(\iota(i)+2)+b(\iota(i)+1)^2+c\right)=a\frac{\iota(L)(\iota(L)+3)}{2}+b\frac{\iota(L)(\iota(L)+1)(2\iota(L)+1)}{6}+c\iota(L).$$ 这里 $\iota(n)$ 表示将自然数 $n$ 强制转换为实数。求和遍历恰有 $L$ 个元素的有限类型中的所有元素，这些元素恰由满足 $0\leq i<L$ 的自然数 $i$ 表示；每个指标先被视为对应的自然数，再被强制转换为实数。右侧每一处 $L$ 也都先被强制转换为实数，再进行所示运算；等式中的加法、乘法、平方和除法均为实数运算。对 $L,a,b,c$ 均没有正性或非零条件。尤其包括 $L=0$ 的情形：指标集为空，和为实数零，且对于任意 $a,b,c$，等式两侧均为零。证明体为 `by sorry`，即承认结论的占位符。
