## Thm_AbcAdaptation_Reference_Iut_log_pi_le_two.lean

With no explicit or implicit parameters and no hypotheses, the natural logarithm of the real constant $\pi$ satisfies $\ln(\pi)\leq 2$, where $2$ is a real number. There is no variable over which a degenerate case can arise. The proof body is `by sorry`, an admitted placeholder.

## Thm_AbcAdaptation_Reference_Iut_log_pi_nonneg.lean

With no explicit or implicit parameters and no hypotheses, the natural logarithm of the real constant $\pi$ satisfies $0\leq\ln(\pi)$, where $0$ is the real zero. There is no variable over which a degenerate case can arise. The proof body is `by sorry`, an admitted placeholder.

## Thm_AbcAdaptation_Reference_Iut_sum_affine_quadratic.lean

For every natural number $L$ and every three real numbers $a,b,c$, all four supplied as explicit parameters, with no implicit parameters or hypotheses, the following equality of real numbers is asserted: $$\sum_{i\in\{0,\ldots,L-1\}}\left(a(\iota(i)+2)+b(\iota(i)+1)^2+c\right)=a\frac{\iota(L)(\iota(L)+3)}{2}+b\frac{\iota(L)(\iota(L)+1)(2\iota(L)+1)}{6}+c\iota(L).$$ Here $\iota(n)$ denotes the coercion of a natural number $n$ to a real number. The sum ranges over every element of the finite type with $L$ elements, represented by exactly the natural numbers $i$ satisfying $0\leq i<L$; each index is first regarded as that natural number and then coerced to a real number. Every occurrence of $L$ on the right is likewise coerced to a real number before the displayed arithmetic; the additions, multiplications, squares, and divisions in the equality are real arithmetic. There are no positivity or nonzero conditions on $L,a,b,c$. In particular, $L=0$ is included: the index set is empty, the sum is the real zero, and both sides are zero for every $a,b,c$. The proof body is `by sorry`, an admitted placeholder.
