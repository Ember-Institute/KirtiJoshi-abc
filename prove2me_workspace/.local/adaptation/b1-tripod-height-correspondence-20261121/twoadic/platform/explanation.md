Fix a point $x$ in $K$ with coordinate $\lambda$. Let $w$ be a place of the curve field $F_x$ above $2$ where the curve has multiplicative reduction. Write $v$ for the place of the tripodal field below $w$. The valuation of the $j$-invariant gives the order $m_w$ of the Tate parameter. The Legendre formula and the ultrametric inequality give
$$
m_w \le 2\bigl(\lvert\log v_w(\lambda)\rvert+
                  \lvert\log v_w(\lambda-1)\rvert\bigr).
$$
The two logarithmic valuations at $w$ are the corresponding values at $v$ multiplied by the relative ramification index $e(w/v)$. The compact bounds control each absolute value at $v$ after multiplication by $f_v\log 2$. Since $f_w=f_v f(w/v)$, the local summand is therefore at most $4c\,e(w/v)f(w/v)$.

The product $e(w/v)f(w/v)$ is at most the absolute local degree $d_w$, because $d_w=d_v e(w/v) f(w/v)$ and $d_v\ge 1$. The presence of $x$ in $K$ gives $c\ge 0$, so the summand is at most $4c\,d_w$. The lemma `term_le` establishes this inequality. Sum over the multiplicative places above $2$ and use $\sum_{w\mid 2}d_w=[F_x:\mathbb Q]$. Division by $[F_x:\mathbb Q]$ gives the bound $4c$, which is at most $\max(4c,0)$.
