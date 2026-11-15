## Thm_AbcAdaptation_Reference_Iut_log_bound_ell.lean

For every pair of real numbers $\delta$ and $h$, both implicit parameters, given the explicit hypotheses $h_\delta:1\leq\delta$ and $h_h:1\leq h$, the natural logarithm satisfies $\log(20\delta^2h^2)\leq6\log(2\delta h)$. Both inequalities in the hypotheses are non-strict, so $\delta=1$, $h=1$, and their simultaneous occurrence are included; zero and negative values of either parameter are excluded. Under these hypotheses both logarithm arguments are positive. There are no additional parameters or typeclass assumptions. The supplied proof is the placeholder `by sorry`.

## Thm_AbcAdaptation_Reference_Iut_log_le_four_mul_sqrt_sqrt.lean

For every real number $h$, an implicit parameter, given the explicit hypothesis $h_h:1\leq h$, the natural logarithm and the nonnegative real square root satisfy $\log h\leq4\sqrt{\sqrt h}$. The boundary value $h=1$ is included; zero and negative values are excluded. Under the hypothesis, the logarithm argument and both radicands are positive, and both square roots are the nonnegative real square roots. There are no additional parameters or typeclass assumptions. The supplied proof is the placeholder `by sorry`.

## Thm_AbcAdaptation_Reference_Iut_log_le_half_of_pos.lean

For every real number $y$, an implicit parameter, given the explicit hypothesis $h_y:0<y$, the natural logarithm satisfies $\log y\leq y/2$, where division is in the real numbers. All positive real values are included, in particular $0<y<1$ and $y=1$; $y=0$ and negative values are excluded. The denominator is the nonzero real number $2$, so no division-by-zero case occurs. There are no additional parameters or typeclass assumptions. The supplied proof is the placeholder `by sorry`.

## Thm_AbcAdaptation_Reference_Iut_log_le_self_of_pos.lean

For every real number $y$, an implicit parameter, given the explicit hypothesis $h_y:0<y$, the natural logarithm satisfies $\log y\leq y$. All positive real values are included, in particular $0<y<1$ and $y=1$; $y=0$ and negative values are excluded. There are no additional parameters or typeclass assumptions. The supplied proof is the placeholder `by sorry`.
