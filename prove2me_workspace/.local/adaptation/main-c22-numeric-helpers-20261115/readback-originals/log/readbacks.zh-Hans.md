## Thm_AbcAdaptation_Reference_Iut_log_bound_ell.lean

对于任意实数 $\delta$ 和 $h$（二者均为隐式参数），给定显式前提 $h_\delta:1\leq\delta$ 和 $h_h:1\leq h$，自然对数满足 $\log(20\delta^2h^2)\leq6\log(2\delta h)$。两个前提中的不等式均为非严格不等式，因此包括 $\delta=1$、$h=1$ 以及二者同时成立的情形；任一参数为零或负数的情形均被排除。在这些前提下，两个对数的真数均为正数。没有其他参数或类型类假设。所提供的证明为占位代码 `by sorry`。

## Thm_AbcAdaptation_Reference_Iut_log_le_four_mul_sqrt_sqrt.lean

对于任意实数 $h$（隐式参数），给定显式前提 $h_h:1\leq h$，自然对数与非负实平方根满足 $\log h\leq4\sqrt{\sqrt h}$。包括边界值 $h=1$；零和负数均被排除。在该前提下，对数的真数和两个被开方数均为正数，两个平方根均指非负实平方根。没有其他参数或类型类假设。所提供的证明为占位代码 `by sorry`。

## Thm_AbcAdaptation_Reference_Iut_log_le_half_of_pos.lean

对于任意实数 $y$（隐式参数），给定显式前提 $h_y:0<y$，自然对数满足 $\log y\leq y/2$，其中除法为实数除法。包括所有正实数值，特别包括 $0<y<1$ 和 $y=1$；$y=0$ 和负数均被排除。分母为非零实数 $2$，因此不存在除以零的情形。没有其他参数或类型类假设。所提供的证明为占位代码 `by sorry`。

## Thm_AbcAdaptation_Reference_Iut_log_le_self_of_pos.lean

对于任意实数 $y$（隐式参数），给定显式前提 $h_y:0<y$，自然对数满足 $\log y\leq y$。包括所有正实数值，特别包括 $0<y<1$ 和 $y=1$；$y=0$ 和负数均被排除。没有其他参数或类型类假设。所提供的证明为占位代码 `by sorry`。
