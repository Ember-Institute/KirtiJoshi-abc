# 简体中文读回

本稿由原中文译文定稿，按 TERM-015 采用「素元」。独立英文读回由原档记录为 gpt-6.1-sol。 [原中文](readback.zh-Hans.md) · [独立英文](readback.en.frozen.md) · [TERM-015](../../../../../../docs/三语术语名词关键对照.md#L44) · [Lean 声明](../../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_UniformizerSupply.lean#L20)

## `AbcAdaptation.Reference.Iut.norm_le_one_iff_valued`

对每个具有数域结构的域 $F$、$F$ 的每个有限位 $w$，以及 $F_w$ 的每个元素 $x$，都有 $\|x\|\leq1$ 当且仅当 $v_w(x)\leq1$。这里，$F_w$ 是 $F$ 关于其整数环的非零素理想 $\mathfrak p=w.\mathrm{maximalIdeal}$ 所对应的离散赋值的完备化；$\|\cdot\|:F_w\to\mathbb R$ 是该完备化域的赋范域结构所给出的范数，$v_w:F_w\to\Gamma_0$ 是它的乘法赋值，其中 $\Gamma_0=\operatorname{WithZero}(\operatorname{Multiplicative}\mathbb Z)$ 是加法群 $\mathbb Z$ 的有序乘法副本再添一个零元。其非零元素记为 $\exp(n)$，满足 $\exp(m)\exp(n)=\exp(m+n)$、$\exp(0)=1$，且 $\exp(m)<\exp(n)$ 当且仅当 $m<n$；添入的零元小于每个非零元素。左侧的 $1$ 是实数，右侧的 $1$ 是 $\Gamma_0$ 的单位元。对 $x$ 的量化包括 $x=0$。

## `AbcAdaptation.Reference.Iut.norm_lt_one_iff_valued`

对每个具有数域结构的域 $F$、$F$ 的每个有限位 $w$，以及 $F_w$ 的每个元素 $x$，都有 $\|x\|<1$ 当且仅当 $v_w(x)<1$。这里，$F_w$ 是 $F$ 关于其整数环的非零素理想 $\mathfrak p=w.\mathrm{maximalIdeal}$ 所对应的离散赋值的完备化；$\|\cdot\|:F_w\to\mathbb R$ 是该完备化域的赋范域结构所给出的范数，$v_w:F_w\to\Gamma_0$ 是它的乘法赋值，其中 $\Gamma_0=\operatorname{WithZero}(\operatorname{Multiplicative}\mathbb Z)$ 是加法群 $\mathbb Z$ 的有序乘法副本再添一个零元。其非零元素记为 $\exp(n)$，满足 $\exp(m)\exp(n)=\exp(m+n)$、$\exp(0)=1$，且 $\exp(m)<\exp(n)$ 当且仅当 $m<n$；添入的零元小于每个非零元素。左侧的 $1$ 是实数，右侧的 $1$ 是 $\Gamma_0$ 的单位元。对 $x$ 的量化包括 $x=0$。

## `AbcAdaptation.Reference.Iut.norm_eq_one_iff_valued`

对每个具有数域结构的域 $F$、$F$ 的每个有限位 $w$，以及 $F_w$ 的每个元素 $x$，都有 $\|x\|=1$ 当且仅当 $v_w(x)=1$。这里，$F_w$ 是 $F$ 关于其整数环的非零素理想 $\mathfrak p=w.\mathrm{maximalIdeal}$ 所对应的离散赋值的完备化；$\|\cdot\|:F_w\to\mathbb R$ 是该完备化域的赋范域结构所给出的范数，$v_w:F_w\to\Gamma_0$ 是它的乘法赋值，其中 $\Gamma_0=\operatorname{WithZero}(\operatorname{Multiplicative}\mathbb Z)$ 是加法群 $\mathbb Z$ 的有序乘法副本再添一个零元。其非零元素记为 $\exp(n)$，满足 $\exp(m)\exp(n)=\exp(m+n)$、$\exp(0)=1$，且 $\exp(m)<\exp(n)$ 当且仅当 $m<n$；添入的零元小于每个非零元素。左侧的 $1$ 是实数，右侧的 $1$ 是 $\Gamma_0$ 的单位元。对 $x$ 的量化包括 $x=0$。

## `AbcAdaptation.Reference.Iut.isUniformizer_of_valuation_eq`

对每个具有数域结构的域 $F$、$F$ 的每个有限位 $w$，以及每个元素 $\pi\in F$，假设 $v_{\mathfrak p}(\pi)=\exp(-1)$，其中 $\mathfrak p=w.\mathrm{maximalIdeal}$ 是 $F$ 的整数环中所对应的非零素理想，$v_{\mathfrak p}:F\to\Gamma_0$ 是它的乘法离散赋值。这里，$\Gamma_0=\operatorname{WithZero}(\operatorname{Multiplicative}\mathbb Z)$ 是加法群 $\mathbb Z$ 的有序乘法副本再添一个零元；$\exp(n)$ 表示整数 $n$ 的非零副本，乘法对应指数相加，$\exp(0)=1$，非零元素的顺序就是其整数指数的顺序，而添入的零元小于所有非零元素。令 $F_w$ 为 $F$ 关于此赋值的完备化，赋予其范数 $\|\cdot\|:F_w\to\mathbb R$，并令 $\iota_w:F\to F_w$ 为典范域嵌入。那么，$\iota_w(\pi)$ 在下述精确意义下是素元：$\iota_w(\pi)\neq0$、$\|\iota_w(\pi)\|<1$，且对每个可逆元素 $u\in F_w^{\times}$，都存在整数 $n\in\mathbb Z$ 使 $\|u\|=\|\iota_w(\pi)\|^n$。整数 $n$ 可以依赖于 $u$，可以为负数、零或正数；这里没有断言 $n$ 的唯一性。由于 $\exp(-1)\neq0$，假设排除了 $\pi=0$。

## `AbcAdaptation.Reference.Iut.exists_isUniformizer`

对每个具有数域结构的域 $F$ 和 $F$ 的每个有限位 $w$，令 $F_w$ 为 $F$ 关于其整数环的非零素理想 $\mathfrak p=w.\mathrm{maximalIdeal}$ 所对应的乘法离散赋值的完备化，带有其范数 $\|\cdot\|:F_w\to\mathbb R$。赋值取值于 $\Gamma_0=\operatorname{WithZero}(\operatorname{Multiplicative}\mathbb Z)$，即加法群 $\mathbb Z$ 的有序乘法副本再添一个零元：其非零元素为 $\exp(n)$（$n\in\mathbb Z$），乘法对应指数相加，$\exp(0)=1$，非零元素的顺序就是指数的顺序，而零元小于所有非零元素。存在元素 $\pi\in F_w$，在下述精确意义下是素元：$\pi\neq0$、$\|\pi\|<1$，且对每个可逆元素 $u\in F_w^{\times}$，都存在整数 $n\in\mathbb Z$ 使 $\|u\|=\|\pi\|^n$。$\pi$ 的选择可以依赖于 $F$ 和 $w$，整数 $n$ 可以依赖于 $u$，可以为负数、零或正数。这里没有断言 $\pi$ 或 $n$ 的唯一性。
