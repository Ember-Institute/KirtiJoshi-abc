# 中文读回

## primeUnder

任取数域 $K$、域 $k$ 和给定的域嵌入 $\iota\colon k\to K$，记 $\iota_{\mathcal O}\colon\mathcal O_k\to\mathcal O_K$ 为它在整数环上的限制，这里的整数环由相应域中在 $\mathbb Z$ 上整的元素组成。对 $K$ 的任意有限处 $w$，记 $\mathfrak p_w$ 为它对应的 $\mathcal O_K$ 中的非零素理想。此定义返回收缩理想 $\iota_{\mathcal O}^{-1}(\mathfrak p_w)$，并给出它是 $\mathcal O_k$ 中非零素理想的证明。

## placeUnder

任取数域 $k,K$ 和给定的域嵌入 $\iota\colon k\to K$，记 $\iota_{\mathcal O}\colon\mathcal O_k\to\mathcal O_K$ 为它在整数环上的限制。对 $K$ 的任意有限处 $w$，设 $\mathfrak p_w$ 为其对应的素理想。此定义返回 $k$ 上与收缩理想 $\iota_{\mathcal O}^{-1}(\mathfrak p_w)$ 对应的有限处。该有限处的实值绝对值由 $k$ 在此素理想处的完备化范数沿典范嵌入拉回 $k$ 得到。

## placeUnder_maximalIdeal

任取数域 $k,K$、给定的域嵌入 $\iota\colon k\to K$，以及 $K$ 的任意有限处 $w$，其对应的素理想为 $\mathfrak p_w\subset\mathcal O_K$。用 $\iota_{\mathcal O}$ 表示诱导的整数环映射。令 $v_0$ 为将 $\iota_{\mathcal O}^{-1}(\mathfrak p_w)$ 处的完备化范数拉回 $k$ 所得的有限处。$v_0$ 对应的 $\mathcal O_k$ 中的极大理想等于 $\mathfrak p_w$ 的收缩。
$$
\mathfrak p_{v_0}=\iota_{\mathcal O}^{-1}(\mathfrak p_w).
$$

## liesOver_placeUnder

任取数域 $k,K$、给定的域嵌入 $\iota\colon k\to K$，以及 $K$ 的任意有限处 $w$，其对应的素理想为 $\mathfrak p_w\subset\mathcal O_K$。用 $\iota_{\mathcal O}$ 表示诱导的整数环映射。令 $v_0$ 为将 $\iota_{\mathcal O}^{-1}(\mathfrak p_w)$ 处的完备化范数拉回 $k$ 所得的有限处。则 $w$ 位于 $v_0$ 上方，即 $v_0$ 对应的 $\mathcal O_k$ 中的素理想等于 $\mathfrak p_w$ 在 $\iota_{\mathcal O}$ 下的原像。

## placeUnder_eq_of_liesOver_place

任取数域 $k,K$ 和给定的域嵌入 $\iota\colon k\to K$，以及 $K$ 的任意有限处 $w$ 和 $k$ 的任意有限处 $v$。其对应的素理想分别是 $\mathfrak p_w\subset\mathcal O_K$ 和 $\mathfrak p_v\subset\mathcal O_k$。假定 $\mathfrak p_v=\iota_{\mathcal O}^{-1}(\mathfrak p_w)$，其中 $\iota_{\mathcal O}$ 为诱导的整数环映射。则将 $\iota_{\mathcal O}^{-1}(\mathfrak p_w)$ 处的完备化范数拉回 $k$ 所得的有限处等于 $v$。

## relRamIdx

任取数域 $k,K$ 和给定的域嵌入 $\iota\colon k\to K$，以及 $K$ 的任意有限处 $v$ 和 $k$ 的任意有限处 $w$。其对应的素理想分别是 $\mathfrak p_v\subset\mathcal O_K$ 和 $\mathfrak p_w\subset\mathcal O_k$。记 $\mathfrak p_w\mathcal O_K$ 为 $\mathfrak p_w$ 在诱导的整数环映射下的像所生成的理想。此定义返回使 $\mathfrak p_w\mathcal O_K\subseteq\mathfrak p_v^n$ 成立的最大自然数 $n$。若这样的 $n$ 没有最大值，定义取 $0$。若 $0$ 是唯一使包含关系成立的指数，定义也取 $0$。

## relInertDeg

任取数域 $k,K$ 和给定的域嵌入 $\iota\colon k\to K$，以及 $K$ 的任意有限处 $v$ 和 $k$ 的任意有限处 $w$。其对应的素理想分别是 $\mathfrak p_v\subset\mathcal O_K$ 和 $\mathfrak p_w\subset\mathcal O_k$。若 $\mathfrak p_v$ 在诱导的整数环映射 $\iota_{\mathcal O}\colon\mathcal O_k\to\mathcal O_K$ 下的原像等于 $\mathfrak p_w$，则此定义返回在诱导的剩余域映射下 $\mathcal O_K/\mathfrak p_v$ 在 $\mathcal O_k/\mathfrak p_w$ 上的维数。对其余各对有限处，定义取 $0$。

## ramificationIdx'_ne_zero

任取数域 $k,K$ 和给定的域嵌入 $\iota\colon k\to K$，以及 $K$ 的任意有限处 $w$ 和 $k$ 的任意有限处 $v$。其对应的素理想分别是 $\mathfrak p_w\subset\mathcal O_K$ 和 $\mathfrak p_v\subset\mathcal O_k$。假定 $\mathfrak p_v=\iota_{\mathcal O}^{-1}(\mathfrak p_w)$，其中 $\iota_{\mathcal O}$ 为诱导的整数环映射。记 $\mathfrak p_v\mathcal O_K$ 为 $\mathfrak p_v$ 的像所生成的理想。取使 $\mathfrak p_v\mathcal O_K\subseteq\mathfrak p_w^n$ 成立的最大自然数 $n$，在没有最大值时取 $0$。在所给假定下，这个自然数非零。

## valuation_algebraMap_eq_pow

任取数域 $k,K$ 和给定的域嵌入 $\iota\colon k\to K$，以及 $K$ 的任意有限处 $w$ 和 $k$ 的任意有限处 $v$。其对应的素理想分别是 $\mathfrak p_w\subset\mathcal O_K$ 和 $\mathfrak p_v\subset\mathcal O_k$。假定 $\mathfrak p_v=\iota_{\mathcal O}^{-1}(\mathfrak p_w)$，其中 $\iota_{\mathcal O}$ 为诱导的整数环映射。记 $\mathfrak p_v\mathcal O_K$ 为 $\mathfrak p_v$ 的像所生成的理想，令 $e$ 为使 $\mathfrak p_v\mathcal O_K\subseteq\mathfrak p_w^n$ 成立的最大自然数 $n$，在没有最大值时取 $e=0$。对 $a\in\{v,w\}$，记 $\nu_a$ 为其素理想对应的乘法赋值。值域由生成元 $t$ 的形式幂 $t^m$（$m\in\mathbb Z$，$t^mt^n=t^{m+n}$）和一个吸收元 $0$ 组成。非零元素 $z$ 的赋值为 $t^{-\operatorname{ord}_{\mathfrak p_a}(z)}$，其中 $\operatorname{ord}_{\mathfrak p_a}(z)$ 为 $a$ 所属数域中 $z$ 的主分式理想里的 $\mathfrak p_a$ 指数。$\nu_a(0)=0$。对任意 $x\in k$，包括 $x=0$，有
$$
\nu_w(\iota(x))=\nu_v(x)^e.
$$

## relRamIdx_ne_zero

任取数域 $k,K$ 和给定的域嵌入 $\iota\colon k\to K$，以及 $K$ 的任意有限处 $v$ 和 $k$ 的任意有限处 $w$。其对应的素理想分别是 $\mathfrak p_v\subset\mathcal O_K$ 和 $\mathfrak p_w\subset\mathcal O_k$。假定 $\mathfrak p_w=\iota_{\mathcal O}^{-1}(\mathfrak p_v)$，其中 $\iota_{\mathcal O}$ 为诱导的整数环映射。记 $\mathfrak p_w\mathcal O_K$ 为 $\mathfrak p_w$ 的像所生成的理想。将 $e(v/w)$ 定义为使 $\mathfrak p_w\mathcal O_K\subseteq\mathfrak p_v^n$ 成立的最大自然数 $n$，在没有最大值时取 $0$。在所给假定下，$e(v/w)\ne 0$。
