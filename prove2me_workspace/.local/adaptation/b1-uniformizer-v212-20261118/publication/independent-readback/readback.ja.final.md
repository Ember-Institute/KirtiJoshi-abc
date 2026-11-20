# 日本語の読み戻し

本稿は gpt-6.1-sol による独立した英語の読み戻しに基づく日本語訳である。TERM-015 に従い、uniformizer を「素元」と記す。 [原訳](readback.ja.md) · [独立した英語の読み戻し](readback.en.frozen.md) · [TERM-015](../../../../../../docs/三语术语名词关键对照.md#L44) · [Lean の宣言](../../../../../Definitions/Def_AbcAdaptation_Reference_Iut_Concrete_UniformizerSupply.lean#L20)

## `AbcAdaptation.Reference.Iut.norm_le_one_iff_valued`

数体構造を備えた任意の体 $F$、$F$ の任意の有限素点 $w$、および $F_w$ の任意の元 $x$ に対し、$\|x\|\leq1$ であることと $v_w(x)\leq1$ であることは同値である。ここで $F_w$ は、$F$ の整数環の非零素イデアル $\mathfrak p=w.\mathrm{maximalIdeal}$ に付随する離散付値に関する $F$ の完備化であり、$\|\cdot\|:F_w\to\mathbb R$ はこの完備化体のノルム体構造が与えるノルム、$v_w:F_w\to\Gamma_0$ はその乗法的付値である。$\Gamma_0=\operatorname{WithZero}(\operatorname{Multiplicative}\mathbb Z)$ は、加法群 $\mathbb Z$ を順序付き乗法群として表したものに零元を添加したものである。その非零元を $\exp(n)$ と書くと、$\exp(m)\exp(n)=\exp(m+n)$、$\exp(0)=1$ であり、$\exp(m)<\exp(n)$ と $m<n$ は同値である。添加した零元はすべての非零元より小さい。左辺の $1$ は実数であり、右辺の $1$ は $\Gamma_0$ の単位元である。$x$ に関する量化には $x=0$ も含まれる。

## `AbcAdaptation.Reference.Iut.norm_lt_one_iff_valued`

数体構造を備えた任意の体 $F$、$F$ の任意の有限素点 $w$、および $F_w$ の任意の元 $x$ に対し、$\|x\|<1$ であることと $v_w(x)<1$ であることは同値である。ここで $F_w$ は、$F$ の整数環の非零素イデアル $\mathfrak p=w.\mathrm{maximalIdeal}$ に付随する離散付値に関する $F$ の完備化であり、$\|\cdot\|:F_w\to\mathbb R$ はこの完備化体のノルム体構造が与えるノルム、$v_w:F_w\to\Gamma_0$ はその乗法的付値である。$\Gamma_0=\operatorname{WithZero}(\operatorname{Multiplicative}\mathbb Z)$ は、加法群 $\mathbb Z$ を順序付き乗法群として表したものに零元を添加したものである。その非零元を $\exp(n)$ と書くと、$\exp(m)\exp(n)=\exp(m+n)$、$\exp(0)=1$ であり、$\exp(m)<\exp(n)$ と $m<n$ は同値である。添加した零元はすべての非零元より小さい。左辺の $1$ は実数であり、右辺の $1$ は $\Gamma_0$ の単位元である。$x$ に関する量化には $x=0$ も含まれる。

## `AbcAdaptation.Reference.Iut.norm_eq_one_iff_valued`

数体構造を備えた任意の体 $F$、$F$ の任意の有限素点 $w$、および $F_w$ の任意の元 $x$ に対し、$\|x\|=1$ であることと $v_w(x)=1$ であることは同値である。ここで $F_w$ は、$F$ の整数環の非零素イデアル $\mathfrak p=w.\mathrm{maximalIdeal}$ に付随する離散付値に関する $F$ の完備化であり、$\|\cdot\|:F_w\to\mathbb R$ はこの完備化体のノルム体構造が与えるノルム、$v_w:F_w\to\Gamma_0$ はその乗法的付値である。$\Gamma_0=\operatorname{WithZero}(\operatorname{Multiplicative}\mathbb Z)$ は、加法群 $\mathbb Z$ を順序付き乗法群として表したものに零元を添加したものである。その非零元を $\exp(n)$ と書くと、$\exp(m)\exp(n)=\exp(m+n)$、$\exp(0)=1$ であり、$\exp(m)<\exp(n)$ と $m<n$ は同値である。添加した零元はすべての非零元より小さい。左辺の $1$ は実数であり、右辺の $1$ は $\Gamma_0$ の単位元である。$x$ に関する量化には $x=0$ も含まれる。

## `AbcAdaptation.Reference.Iut.isUniformizer_of_valuation_eq`

数体構造を備えた任意の体 $F$、$F$ の任意の有限素点 $w$、および任意の元 $\pi\in F$ に対し、$v_{\mathfrak p}(\pi)=\exp(-1)$ と仮定する。ここで $\mathfrak p=w.\mathrm{maximalIdeal}$ は $F$ の整数環における対応する非零素イデアルであり、$v_{\mathfrak p}:F\to\Gamma_0$ はその乗法的離散付値である。$\Gamma_0=\operatorname{WithZero}(\operatorname{Multiplicative}\mathbb Z)$ は、加法群 $\mathbb Z$ を順序付き乗法群として表したものに零元を添加したものである。$\exp(n)$ は整数 $n$ に対応する非零元を表し、乗法は指数の加法に対応し、$\exp(0)=1$ であり、非零元の順序はその整数指数の順序であり、添加した零元はすべての非零元より小さい。この付値に関する $F$ の完備化を $F_w$、そのノルムを $\|\cdot\|:F_w\to\mathbb R$、標準的な体の埋め込みを $\iota_w:F\to F_w$ とする。このとき $\iota_w(\pi)$ は、次の厳密な意味で素元（uniformizer）である：$\iota_w(\pi)\neq0$、$\|\iota_w(\pi)\|<1$ であり、任意の可逆元 $u\in F_w^{\times}$ に対して、$\|u\|=\|\iota_w(\pi)\|^n$ を満たす整数 $n\in\mathbb Z$ が存在する。整数 $n$ は $u$ に依存してよく、負、零、正のいずれでもよい。$n$ の一意性は主張されていない。$\exp(-1)\neq0$ であるため、仮定は $\pi=0$ を除外する。

## `AbcAdaptation.Reference.Iut.exists_isUniformizer`

数体構造を備えた任意の体 $F$ と $F$ の任意の有限素点 $w$ に対し、$F$ の整数環の非零素イデアル $\mathfrak p=w.\mathrm{maximalIdeal}$ に付随する乗法的離散付値に関する $F$ の完備化を $F_w$ とし、そのノルムを $\|\cdot\|:F_w\to\mathbb R$ とする。付値の値は $\Gamma_0=\operatorname{WithZero}(\operatorname{Multiplicative}\mathbb Z)$ に属する。これは、加法群 $\mathbb Z$ を順序付き乗法群として表したものに零元を添加したものであり、その非零元は $\exp(n)$（$n\in\mathbb Z$）であり、乗法は指数の加法に対応し、$\exp(0)=1$ であり、非零元の順序は指数の順序であり、零元はすべての非零元より小さい。次の厳密な意味で素元（uniformizer）である元 $\pi\in F_w$ が存在する：$\pi\neq0$、$\|\pi\|<1$ であり、任意の可逆元 $u\in F_w^{\times}$ に対して、$\|u\|=\|\pi\|^n$ を満たす整数 $n\in\mathbb Z$ が存在する。$\pi$ の選択は $F$ と $w$ に依存してよく、整数 $n$ は $u$ に依存してよく、負、零、正のいずれでもよい。$\pi$ と $n$ のいずれについても一意性は主張されていない。
