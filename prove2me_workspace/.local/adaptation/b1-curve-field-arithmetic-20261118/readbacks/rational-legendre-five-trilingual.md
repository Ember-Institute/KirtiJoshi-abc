# The 5-adic valuation and norm for the rational Legendre family

## English

### The curve and the normalization

For a natural number $m$, put $\lambda_m=5^m/(2\cdot 5^m+1)\in\mathbb Q$. The Legendre curve $E_m$ over $\mathbb Q$ has affine equation
$$
y^2=x(x-1)(x-\lambda_m).
$$
The rational bounds $1/3\le\lambda_m<1/2$ give $\lambda_m\ne0,1$. The code constructs the ellipticity instance for every $m$. The function `legendreJ` is the rational expression
$$
J(t)=256\,\frac{(t^2-t+1)^3}{t^2(t-1)^2}.
$$
At $t=\lambda_m$ it equals the elliptic curve invariant $j(E_m)$. [Parameter and ellipticity](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRationalLegendreFive.lean:15) · [Legendre equation](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_LegendreModel.lean:19) · [Definition of the rational expression](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_TripodCanonicalHighHeightInputs.lean:23) · [Identification with the curve invariant](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FieldLegendreFacts.lean:69)

For a nonzero rational $r=a/b$ in lowest terms, $v_5(r)=\operatorname{ord}_5(a)-\operatorname{ord}_5(b)$. For a nonzero integer $a$, $\operatorname{ord}_5(a)$ is the largest exponent $k$ such that $5^k$ divides $a$. This integer-valued valuation has $v_5(5)=1$. The function `padicValRat 5` uses $v_5(0)=0$ by definition. The rational-valued norm `padicNorm 5` is $|r|_5=5^{-v_5(r)}$ for $r\ne0$, with $|0|_5=0$. In particular, $|5|_5=1/5$. [Valuation](/home/admin-wsl/Coq/mathlib4-0df444a/Mathlib/NumberTheory/Padics/PadicVal/Basic.lean:125) · [Norm](/home/admin-wsl/Coq/mathlib4-0df444a/Mathlib/NumberTheory/Padics/PadicNorm.lean:45)

### `padicValRat_j_rationalLegendreFive`

For every natural number $m>0$, the $5$-adic valuation of the curve's $j$-invariant is
$$
v_5\bigl(j(E_m)\bigr)=-2m\qquad\text{in }\mathbb Z.
$$
The statement uses the ellipticity instance constructed from $\lambda_m$. The denominator $2\cdot5^m+1$ has valuation zero, so $v_5(\lambda_m)=m$. The factors $256$, $\lambda_m-1$, and $\lambda_m^2-\lambda_m+1$ each have valuation zero. The squared factor $\lambda_m^2$ in the denominator gives the negative term $-2m$. [Valuation of the curve invariant](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRationalLegendreFive.lean:120) · [Valuation calculation for the rational expression](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRationalLegendreFive.lean:70)

### `padicNorm_legendreJ_rationalLegendreFiveParam`

For every natural number $m>0$, the norm of the rational expression is
$$
\bigl|J(\lambda_m)\bigr|_5=5^{2m}\qquad\text{in }\mathbb Q.
$$
Here $2m$ is a natural-number exponent. The valuation $-2m$ also gives $J(\lambda_m)\ne0$, so the norm uses the nonzero branch of its definition. [Norm of the rational expression](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRationalLegendreFive.lean:109)

## 简体中文

### 曲线与归一化

对自然数 $m$，令 $\lambda_m=5^m/(2\cdot5^m+1)\in\mathbb Q$。有理数域上的 Legendre 曲线 $E_m$ 的仿射方程为
$$
y^2=x(x-1)(x-\lambda_m).
$$
有理数不等式 $1/3\le\lambda_m<1/2$ 给出 $\lambda_m\ne0,1$。代码对每个 $m$ 构造曲线的椭圆性实例。函数 `legendreJ` 是有理式
$$
J(t)=256\,\frac{(t^2-t+1)^3}{t^2(t-1)^2}.
$$
取 $t=\lambda_m$ 时，它等于椭圆曲线的不变量 $j(E_m)$。 [参数与椭圆性](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRationalLegendreFive.lean:15) · [Legendre 方程](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_LegendreModel.lean:19) · [有理式定义](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_TripodCanonicalHighHeightInputs.lean:23) · [与曲线不变量的等式](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FieldLegendreFacts.lean:69)

对既约分数形式的非零有理数 $r=a/b$，$5$ 进赋值为 $v_5(r)=\operatorname{ord}_5(a)-\operatorname{ord}_5(b)$，其中整数的阶是因子 $5$ 的重数。该赋值取整数值，并归一化为 $v_5(5)=1$。函数 `padicValRat 5` 按定义取 $v_5(0)=0$。有理数值的 $5$ 进范数 `padicNorm 5` 在 $r\ne0$ 时为 $|r|_5=5^{-v_5(r)}$，并取 $|0|_5=0$。特别地，$|5|_5=1/5$。 [赋值定义](/home/admin-wsl/Coq/mathlib4-0df444a/Mathlib/NumberTheory/Padics/PadicVal/Basic.lean:125) · [范数定义](/home/admin-wsl/Coq/mathlib4-0df444a/Mathlib/NumberTheory/Padics/PadicNorm.lean:45)

### `padicValRat_j_rationalLegendreFive`

对每个正自然数 $m$，曲线 $j$-不变量的 $5$ 进赋值在整数中满足
$$
v_5\bigl(j(E_m)\bigr)=-2m.
$$
该声明使用由 $\lambda_m$ 构造出的曲线椭圆性实例。$2\cdot5^m+1$ 的赋值为零，所以 $v_5(\lambda_m)=m$。$256$、$\lambda_m-1$ 和 $\lambda_m^2-\lambda_m+1$ 的赋值均为零。分母中的平方因子 $\lambda_m^2$ 给出负项 $-2m$。 [曲线不变量的赋值](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRationalLegendreFive.lean:120) · [有理式的赋值计算](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRationalLegendreFive.lean:70)

### `padicNorm_legendreJ_rationalLegendreFiveParam`

对每个正自然数 $m$，有理式的 $5$ 进范数在有理数中满足
$$
\bigl|J(\lambda_m)\bigr|_5=5^{2m}.
$$
这里 $2m$ 是自然数指数。赋值等于 $-2m$ 还给出 $J(\lambda_m)\ne0$，因而范数按非零情形计算。 [有理式的范数](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRationalLegendreFive.lean:109)

## 日本語

### 曲線と正規化

自然数 $m$ に対し、$\lambda_m=5^m/(2\cdot5^m+1)\in\mathbb Q$ とする。有理数体上の Legendre 曲線 $E_m$ のアフィン方程式は
$$
y^2=x(x-1)(x-\lambda_m)
$$
である。有理数の不等式 $1/3\le\lambda_m<1/2$ から $\lambda_m\ne0,1$ を得る。コードは各 $m$ に対して、この曲線が楕円曲線であることを表すインスタンスを構成する。関数 `legendreJ` は次の有理式である。
$$
J(t)=256\,\frac{(t^2-t+1)^3}{t^2(t-1)^2}.
$$
$t=\lambda_m$ では、楕円曲線の不変量 $j(E_m)$ に等しい。 [パラメータと楕円曲線であること](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRationalLegendreFive.lean:15) · [Legendre 方程式](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_LegendreModel.lean:19) · [有理式の定義](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_TripodCanonicalHighHeightInputs.lean:23) · [曲線の不変量との等式](/home/admin-wsl/Coq/abc/prove2me_workspace/Definitions/Def_AbcAdaptation_Reference_Iut_Tripod_FieldLegendreFacts.lean:69)

非零有理数を既約分数 $r=a/b$ で表すと、$5$ 進付値は $v_5(r)=\operatorname{ord}_5(a)-\operatorname{ord}_5(b)$ である。ここで整数の位数は因子 $5$ の重複度である。この付値は整数値をとり、$v_5(5)=1$ と正規化される。関数 `padicValRat 5` の定義では $v_5(0)=0$ である。有理数値の $5$ 進ノルム `padicNorm 5` は $r\ne0$ なら $|r|_5=5^{-v_5(r)}$ で、$|0|_5=0$ とする。特に $|5|_5=1/5$ である。 [付値の定義](/home/admin-wsl/Coq/mathlib4-0df444a/Mathlib/NumberTheory/Padics/PadicVal/Basic.lean:125) · [ノルムの定義](/home/admin-wsl/Coq/mathlib4-0df444a/Mathlib/NumberTheory/Padics/PadicNorm.lean:45)

### `padicValRat_j_rationalLegendreFive`

任意の正の自然数 $m$ に対して、曲線の $j$-不変量の $5$ 進付値は整数として
$$
v_5\bigl(j(E_m)\bigr)=-2m
$$
を満たす。この宣言は $\lambda_m$ から構成した楕円曲線のインスタンスを用いる。$2\cdot5^m+1$ の付値は零なので、$v_5(\lambda_m)=m$ である。$256$、$\lambda_m-1$、$\lambda_m^2-\lambda_m+1$ の付値はいずれも零である。分母の二乗因子 $\lambda_m^2$ によって負の項 $-2m$ が生じる。 [曲線の不変量の付値](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRationalLegendreFive.lean:120) · [有理式の付値の計算](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRationalLegendreFive.lean:70)

### `padicNorm_legendreJ_rationalLegendreFiveParam`

任意の正の自然数 $m$ に対して、有理式の $5$ 進ノルムは有理数として
$$
\bigl|J(\lambda_m)\bigr|_5=5^{2m}
$$
を満たす。$2m$ は自然数の指数である。付値が $-2m$ であることから $J(\lambda_m)\ne0$ も従うため、ノルムの定義における非零の場合を適用する。 [有理式のノルム](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_TripodRationalLegendreFive.lean:109)
