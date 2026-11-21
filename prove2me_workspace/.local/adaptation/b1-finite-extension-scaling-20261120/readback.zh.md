# 有限扩张中的有限高度缩放

固定数域 $k,K$ 和代数结构 $k\to K$。用 $v$ 表示 $k$ 的有限处，用 $w$ 表示 $K$ 的有限处。记 $\mathfrak p_v$、$\mathfrak p_w$ 为相应的素理想。$w\mid v$ 表示 $\mathfrak p_w\cap\mathcal O_k=\mathfrak p_v$。写 $e_w,f_w$ 和 $e_v,f_v$ 表示相对于各自下方有理素数的分歧指数与剩余次数。$d_K(w)=e_wf_w$、$d_k(v)=e_vf_v$ 是此处采用的局部次数。对 $w\mid v$，写 $e(w/v)$、$f(w/v)$ 表示相对分歧指数与剩余次数。

1. `under_int_eq_under_int`。若 $w\mid v$，则 $\mathfrak p_w\cap\mathbb Z=\mathfrak p_v\cap\mathbb Z$。沿 $\mathbb Z\to\mathcal O_k\to\mathcal O_K$ 的收缩复合给出等式。
2. `residueChar_eq_of_liesOver`。若 $w\mid v$，两处的剩余特征相同。两处下方的同一个整数素理想由各自的剩余特征生成。
3. `ramIdx_eq_mul`。若 $w\mid v$，则 $e_w=e_v\,e(w/v)$。在下方有理素数、$v$ 与 $w$ 构成的塔上使用分歧指数的乘法公式。
4. `inertDeg_eq_mul`。在同一条件下，$f_w=f_v\,f(w/v)$。相应剩余域扩张给出乘法公式。
5. `localDeg_eq_mul`。若 $w\mid v$，则 $d_K(w)=d_k(v)e(w/v)f(w/v)$。
6. `relLocalDeg`。对任意 $w,v$，以相对分歧指数与剩余次数的 Lean 表达式之积定义自然数 $d(w/v)$。定义接受任意一对有限处，在 $w\mid v$ 时给出上述相对局部次数。
7. `relLocalDeg_ne_zero`。若 $w\mid v$，则 $d(w/v)\ne0$。相对分歧指数非零，且剩余次数的塔公式和 $f_w>0$ 保证相对剩余次数非零。
8. `sum_localDeg_liesOver`。若有限集 $S$ 满足 $w\in S\iff w\mid v$，则 $\sum_{w\in S}d_K(w)=[K:k]d_k(v)$。将 $S$ 与 $\mathfrak p_v$ 上方的素理想作双射，并逐项应用局部次数公式。
9. `sum_relLocalDeg_liesOver`。对同一个完整纤维 $S$，$\sum_{w\in S}d(w/v)=[K:k]$。用 $d_k(v)>0$ 消去共同因子。
10. `apply_algebraMap_eq_pow`。若 $w\mid v$，则对所有 $y\in k$，$|y|_w=|y|_v^{d(w/v)}$。左边在代数映射下取像。这里使用项目的有限处绝对值。对非零元，在对数公式中分别换算分歧指数与剩余次数。零元由 $d(w/v)>0$ 处理。
11. `posLog_apply_algebraMap_eq`。在同一条件下，对所有 $y\in k$，$\log^+|y|_w=d(w/v)\log^+|y|_v$。按 Lean 中的定义 $\log^+(a)=\max(\log a,0)$，并采用 $\log 0=0$ 的约定。
12. `finHeight_algebraMap`。对所有 $y\in k$，
    $$h_{\mathrm{fin}}^K(y)=[K:k]\,h_{\mathrm{fin}}^k(y),\qquad
    h_{\mathrm{fin}}^F(y)=\sum_{u\text{ 有限于 }F}\log^+|y|_u.$$
    左边使用 $y$ 在 $K$ 中的像。有限支撑上的下方处映射把求和按纤维分组。下方项正时，相对次数非零保证该组恰含此处上方的所有有限处，再用相对次数和公式。

[来源、目标及命令对应](SOURCE_LEDGER.md)
