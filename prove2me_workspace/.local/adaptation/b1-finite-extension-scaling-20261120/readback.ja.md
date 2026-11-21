# 数体の拡大における有限高さの換算

数体 $k,K$ と代数準同型 $k\to K$ を固定する。$v$ を $k$ の有限素点、$w$ を $K$ の有限素点とし、対応する素イデアルを $\mathfrak p_v,\mathfrak p_w$ と書く。$w\mid v$ は $\mathfrak p_w\cap\mathcal O_k=\mathfrak p_v$ を表す。下にある有理素数に対する分岐指数と剰余次数を $e_w,f_w$ と $e_v,f_v$ で表し、$d_K(w)=e_wf_w$、$d_k(v)=e_vf_v$ と置く。$w\mid v$ のとき、相対分岐指数と相対剰余次数を $e(w/v),f(w/v)$ と書く。

1. `under_int_eq_under_int`。$w\mid v$ ならば $\mathfrak p_w\cap\mathbb Z=\mathfrak p_v\cap\mathbb Z$ である。$\mathbb Z\to\mathcal O_k\to\mathcal O_K$ に沿って素イデアルを縮約する。
2. `residueChar_eq_of_liesOver`。$w\mid v$ ならば $w$ と $v$ の剰余標数は等しい。各剰余標数は $\mathbb Z$ の同じ素イデアルの生成元である。
3. `ramIdx_eq_mul`。$w\mid v$ ならば、分岐指数の塔の公式から $e_w=e_v\,e(w/v)$ が成り立つ。
4. `inertDeg_eq_mul`。$w\mid v$ ならば、剰余体の拡大次数の塔の公式から $f_w=f_v\,f(w/v)$ が成り立つ。
5. `localDeg_eq_mul`。$w\mid v$ ならば $d_K(w)=d_k(v)e(w/v)f(w/v)$ である。
6. `relLocalDeg`。任意の $w,v$ について、相対分岐指数と相対剰余次数の Lean 式の積として自然数 $d(w/v)$ を定義する。$w\mid v$ ならば上記の相対局所次数を与える。
7. `relLocalDeg_ne_zero`。$w\mid v$ ならば $d(w/v)\ne0$ である。相対分岐指数は零でない。剰余次数の塔の公式と $f_w>0$ により、相対剰余次数も零でない。
8. `sum_localDeg_liesOver`。$w\in S\iff w\mid v$ を満たす有限集合 $S$ に対し、$\sum_{w\in S}d_K(w)=[K:k]d_k(v)$ が成り立つ。各素点を $\mathfrak p_v$ の上にある素イデアルに対応させ、各項に局所次数の公式を使う。
9. `sum_relLocalDeg_liesOver`。同じ全ファイバー $S$ について、$\sum_{w\in S}d(w/v)=[K:k]$ が成り立つ。正の因子 $d_k(v)$ を消去する。
10. `apply_algebraMap_eq_pow`。$w\mid v$ のとき、すべての $y\in k$ に対して $|y|_w=|y|_v^{d(w/v)}$ が成り立つ。左辺では $K$ における像を取る。絶対値はプロジェクトが用いる有限素点の絶対値である。非零の元について対数公式に分岐指数と剰余次数を代入する。零元には $d(w/v)>0$ を用いる。
11. `posLog_apply_algebraMap_eq`。$w\mid v$ のとき、すべての $y\in k$ に対して $\log^+|y|_w=d(w/v)\log^+|y|_v$ が成り立つ。Lean では $\log^+(a)=\max(\log a,0)$ と定め、$\log 0=0$ とする。
12. `finHeight_algebraMap`。すべての $y\in k$ について次が成り立つ。
    $$h_{\mathrm{fin}}^K(y)=[K:k]\,h_{\mathrm{fin}}^k(y),\qquad
    h_{\mathrm{fin}}^F(y)=\sum_{u\text{ は }F\text{ の有限素点}}\log^+|y|_u.$$
    左辺では $K$ での $y$ の像を取る。有限台を下の素点ごとにまとめる。下の素点での項が正ならば、相対局所次数が零でないため、その上にあるすべての素点が和に現れる。そこで相対局所次数の和の公式を適用する。

[出典と対象の宣言](SOURCE_LEDGER.md)
