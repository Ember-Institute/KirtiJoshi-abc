# 形式宣言の読み戻し

## `EllipticCurveData.prime_dvd_ramificationIdx`

$F$ を数体、$\overline F$ を $F$ の選んだ代数閉包、$E$ を $F$ 上のワイエルシュトラス楕円曲線とする。これらは $C$ が与えるデータであり、$F$ と $\overline F$ は同じ宇宙レベルに属する。$M=\mathbb Q(j(E))\subseteq F$ をモジュライ体とする。有限素点 $z$ には整数環の零でない極大イデアル $\mathfrak p_z$ が対応し、その剰余標数は $\mathfrak p_z$ による剰余体の標数である。ある有限素点が別の有限素点の上にあるとは、前者のイデアルの縮約が後者のイデアルに等しいことをいう。

$W$ を、$E$ が乗法的還元を持つ $F$ の有限素点全体の集合とする。ここで乗法的還元を持つとは、$F$ 上のワイエルシュトラス変数変換によって、完備化の付値環上で乗法的還元を持つモデルが得られることをいう。

算術データ $CA:C.\mathrm{CurveArithmetic}$ は次の条件を与える。

- $-1$ は $F$ において平方である。
- $F$ の任意の有限素点において、$E$ は $F$ 上の変数変換の後に良い還元または乗法的還元を持つ。
- $E(\overline F)$ のうち $6$ 倍が単位元となる点は、いずれも $E(F)$ の点から得られる。
- 任意の素数 $r\geq 7$ に対して、$F/M$ はガロア拡大であり、$[F:M]$ と $r$ は互いに素である。
- $F$ の任意の有限素点は $M$ のある有限素点の上にある。この上下関係にある任意の二つの素点の剰余標数は等しい。
- 剰余標数が $2$ と異なる $M$ の任意の有限素点について、その上にある $F$ の素点の一つで $E$ が乗法的還元を持てば、その上にある $F$ のすべての素点で乗法的還元を持つ。
- $W$ は有限集合である。$F$ の各有限素点の下にある有理素数に対する剰余次数は正である。
- 任意の自然数 $r$ に対して、$W$ のうち剰余標数が $r$ である素点の剰余次数の和は $[F:\mathbb Q]$ 以下である。

$w\in W$ ごとに、データ $TI:C.\mathrm{TateInputs}$ は $w$ における完備化 $F_w$ の元 $q_w\in F_w^\times$ で、$\lVert q_w\rVert<1$ を満たすものを与える。$q_w$ のテイト曲線の $j$ 不変量は $j(E)$ の $F_w$ への像に等しい。このデータはまた、$F_w$ の素元 $\pi_w$ を与える。すなわち $\pi_w\ne0$、$\lVert\pi_w\rVert<1$ であり、$F_w^\times$ の各元のノルムは $\lVert\pi_w\rVert$ の整数乗である。$\lVert q_w\rVert=\lVert\pi_w\rVert^{n_w}$ を満たす一意な正の整数を $n_w$ とする。この自然数が `TI.qOrder w hw` である。

$\ell$ を $2$ と異なる素数とする。データ $R:C.\mathrm{ModEllRepData}\,\ell$ は、加法群同型 $b:E(\overline F)[\ell]\simeq\mathbb F_\ell^2$ と群準同型 $\rho:\operatorname{Aut}_F(\overline F)\to\mathrm{GL}_2(\mathbb F_\ell)$ を与える。$\rho$ の核はクルル位相で開部分群である。任意の $\sigma\in\operatorname{Aut}_F(\overline F)$ と $P\in E(\overline F)[\ell]$ について、$b(\sigma P)=\rho(\sigma)b(P)$ が成り立つ。ここで $\sigma$ は点の座標に作用し、単位元を固定する。$K=\overline F^{\ker\rho}$ を $R$ が定める捩れ点体とする。$K$ は数体である。

剰余標数が $2$ および $\ell$ と異なり、$\ell\nmid n_w$ を満たす任意の $w\in W$ を取る。$w$ の上にある $K$ の任意の有限素点 $w'$ に対し、定理は
$$\ell\mid e(w'/w)$$
を主張する。ここで $e(w'/w)$ は、$\mathfrak p_w$ に対する $\mathfrak p_{w'}$ の自然数値の分岐指数である。

## 子の証明義務一　`tateStructureOfTorsion`

$E/F$ を数体 $F$ 上のワイエルシュトラス楕円曲線、$\overline F$ を選んだ代数閉包、$K$ を $\overline F/F$ の中間数体とする。$F$、$\overline F$、$K$ は同じ宇宙レベルに属する。$M=\mathbb Q(j(E))$ とし、$V$ を $M$ の有限素点からなる集合とする。$V$ に属する各素点の剰余標数は $2$ と異なると仮定する。各 $v\in V$ について、その上にある $F$ のすべての有限素点で $E$ は乗法的還元を持つと仮定する。ここでの乗法的還元は、前の宣言と同じく変数変換を許す意味である。

$\ell$ を $2$ と異なる素数とし、$T_K$ を $E(K)$ の加法部分群とする。$T_K\subseteq E(K)[\ell]=\{P:\ell P=0\}$ および $\operatorname{Nat.card}(T_K)\geq\ell^2$ を仮定する。対応するイデアルの意味で、ある $v\in V$ の上にある $K$ の有限素点 $w'$ を取る。このとき、構成は完備化 $K_{w'}$ に底変換した曲線 $E_{K_{w'}}$ 上のテイト構造 $S$ を与える。

$k=K_{w'}$ 上のワイエルシュトラス曲線 $B$ のテイト構造は、次のデータからなる。

- $\lVert q\rVert<1$ を満たすパラメータ $q\in k^\times$。
- $D\cdot B=E_q$ を満たす $k$ 上のワイエルシュトラス変数変換 $D$。ここで $E_q$ は $q$ のテイト・ワイエルシュトラスモデルである。
- 加法記法で表した乗法商群 $k^\times/q^{\mathbb Z}$ から $B(k)$ への加法群同型。
- $q^{\mathbb Z}$ に属さない各 $u\in k^\times$ について、その類に対応する点は変数変換後のモデル $E_q$ においてテイト座標 $X_q(u),Y_q(u)$ を持つ。

## 子の証明義務二　`TateStructure.finite_torsion` と `TateStructure.exists_root_class`

$k$ を、乗法記法で表した $\mathbb Z$ に零を添加した値域を持つ、指定された階数一の付値を備えた体とする。$k$ はこの付値について完備とする。$B$ を $k$ 上のワイエルシュトラス曲線とし、上記のテイト構造 $S$ を与える。$q$ を $S$ のテイトパラメータとする。群 $B(k)$ は非特異なアフィン $k$ 点と無限遠点からなる。零でない自然数 $\ell$ に対し、$B(k)[\ell]=\{P\in B(k):\ell P=0\}$ とおく。第一の主張は $B(k)[\ell]$ が有限群であるというものである。

$\ell^2\leq\operatorname{Nat.card}(B(k)[\ell])$ ならば、第二の主張は $u\in k^\times$ と $m\in\mathbb Z$ が存在し、
$$u^\ell=q^{\,1+\ell m}\quad\text{が }k^\times\text{ において成り立つ}$$
というものである。右辺の指数は整数である。$k^\times$ は $k$ の零でない元全体の乗法群である。

### 参照証明における指定された有限素点での計算

親の定理の仮定のもとで、$E_{K_{w'}}$ 上のテイト構造 $S$ を取り、そのパラメータを $q$ とする。体 $K$ 上の捩れ点から位数の下界 $\ell^2\leq\operatorname{Nat.card}(E(K_{w'})[\ell])$ が得られる。したがって、上記の根の類の計算から $K_{w'}^\times$ における等式 $u^\ell=q^{1+\ell m}$ が得られる。

$\operatorname{ord}_{w'}$ を $K_{w'}^\times$ の正規化された加法付値とする。$q$ のテイト曲線の $j$ 不変量は $j(E)$ の $K_{w'}$ への像に等しい。体の拡大によって $\operatorname{ord}_{w'}(q)=e(w'/w)n_w$ が成り立つ。根の等式の両辺に加法付値を取ると、
$$\ell\,\operatorname{ord}_{w'}(u)=(1+\ell m)e(w'/w)n_w$$
となる。右辺は $\ell$ を法として $e(w'/w)n_w$ に合同であるため、$\ell$ は $e(w'/w)n_w$ を割り切る。$\ell$ は素数であり $\ell\nmid n_w$ であるから、$\ell$ は $e(w'/w)$ を割り切る。
