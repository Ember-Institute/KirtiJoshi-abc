# 日本語の読み戻し

## primeUnder

任意の数体 $K$、任意の体 $k$、および指定された体の埋め込み $\iota\colon k\to K$ を取る。その整数環への制限を $\iota_{\mathcal O}\colon\mathcal O_k\to\mathcal O_K$ とする。ここで各整数環は対応する体の $\mathbb Z$ 上整な元からなる。$K$ の任意の有限素点 $w$ に対し、$\mathfrak p_w$ を対応する $\mathcal O_K$ の零でない素イデアルとする。この定義は、縮約 $\iota_{\mathcal O}^{-1}(\mathfrak p_w)$ を $\mathcal O_k$ の零でない素イデアルとして返し、素であることと零でないことの証明を含める。

## placeUnder

任意の数体 $k,K$ と、指定された体の埋め込み $\iota\colon k\to K$ を取る。その整数環への制限を $\iota_{\mathcal O}\colon\mathcal O_k\to\mathcal O_K$ とする。$K$ の任意の有限素点 $w$ とその対応する素イデアル $\mathfrak p_w$ に対し、この定義は縮約 $\iota_{\mathcal O}^{-1}(\mathfrak p_w)$ に対応する $k$ の有限素点を返す。この有限素点の実数値絶対値は、その素イデアルにおける完備化のノルムを標準埋め込みで $k$ に引き戻したものである。

## placeUnder_maximalIdeal

任意の数体 $k,K$ と、指定された体の埋め込み $\iota\colon k\to K$、および $K$ の任意の有限素点 $w$ を取る。$\mathfrak p_w\subset\mathcal O_K$ を $w$ に対応する素イデアルとし、$\iota_{\mathcal O}$ を誘導される整数環の写像とする。$\iota_{\mathcal O}^{-1}(\mathfrak p_w)$ における完備化のノルムを $k$ に引き戻して得られる有限素点を $v_0$ とする。$v_0$ に対応する $\mathcal O_k$ の極大イデアルは $\mathfrak p_w$ の縮約に等しい。
$$
\mathfrak p_{v_0}=\iota_{\mathcal O}^{-1}(\mathfrak p_w).
$$

## liesOver_placeUnder

任意の数体 $k,K$ と、指定された体の埋め込み $\iota\colon k\to K$、および $K$ の任意の有限素点 $w$ を取る。$\mathfrak p_w\subset\mathcal O_K$ を $w$ に対応する素イデアルとし、$\iota_{\mathcal O}$ を誘導される整数環の写像とする。$\iota_{\mathcal O}^{-1}(\mathfrak p_w)$ における完備化のノルムを $k$ に引き戻して得られる有限素点を $v_0$ とする。$w$ は $v_0$ の上にある。すなわち、$v_0$ に対応する $\mathcal O_k$ の素イデアルは $\iota_{\mathcal O}$ による $\mathfrak p_w$ の逆像に等しい。

## placeUnder_eq_of_liesOver_place

任意の数体 $k,K$ と、指定された体の埋め込み $\iota\colon k\to K$、および $K$ の任意の有限素点 $w$ と $k$ の任意の有限素点 $v$ を取る。それぞれに対応する素イデアルを $\mathfrak p_w\subset\mathcal O_K$ と $\mathfrak p_v\subset\mathcal O_k$ とする。誘導される整数環の写像 $\iota_{\mathcal O}$ について $\mathfrak p_v=\iota_{\mathcal O}^{-1}(\mathfrak p_w)$ と仮定する。このとき、$\iota_{\mathcal O}^{-1}(\mathfrak p_w)$ における完備化のノルムを $k$ に引き戻して得られる有限素点は $v$ に等しい。

## relRamIdx

任意の数体 $k,K$ と、指定された体の埋め込み $\iota\colon k\to K$、および $K$ の任意の有限素点 $v$ と $k$ の任意の有限素点 $w$ を取る。それぞれに対応する素イデアルを $\mathfrak p_v\subset\mathcal O_K$ と $\mathfrak p_w\subset\mathcal O_k$ とする。$\mathfrak p_w\mathcal O_K$ は誘導される整数環の写像による $\mathfrak p_w$ の像が生成するイデアルである。この定義は $\mathfrak p_w\mathcal O_K\subseteq\mathfrak p_v^n$ を満たす最大の自然数 $n$ を返し、そのような最大値が存在しなければ $0$ を返す。包含を満たす指数が $0$ だけの場合にも値は $0$ である。

## relInertDeg

任意の数体 $k,K$ と、指定された体の埋め込み $\iota\colon k\to K$、および $K$ の任意の有限素点 $v$ と $k$ の任意の有限素点 $w$ を取る。それぞれに対応する素イデアルを $\mathfrak p_v\subset\mathcal O_K$ と $\mathfrak p_w\subset\mathcal O_k$ とする。誘導される整数環の写像 $\iota_{\mathcal O}\colon\mathcal O_k\to\mathcal O_K$ による $\mathfrak p_v$ の逆像が $\mathfrak p_w$ に等しい場合、この定義は誘導される剰余体の写像について $\mathcal O_K/\mathfrak p_v$ の $\mathcal O_k/\mathfrak p_w$ 上の次元を返す。それ以外の対には $0$ を返す。

## ramificationIdx'_ne_zero

任意の数体 $k,K$ と、指定された体の埋め込み $\iota\colon k\to K$、および $K$ の任意の有限素点 $w$ と $k$ の任意の有限素点 $v$ を取る。それぞれに対応する素イデアルを $\mathfrak p_w\subset\mathcal O_K$ と $\mathfrak p_v\subset\mathcal O_k$ とする。誘導される整数環の写像 $\iota_{\mathcal O}$ について $\mathfrak p_v=\iota_{\mathcal O}^{-1}(\mathfrak p_w)$ と仮定する。$\mathfrak p_v\mathcal O_K$ を $\mathfrak p_v$ の像が生成するイデアルとする。$\mathfrak p_v\mathcal O_K\subseteq\mathfrak p_w^n$ を満たす最大の自然数 $n$ を取り、最大値が存在しない場合には $0$ を取る。仮定の下でこの自然数は零でない。

## valuation_algebraMap_eq_pow

任意の数体 $k,K$ と、指定された体の埋め込み $\iota\colon k\to K$、および $K$ の任意の有限素点 $w$ と $k$ の任意の有限素点 $v$ を取る。それぞれに対応する素イデアルを $\mathfrak p_w\subset\mathcal O_K$ と $\mathfrak p_v\subset\mathcal O_k$ とする。誘導される整数環の写像 $\iota_{\mathcal O}$ について $\mathfrak p_v=\iota_{\mathcal O}^{-1}(\mathfrak p_w)$ と仮定する。$\mathfrak p_v\mathcal O_K$ を $\mathfrak p_v$ の像が生成するイデアルとし、$e$ を $\mathfrak p_v\mathcal O_K\subseteq\mathfrak p_w^n$ を満たす最大の自然数 $n$ とする。最大値が存在しなければ $e=0$ とする。$a\in\{v,w\}$ の素イデアルに対応する乗法的付値を $\nu_a$ と書く。値域は生成元 $t$ の形式的なべき $t^m$（$m\in\mathbb Z$、$t^mt^n=t^{m+n}$）と吸収元 $0$ からなる。零でない元 $z$ の付値は $t^{-\operatorname{ord}_{\mathfrak p_a}(z)}$ であり、$\operatorname{ord}_{\mathfrak p_a}(z)$ は $a$ が属する数体において、$z$ の主分数イデアルにおける $\mathfrak p_a$ の指数である。$\nu_a(0)=0$ とする。$x=0$ を含むすべての $x\in k$ について次の等式が成り立つ。
$$
\nu_w(\iota(x))=\nu_v(x)^e.
$$

## relRamIdx_ne_zero

任意の数体 $k,K$ と、指定された体の埋め込み $\iota\colon k\to K$、および $K$ の任意の有限素点 $v$ と $k$ の任意の有限素点 $w$ を取る。それぞれに対応する素イデアルを $\mathfrak p_v\subset\mathcal O_K$ と $\mathfrak p_w\subset\mathcal O_k$ とする。誘導される整数環の写像 $\iota_{\mathcal O}$ について $\mathfrak p_w=\iota_{\mathcal O}^{-1}(\mathfrak p_v)$ と仮定する。$\mathfrak p_w\mathcal O_K$ を $\mathfrak p_w$ の像が生成するイデアルとする。$e(v/w)$ を $\mathfrak p_w\mathcal O_K\subseteq\mathfrak p_v^n$ を満たす最大の自然数 $n$ とし、最大値が存在しなければ $0$ とする。仮定の下で $e(v/w)\ne 0$ である。
