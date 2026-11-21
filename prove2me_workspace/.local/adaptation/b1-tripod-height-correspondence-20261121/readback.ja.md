# Legendre 曲線の j 不変量の正規化有限高さ

曲線の供給データ \(P\) と、パラメータ \(\lambda\in\overline{\mathbb Q}\setminus\{0,1\}\) を持つ三脚の点 \(x\) を取る。\(P\) は、すべての代数的パラメータに対する Legendre 曲線の \(3\) 等分点集合と \(5\) 等分点集合の有限性の証明、および各三脚の点における曲線の算術データと各素数 \(\ell\) に対する mod \(\ell\) Galois 表現を与える。点 \(x\) における曲線 \(E_\lambda\) の方程式は \(y^2=X(X-1)(X-\lambda)\) である。その定義体 \(F_\lambda\) は、\(\lambda\)、選んだ \(-1,\lambda,1-\lambda\) の平方根、およびこの曲線の \(3\) 等分点と \(5\) 等分点のアフィン座標を \(\mathbb Q\) に添加して得られる。\(h_P(x)=[F_\lambda:\mathbb Q]^{-1}\sum_w n_w f_w\log p_w\) と書く。和は、\(E_\lambda\) が乗法的還元を持つ \(F_\lambda\) の有限素点 \(w\) 上を動く。\(p_w\) は剰余標数、\(f_w\) は剰余次数である。選んだ Tate パラメータ \(q_w\) は完備化において \(j(E_{q_w})=j(E_\lambda)\) を満たし、その位数 \(n_w\) は選んだ素元 \(\pi_w\) に関して \(\|q_w\|=\|\pi_w\|^{n_w}\) となる。

このようなすべての \(P,x\) に対して \(k=\mathbb Q(\lambda)\) および \(J_\lambda=256(\lambda^2-\lambda+1)^3/(\lambda^2(\lambda-1)^2)\in k\) とおく。定理は次の等式を主張する。
\[
h_P(x)=\frac{\displaystyle\sum_{v\text{ は }k\text{ の有限素点}}^{\mathrm f}\max\{0,\log |J_\lambda|_v\}}{[k:\mathbb Q]}.
\]
絶対値 \(|\cdot|_v\) は \(v\) における完備化のノルムから得られる。ここで実対数は \(\log 0=0\) と定めるため、\(J_\lambda=0\) なら右辺は零である。分母は \(\lambda\) の \(\mathbb Q\) 上の最小多項式の次数であり、正である。乗法的還元を持つ有限素点がなければ、\(h_P(x)\) の定義に現れる和は空和で値は零となる。
