# Legendre 曲线 j 不变量的归一化有限高度

给定曲线供应数据 \(P\) 和三足点 \(x\)，其参数为 \(\lambda\in\overline{\mathbb Q}\setminus\{0,1\}\)。\(P\) 给出每个代数参数的 Legendre 曲线 \(3\) 阶、\(5\) 阶挠点集的有限性证明，以及每个三足点的曲线算术数据和每个素数 \(\ell\) 对应的模 \(\ell\) 伽罗瓦表示。在 \(x\) 处的曲线 \(E_\lambda\) 由 \(y^2=X(X-1)(X-\lambda)\) 给出。它的定义域 \(F_\lambda\) 由 \(\lambda\)、选定的 \(-1,\lambda,1-\lambda\) 的平方根以及曲线 \(3\) 阶、\(5\) 阶挠点的仿射坐标在 \(\mathbb Q\) 上生成。记 \(h_P(x)=[F_\lambda:\mathbb Q]^{-1}\sum_w n_w f_w\log p_w\)，其中 \(w\) 遍历 \(F_\lambda\) 中 \(E_\lambda\) 具有乘法约化的有限处。\(p_w\) 与 \(f_w\) 分别是剩余特征和剩余次数。所选的 Tate 参数 \(q_w\) 在该处完备化中满足 \(j(E_{q_w})=j(E_\lambda)\)。其阶数 \(n_w\) 以所选素元 \(\pi_w\) 归一化，满足 \(\|q_w\|=\|\pi_w\|^{n_w}\)。

对每一组这样的 \(P,x\)，令 \(k=\mathbb Q(\lambda)\) 及 \(J_\lambda=256(\lambda^2-\lambda+1)^3/(\lambda^2(\lambda-1)^2)\in k\)。定理断言
\[
h_P(x)=\frac{\displaystyle\sum_{v\text{ 为 }k\text{ 的有限处}}^{\mathrm f}\max\{0,\log|J_\lambda|_v\}}{[k:\mathbb Q]}.
\]
绝对值 \(|\cdot|_v\) 来自 \(v\) 处完备化的范数。这里实对数取 \(\log 0=0\)，因此 \(J_\lambda=0\) 时右端为零。分母是 \(\lambda\) 在 \(\mathbb Q\) 上的最小多项式的次数，是正整数。若 \(E_\lambda\) 没有乘法约化的有限处，则 \(h_P(x)\) 的定义使用空和，值为零。
