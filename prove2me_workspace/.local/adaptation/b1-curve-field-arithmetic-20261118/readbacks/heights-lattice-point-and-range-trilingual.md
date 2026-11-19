# Injectivity of the lattice quotient point map and surjectivity of modular $j$

## English

### `latticeQuotientPointMap_injective`

For $\tau$ in the complex upper half-plane $\mathbb H$, let $\Lambda_\tau=\mathbb Z\tau+\mathbb Z$ and let $W_\tau$ be the short Weierstrass curve of this lattice. The map from $\mathbb C/\Lambda_\tau$ to $W_\tau(\mathbb C)$ sends the zero class to the point at infinity. It sends the class of $z\notin\Lambda_\tau$ to the point with coordinates $\bigl(\wp_\tau(z),\wp_\tau'(z)/2\bigr)$, where $\wp_\tau$ is the lattice Weierstrass function. For every $\tau\in\mathbb H$, this map is injective. For complex representatives $z,w$, their images agree exactly when $z-w\in\Lambda_\tau$. [Local map](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceHeightsLatticePointMap.lean:60) · [Local declaration](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceHeightsLatticePointMapInjectivity.lean:48) · [Pinned Heights declaration](https://github.com/lana-agents/heights/blob/721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/LatticePointMapInjectivity.lean#L68)

### `modularJ_surjective`

Let $j(\tau)=E_4(\tau)^3/\Delta_{\mathrm{mod}}(\tau)$, with $\Delta_{\mathrm{mod}}=(E_4^3-E_6^2)/1728$. The map $j\colon\mathbb H\to\mathbb C$ is surjective. For every $a\in\mathbb C$, there exists $\tau\in\mathbb H$ with $j(\tau)=a$. [Local definition](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceHeightsLatticeModular.lean:61) · [Local declaration](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceHeightsModularRange.lean:73) · [Pinned Heights declaration](https://github.com/lana-agents/heights/blob/721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/ModularJ.lean#L355)

## 中文

### `latticeQuotientPointMap_injective`

设 $\tau$ 为复上半平面 $\mathbb H$ 中的一点，令 $\Lambda_\tau=\mathbb Z\tau+\mathbb Z$，并记该周期格对应的短 Weierstrass 曲线为 $W_\tau$。从 $\mathbb C/\Lambda_\tau$ 到 $W_\tau(\mathbb C)$ 的映射将零类送到无穷远点。对 $z\notin\Lambda_\tau$，该映射将 $z$ 的类送到坐标为 $\bigl(\wp_\tau(z),\wp_\tau'(z)/2\bigr)$ 的点，其中 $\wp_\tau$ 是该周期格的 Weierstrass 函数。对每个 $\tau\in\mathbb H$，此映射是单射。对任意复数代表元 $z,w$，两者的像相同当且仅当 $z-w\in\Lambda_\tau$。 [本地映射](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceHeightsLatticePointMap.lean:60) · [本地声明](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceHeightsLatticePointMapInjectivity.lean:48) · [固定版本的 Heights 声明](https://github.com/lana-agents/heights/blob/721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/LatticePointMapInjectivity.lean#L68)

### `modularJ_surjective`

令 $j(\tau)=E_4(\tau)^3/\Delta_{\mathrm{mod}}(\tau)$，其中 $\Delta_{\mathrm{mod}}=(E_4^3-E_6^2)/1728$。映射 $j\colon\mathbb H\to\mathbb C$ 是满射。对每个 $a\in\mathbb C$，存在 $\tau\in\mathbb H$ 使 $j(\tau)=a$。 [本地定义](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceHeightsLatticeModular.lean:61) · [本地声明](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceHeightsModularRange.lean:73) · [固定版本的 Heights 声明](https://github.com/lana-agents/heights/blob/721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/ModularJ.lean#L355)

## 日本語

### `latticeQuotientPointMap_injective`

$\tau$ を複素上半平面 $\mathbb H$ の点とする。$\Lambda_\tau=\mathbb Z\tau+\mathbb Z$ とおき、この周期格子の短 Weierstrass 曲線を $W_\tau$ とする。$\mathbb C/\Lambda_\tau$ から $W_\tau(\mathbb C)$ への写像は零剰余類を無限遠点に送る。$z\notin\Lambda_\tau$ の剰余類は、座標が $\bigl(\wp_\tau(z),\wp_\tau'(z)/2\bigr)$ の点に移る。ここで $\wp_\tau$ はこの周期格子の Weierstrass 関数である。任意の $\tau\in\mathbb H$ に対し、この写像は単射である。代表元 $z,w\in\mathbb C$ の像が等しいための必要十分条件は $z-w\in\Lambda_\tau$ である。 [ローカルの写像](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceHeightsLatticePointMap.lean:60) · [ローカルの宣言](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceHeightsLatticePointMapInjectivity.lean:48) · [固定リビジョンの Heights の宣言](https://github.com/lana-agents/heights/blob/721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/LatticePointMapInjectivity.lean#L68)

### `modularJ_surjective`

$j(\tau)=E_4(\tau)^3/\Delta_{\mathrm{mod}}(\tau)$ とおく。ここで $\Delta_{\mathrm{mod}}=(E_4^3-E_6^2)/1728$ である。写像 $j\colon\mathbb H\to\mathbb C$ は全射である。任意の $a\in\mathbb C$ に対し、$j(\tau)=a$ を満たす $\tau\in\mathbb H$ が存在する。 [ローカルの定義](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceHeightsLatticeModular.lean:61) · [ローカルの宣言](/home/admin-wsl/Coq/abc/prove2me_workspace/Solutions/Source_ReferenceHeightsModularRange.lean:73) · [固定リビジョンの Heights の宣言](https://github.com/lana-agents/heights/blob/721496ca4c158e511d25d8ccf6bfe8503eda73c1/Heights/ModularJ.lean#L355)
